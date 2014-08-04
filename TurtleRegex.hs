module TurtleRegex where

import Data.List
import Data.Maybe
import Data.Char (chr)
import Data.Function (on)
import Control.Applicative ((<*), (<$>), (*>), (<$))
import Control.Monad
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.String (Parser)

data Literal = OneOf String
             | Epsion
             deriving (Show, Eq, Ord)

litAnyChar = '\t': map chr [32 .. 126]
litAnyDigit = "0123456789"
litAnySpace = "\t "

data Expr = Lit Literal
          | Alter [Expr]
          | Concat [Expr]
          | Repeat (Int, Maybe Int) Expr
          deriving Show

charSpec :: Parser String
charSpec = (char '.' *> return litAnyChar)
       <|> do char '\\'
              c <- anyChar
              return . fromMaybe [c] $ lookup c escLst
       <|> do c <- oneOf (litAnyChar \\ "]")
              return [c]
    where escLst =  [('t', "\t"), ('d', litAnyDigit), ('s', litAnySpace)]

singleOrRange :: Parser String
singleOrRange = do
        c0 <- charSpec
        ((do char '-'
             c1 <- charSpec
             case (c0, c1) of
                 ([c0'], [c1']) -> return (enumFromTo c0' c1')
                 _ -> error "range")
         <|> return c0)

literal :: Parser Literal
literal = between (char '(') (char ')')
             (char '^' *> (OneOf . (litAnyChar \\) . concat <$> many1 singleOrRange)
                      <|> (OneOf . concat <$> many1 singleOrRange))
      <|> OneOf <$> charSpec

integer :: Parser Int
integer = read <$> many1 digit

range :: Parser (Int, Maybe Int)
range = do char '{'
           (do char ','; b <- integer; char '}'; return (0, Just b)) <|>
            (do a <- integer
                char ','
                (do b <- integer; char '}'; return (a, Just b)) <|>
                 (do char '}'; return (a, Nothing))) -- NOTE: Nothing for INF

expr :: Parser Expr
expr = buildExpressionParser ops atom where
    ops = [
           [ Postfix (Repeat (0, Nothing) <$ char '*')
           , Postfix (Repeat (1, Nothing) <$ char '+')
           , Postfix (Repeat (0, Just 1) <$ char '?')
           , Postfix (do r <- range; return $ Repeat r)]
          ,[Infix (return sequence) AssocRight]
          ,[Infix (choice <$ char '|') AssocRight]
          ]
    atom = msum [Lit <$> literal, between (char '(') (char ')') expr]
    sequence a b = Concat $ seqTerms a ++ seqTerms b
    choice a b = Alter $ choiceTerms a ++ choiceTerms b
    seqTerms (Concat ts) = ts
    seqTerms t = [t]
    choiceTerms (Alter ts) = ts
    choiceTerms t = [t]

parseReg :: String -> Expr
parseReg s = case parse (expr <* eof) "regex" s of
                 Right e -> e
                 Left err -> error (show err)

---------------------------------------------------------------------------------

data Nfa = Nfa { maxId :: Int , startNfa :: Int , finalNfa :: Int
               , tranNfa :: [(Int, (Literal, Int))] }
        deriving Show

reg2nfa :: Expr -> Nfa
reg2nfa e = let nfa = tranReg e (1, 0)
            in  nfa { tranNfa = renameTran $ tranNfa nfa }

-- NOTE: (st :: Int, ed :: Int) means (next start id, final id)
tranReg :: Expr -> (Int, Int) -> Nfa
tranReg (Lit lit) (st, ed) = Nfa st st ed [(st, (lit, ed))]

tranReg (Alter es) (st, ed) =
        let travel e (nfas, st, ed) = let nfa = tranReg e (st, ed)
                                      in  (nfa: nfas, 1 + maxId nfa, ed) -- same ed
            (nfas, newSt, _) = foldr travel ([], st, ed) es -- new st
            newEdges = [(newSt, (Epsion, startNfa nfa)) | nfa <- nfas]
        in  Nfa newSt newSt ed (newEdges ++ concatMap tranNfa nfas)

tranReg (Concat [e]) (st, ed) = tranReg e (st, ed)
tranReg (Concat es) (st, ed) =
        let travel e (nfas, st, ed) = let nfa = tranReg e (st, ed)
                                      in  (nfa: nfas, 1 + maxId nfa, startNfa nfa)
            (nfas, maxid_1, _) = foldr travel ([], st, ed) es -- chain
        in  Nfa (maxid_1 - 1) (startNfa . head $ nfas) ed (concatMap tranNfa nfas)

tranReg (Repeat (0, Nothing) e) (st, ed) =
        let newSt = st
            nfa = tranReg e (st + 1, newSt)
            moreEdges = [(newSt, (Epsion, ed)), (newSt, (Epsion, startNfa nfa))]
        in  Nfa (maxId nfa) newSt ed (tranNfa nfa ++ moreEdges)

tranReg (Repeat (1, Nothing) e) (st, ed) =
        let ed' = st
            nfa = tranReg e (st + 1, ed')
            moreEdges = [(ed', (Epsion, startNfa nfa)), (ed', (Epsion, ed))]
        in  Nfa (maxId nfa) (startNfa nfa) ed (tranNfa nfa ++ moreEdges)

tranReg (Repeat (0, Just 1) e) (st, ed) =
        let nfa = tranReg e (st, ed)
            newSt = maxId nfa + 1
            moreEdges = [(newSt, (Epsion, ed)), (newSt, (Epsion, startNfa nfa))]
        in  Nfa newSt newSt ed (tranNfa nfa ++ moreEdges)

tranReg (Repeat (a, b) e) (st, ed) =
        let es = case (a, b) of
                     (a, Nothing) -> replicate a e ++ [Repeat (0, Nothing) e]
                     (a, Just b) -> replicate a e ++
                                    replicate (b-a) (Repeat (0, Just 1) e)
        in  tranReg (Concat es) (st, ed)

-- split char ranges to not be overloapped with each other
swapSplit :: [String] -> M.Map String [String]
swapSplit segs = M.fromList [(seg, swapSplit' seg) | seg <- segs]
    where sts = nub $ map head segs
          eds = nub $ map last segs
          swapSplit' seg = filter (not . null) . reverse . map reverse
                         $ foldl swapSplit'' [[]] seg
          swapSplit'' res@(x:xs) c
            | c `elem` sts && c `elem` eds = []:[c]:res
            | c `elem` sts = [c]:res
            | c `elem` eds = []:(c:x):xs
            | otherwise = (c:x):xs

-- split all rules
renameTran :: [(Int, (Literal, Int))] -> [(Int, (Literal, Int))]
renameTran tran = concatMap renameOne tran
    where m = swapSplit . nub $ [cs | (_, (OneOf cs, _)) <- tran]
          more Epsion = [Epsion]
          more (OneOf cs) = map OneOf $ m M.! cs
          renameOne (a, (b, c)) = [(a, (b', c)) | b' <- more b]

{-----------------------------------------------------------------------------------}

data DfaBig = DfaBig IS.IntSet   -- start status
                     [IS.IntSet] -- accepted statuses
                     [IS.IntSet] -- all statuses
                     (M.Map IS.IntSet [(Literal, IS.IntSet)])
            deriving Show

-- all reachable status following epsion
reach :: Nfa -> Int -> IS.IntSet
reach nfa s = IS.fromList . snd $ dfs s (IS.empty, [])
        where dfs s (saw, ans) =
                let saw' = IS.insert s saw
                    ans' = s: ans
                    test (a, (b, c)) = if a == s && b == Epsion then Just c
                                                                else Nothing
                    ts = mapMaybe test . tranNfa $ nfa -- reachable t's from s
                in  if IS.member s saw
                        then (saw, ans)
                        else foldr dfs (saw', ans') ts

nfa2dfa :: Nfa -> DfaBig
nfa2dfa nfa = let startSt = reach' $ startNfa nfa -- closure of start status
                  (saw, edges) = construct startSt (S.empty, []) -- dfs
                  allSts = S.toList saw
                  acceptedSts = filter (IS.member (finalNfa nfa)) allSts
                  -- grouping and mapping edges
                  m = groupBy ((==) `on` fst) . sortBy (compare `on` fst) $ edges
                  m' = M.fromList [(fst . head $ g, map snd g) | g <- m]

              in  DfaBig startSt acceptedSts allSts m'

    where -- cached closure of all status
          reach_map = M.fromList [(i, reach nfa i) | i <- [0 .. maxId nfa]]
          reach' x = reach_map M.! x -- helper function
          extends xs = IS.unions [reach' x | x <- xs] -- unioned closure
          -- dfs to construct all dfa's status and edges
          construct s (saw, edges) =
            if S.member s saw
                then (saw, edges)
                else let -- all outer edges
                         es = [ (b, c) | (a, (b, c)) <- tranNfa nfa
                                       , IS.member a s ]
                         -- grouping by b
                         gs = groupBy ((==) `on` fst) .
                              sortBy (compare `on` fst) $ es
                         -- (b, t: all reachable status following b)
                         tr = [ (b , extends . map snd $ g)
                              | g <- gs, let b = fst . head $ g, b /= Epsion]
                         saw' = S.insert s saw
                         -- edges: s--b->t
                         edges' = edges ++ [(s, (b, t)) | (b, t) <- tr]
                     in  foldr construct (saw', edges') (map snd tr)

---------------------------------------------------------------------------------

data Dfa = Dfa Int -- startSt
               Int -- deadSt
               [Int] -- acceptedSts
               (IM.IntMap [(Literal, Int)]) -- transition
            deriving Show

dead = IS.empty -- dead status, self circled

minimize :: DfaBig -> Dfa
minimize (DfaBig stSt acSts allSts tran) =
        let -- two subsets: accepted, not
            subsets = [ S.fromList acSts,
                        S.difference (S.fromList (dead : allSts))
                                     (S.fromList  acSts)]
            -- all minimize (maximize ?) subsets by hopcroft algorithm
            status_sets = hopcroft tran subsets
            -- new id mapping: status of each subsets -> Int
            newid = M.fromList [ (status, i)
                               | (i, subset) <- zip [0..] status_sets
                               , status <- S.toList subset]
            -- new ids in transition
            tran' = [ (newid M.! a, m') | (a, m) <- M.toList tran
                    , let m' = [ (b, newid M.! c) | (b, c) <- m] ]
            tran'' = IM.fromList tran'
        in  Dfa (newid M.! stSt)
                (newid M.! dead)
                (nub (map (newid M.!) acSts))
                tran''

-- hopcroft :: transition -> subsets -> new subsets
hopcroft tran subsets =
        let subsets' = concatMap (splitOne tran) subsets
        in  if length subsets == length subsets' -- stable ?
                then subsets'
                else hopcroft tran subsets'

-- splitOne :: transition -> subset -> new subsets
splitOne tran subset =
  if S.size subset == 1 -- cannot split
      then [subset]
      else let -- all outer edges
               bs = nub . concat $ [ map fst m | a <- S.toList subset
                                   , let m = M.findWithDefault [] a tran]
              -- whether can split by edge b
               sp b = let self_as = -- a's that back to self subsets
                            S.fromList [a | a <- S.toList subset
                                       , let m = M.findWithDefault [] a tran
                                       , let c = fromMaybe dead (lookup b m)
                                       , S.member c subset]
                      in  if S.size self_as `elem` [0, S.size subset]
                              then Nothing
                              else Just [self_as, S.difference subset self_as]
            in fromMaybe [subset] (msum (map sp bs))

---------------------------------------------------------------------------------

matchLit :: Char -> Literal -> Bool
matchLit c (OneOf cs) = c `elem` cs
matchLit _ Epsion = error "Epsion edges in Dfa are not allowed."

match :: Dfa -> String -> Either String String
match (Dfa stSt deadSt acSts tran) s = match' stSt s ""
    where match' st buf cur
            | st `elem` acSts && null buf = Right . reverse $ cur
            | st == deadSt || null buf = Left . reverse $ cur
            | otherwise = let (c:buf') = buf
                              m = IM.findWithDefault [] st tran
                              nxts = [ nxt | (l, nxt) <- m, matchLit c l ]
                          in  if null nxts then match' deadSt      buf' cur
                                           else match' (head nxts) buf' (c:cur)

compile :: String -> Dfa
compile = minimize . nfa2dfa . reg2nfa . parseReg
