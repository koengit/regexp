{-# LANGUAGE FlexibleInstances #-}
module RegExp where

import Control.Monad( liftM, liftM2 )
import Test.QuickCheck hiding ((.&.))

infix  5 ~~
infixl 7 .+.
infixl 8 .>.

--------------------------------------------------------------------------------
-- regular expressions with intersection

data R a
  = Nil
  | Eps
  | Atom a
  | R a :+: R a
  | R a :&: R a
  | R a :>: R a
  | Star (R a)
  | X -- hack to get holes
 deriving (Eq, Ord, Show)

(.+.),(.&.),(.>.) :: R a -> R a -> R a
Nil .+. q   = q
p   .+. Nil = p
p   .+. q   = p :+: q

Nil .&. q   = Nil
p   .&. Nil = Nil
p   .&. q   = p :&: q

Nil .>. q   = Nil
p   .>. Nil = Nil
Eps .>. q   = q
p   .>. Eps = p
p   .>. q   = p :>: q

--------------------------------------------------------------------------------
-- can the RE parse the empty string?

eps :: R a -> Bool
eps Eps       = True
eps (p :+: q) = eps p || eps q
eps (p :&: q) = eps p && eps q
eps (p :>: q) = eps p && eps q
eps (Star _)  = True
eps _         = False

epsR :: R a  -> R a
epsR p | eps p     = Eps
       | otherwise = Nil

--------------------------------------------------------------------------------
-- small step operational semantics, Brzozowsky-style

step :: Eq a => R a -> a -> R a
step (Atom a)  x | a == x    = Eps
                 | otherwise = Nil
step (p :+: q) x = step p x .+. step q x
step (p :&: q) x = step p x .&. step q x
step (p :>: q) x = (step p x .>. q) .+. if eps p then step q x else Nil
step (Star p)  x = step p x .>. Star p
step _         x = Nil

rec :: Eq a => R a -> [a] -> Bool
rec p []     = eps p
rec p (x:xs) = rec (step p x) xs

--------------------------------------------------------------------------------
-- properties, complete?

prop_Nil s =
  rec Nil s == False

prop_Eps s =
  rec Eps s == null s

prop_Atom a s =
  rec (Atom a) s == (s == [a])

prop_Plus p q s =
  rec (p :+: q) s == (rec p s || rec q s)

prop_And p q s =
  rec (p :&: q) s == undefined

prop_Seq p q s =
  rec (p :>: q) s == undefined -- hard one

prop_Star p s =
  rec (Star p) s == rec ((p :>: Star p) :+: Eps) s

--------------------------------------------------------------------------------
-- properties, all falsifiable

prop_SeqComm p q =
  p .>. q ~~ q .>. p

prop_StarPlus p q =
  Star (p .+. q) ~~ Star p .+. Star q

prop_StarSeq p q =
  Star (p .>. q) ~~ Star p .>. Star q

prop_SomeAnd p q =
  some p .&. some q ~~ some (p .&. q)
 where
  some p = p .>. (p .+. Eps)

-- ~~

{-
(~~) :: R L -> R L -> [L] -> Property
p ~~ q = \s -> rec p s === rec q s
-}

(~~) :: R L -> R L -> [L] -> Bool
(~~) p q [] = True
(~~) p q (x:xs)
  | eps p /= eps q               = False
  | size p > 100 || size q > 100 = True
  | otherwise                    = (step p x ~~ step q x) xs

-- the size is there to avoid explosion when evaluating
size :: R L -> Int
size (p :+: q) = 1 + size p + size q
size (p :>: q) = 1 + size p + size q
size (p :&: q) = 1 + size p + size q
size (Star p)  = 1 + size p
size _         = 1

--------------------------------------------------------------------------------
-- arbitrary

data L = A | B | C deriving ( Eq, Ord, Show, Read, Enum )

instance Arbitrary L where
  arbitrary = elements [A ..]

instance Arbitrary (R L) where
  arbitrary = sized (\n -> arb n pats X)
    {-
    sized go
    where
      go s = frequency
        [(1,return Nil)
        ,(1,return Eps)
        ,(3,Atom `fmap` arbitrary)
        ,(s,liftM2 (:+:) (go s2) (go s2))
        ,(s,liftM2 (:&:) (go s2) (go s2))
        ,(s,liftM2 (:>:) (go s2) (go s2))
        ,(s,liftM  Star  (go s1))
        ]
        where
         s2 = s`div`2
         s1 = pred s
    -}

  shrink Eps       = [Nil]
  shrink (Atom a)  = [ Atom a' | a' <- shrink a ]
  shrink (p :+: q) = [ p, q ]
                  ++ [ p' :+: q | p' <- shrink p ]
                  ++ [ p :+: q' | q' <- shrink q ]
  shrink (p :&: q) = [ p, q ]
                  ++ [ p' :&: q | p' <- shrink p ]
                  ++ [ p :&: q' | q' <- shrink q ]
  shrink (p :>: q) = [ p, q ]
                  ++ [ p' :>: q | p' <- shrink p ]
                  ++ [ p :>: q' | q' <- shrink q ]
  shrink (Star p)  = [ Eps, p ]
                  ++ [ Star p' | p' <- shrink p ]
  shrink _         = []

--------------------------------------------------------------------------------

arb :: Eq a => Int -> [R a] -> R a -> Gen (R a)
arb n pats pat =
  do pat' <- elements [ p =:= pat
                      | p <- pats
                      , n > 0 || closed p
                      , p =?= pat
                      ]
     step n pats pat'
 where
  n1 = n-1
  n2 = n `div` 2
 
  step n pats (p :+: q) = liftM2 (:+:) (arb n2 pats p) (arb n2 pats q)
  step n pats (p :>: q) = liftM2 (:>:) (arb n2 pats p) (arb n2 pats q)
  step n pats (p :&: q) = liftM2 (:&:) (arb n2 pats p) (arb n2 pats q)
  step n pats (Star p)  = liftM  Star  (arb n1 pats p)
  step n pats p         = return p
 
  closed (p :+: q) = closed p && closed q
  closed (p :&: q) = closed p && closed q
  closed (p :>: q) = closed p && closed q
  closed (Star p)  = closed p
  closed X         = False
  closed _         = True

  X         =?= _         = True
  _         =?= X         = True
  (p :+: q) =?= (v :+: w) = (p =?= v) && (q =?= w)
  (p :>: q) =?= (v :>: w) = (p =?= v) && (q =?= w)
  (p :&: q) =?= (v :&: w) = (p =?= v) && (q =?= w)
  Star p    =?= Star v    = p =?= v
  p         =?= q         = p == q

  X         =:= v         = v
  p         =:= X         = p
  (p :+: q) =:= (v :+: w) = (p =:= v) :+: (q =:= w)
  (p :>: q) =:= (v :>: w) = (p =:= v) :>: (q =:= w)
  (p :&: q) =:= (v :&: w) = (p =:= v) :&: (q =:= w)
  Star p    =:= Star v    = Star (p =:= v)
  p         =:= _         = p -- should be equal

pats :: [R L]
pats = [ X :+: X
       , X :>: X
       , X :&: X
       , Star X
       , Atom A
       , Atom B
       , Atom C
       , Eps
       , Nil
       , X .>. (X .+. Eps)
       , X .>. (X .+. Eps) .&. X .>. (X .+. Eps)
       ]

