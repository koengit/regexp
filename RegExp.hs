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

instance Arbitrary a => Arbitrary (R a) where
  arbitrary = sized go
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

