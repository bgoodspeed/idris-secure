module ListProofs

{-
splitProp : (l : List a) -> (f : (a -> Bool)) -> ((length (split f l) >= 1) = True)
splitProp [] f = Refl
splitProp (x :: xs) f = case (f x) of 
                             True  => ?spC1
                             False => ?spC2

-}


splitProp : (l : List a) -> (f : (a -> Bool)) -> ((length (split f l) >= 1) = True)
splitProp [] f = Refl
splitProp (x :: xs) f =
  let inductiveHypothesis = splitProp xs f in
      ?splitPropStepCase

-- intros; rewrite inductiveHypothesis;       
