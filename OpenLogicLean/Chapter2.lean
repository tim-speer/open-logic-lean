import Mathlib.Data.Set.Basic
import OpenLogicLean.Chapter1


/-*********
Section 2.1
*********-/
section Section_2_1

-- Definition 2.1 --
def binary_relation {α : Type}
  (R : Set (Set (Set α))) (A : Set α) : Prop :=
  subset R (cartesian_product A A)

end Section_2_1
