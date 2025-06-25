import Mathlib.Data.Set.Basic
import OpenLogicLean.Chapter1


/-*********
Section 2.1
*********-/
section Section_2_1

-- Definition 2.1 --
def is_binary_relation {α : Type}
  (R : Set (Set (Set α))) (A : Set α) : Prop :=
  subset R (cartesian_product A A)

structure binary_relation where
  α : Type
  A : Set α
  R : Set (Set (Set α))
  br : is_binary_relation R A

end Section_2_1


/-*********
Section 2.3
*********-/
section Section_2_3

-- Definition 2.3 --
def reflexive (bin_rel : binary_relation) : Prop :=
  ∀ x, x ∈ bin_rel.A → (ordered_pair x x) ∈ bin_rel.R

-- Definition 2.4 --
def transitive (bin_rel : binary_relation) : Prop :=
  ∀ x y z, x ∈ bin_rel.A ∧ y ∈ bin_rel.A ∧ z ∈ bin_rel.A →
  (ordered_pair x y) ∈ bin_rel.R ∧ (ordered_pair y z) ∈ bin_rel.R →
  (ordered_pair x z) ∈ bin_rel.R

-- Definition 2.5 --
def symmetric (bin_rel : binary_relation) : Prop :=
  ∀ x y, x ∈ bin_rel.A ∧ y ∈ bin_rel.A → (ordered_pair x y) ∈ bin_rel.R →
  (ordered_pair y x ∈ bin_rel.R)

-- Definition 2.6 --
def anti_symmetric (bin_rel : binary_relation) : Prop :=
  ∀ x y, x ∈ bin_rel.A ∧ y ∈ bin_rel.A →
  (ordered_pair x y) ∈ bin_rel.R ∧ (ordered_pair y x ∈ bin_rel.R) → x = y

-- Definition 2.7 --
def connected (bin_rel : binary_relation) : Prop :=
  ∀ x y, x ∈ bin_rel.A ∧ y ∈ bin_rel.A → x ≠ y →
  (ordered_pair x y) ∈ bin_rel.R ∨ (ordered_pair y x) ∈ bin_rel.R

-- Definition 2.8 --
def irreflexive (bin_rel : binary_relation) : Prop :=
  ∀ x, x ∈ bin_rel.A → (ordered_pair x x) ∉ bin_rel.R

-- Definition 2.9 --
def asymmetric (bin_rel : binary_relation) : Prop :=
  ∀ x y, x ∈ bin_rel.A ∧ y ∈ bin_rel.A → x ≠ y →
  (ordered_pair x y) ∉ bin_rel.R ∨ (ordered_pair y x) ∉ bin_rel.R

end Section_2_3


/-*********
Section 2.4
*********-/
section Section_2_4

-- Definition 2.10 --
def is_equivalence_relation (bin_rel : binary_relation) : Prop :=
  reflexive bin_rel ∧ symmetric bin_rel ∧ transitive bin_rel

structure equivalence_relation where
  bin_rel : binary_relation
  er : is_equivalence_relation bin_rel

-- Definition 2.11 --
def equivalence_class (eq_rel : equivalence_relation) (x : eq_rel.bin_rel.α)
  (x_in_A : x ∈ eq_rel.bin_rel.A) : Set eq_rel.bin_rel.α :=
  {y : eq_rel.bin_rel.α | ordered_pair x y ∈ eq_rel.bin_rel.R}


end Section_2_4
