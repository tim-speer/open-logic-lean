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


/-*********
Section 2.3
*********-/
section Section_2_3

-- Definition 2.3 --
def reflexive {α : Type} (R : Set (Set (Set α))) (A : Set α) : Prop :=
  binary_relation R A ∧
  (∀ x, x ∈ A → binary_relation R A → (ordered_pair x x) ∈ R)

-- Definition 2.4 --
def transitive {α : Type} (R : Set (Set (Set α))) (A : Set α) : Prop :=
  binary_relation R A ∧
  (∀ x y z, x ∈ A ∧ y ∈ A ∧ z ∈ A →
  (ordered_pair x y) ∈ R ∧ (ordered_pair y z) ∈ R →
  (ordered_pair x z) ∈ R)

-- Definition 2.5 --
def symmetric {α : Type} (R : Set (Set (Set α))) (A : Set α) : Prop :=
  binary_relation R A ∧
  (∀ x y , x ∈ A ∧ y ∈ A → (ordered_pair x y) ∈ R →
  (ordered_pair y x ∈ R))

-- Definition 2.6 --
def anti_symmetric {α : Type} (R : Set (Set (Set α))) (A : Set α)
  : Prop :=
  binary_relation R A ∧
  (∀ x y, x ∈ A ∧ y ∈ A → (ordered_pair x y) ∈ R ∧ (ordered_pair y x ∈ R)
  → x = y)

-- Definition 2.7 --
def connected {α : Type} (R : Set (Set (Set α))) (A : Set α) : Prop :=
  binary_relation R A ∧
  (∀ x y, x ∈ A ∧ y ∈ A → x ≠ y →
  (ordered_pair x y) ∈ R ∨ (ordered_pair y x) ∈ R)

-- Definition 2.8 --
def irreflexive {α : Type} (R : Set (Set (Set α))) (A : Set α) : Prop :=
  binary_relation R A ∧
  (∀ x, x ∈ A → (ordered_pair x x) ∉ R)

-- Definition 2.9 --
def asymmetric {α : Type} (R : Set (Set (Set α))) (A : Set α) : Prop :=
  binary_relation R A ∧
  (∀ x y, x ∈ A ∧ y ∈ A → x ≠ y →
  (ordered_pair x y) ∉ R ∨ (ordered_pair y x) ∉ R)

end Section_2_3


/-*********
Section 2.4
*********-/
section Section_2_4

-- Definition 2.10 --
def equivalence_relation {α : Type} (R : Set (Set (Set α))) (A : Set α) : Prop :=
  reflexive R A ∧ symmetric R A ∧ transitive R A

def equivalence_class {α : Type} (R : Set (Set (Set α))) (A : Set α) (x : α)
  (x_in_A : x ∈ A) (eq_rel : equivalence_relation R A) : Set α :=
  {y : α | y ∈ A ∧ (ordered_pair x y ∈ R)}

end Section_2_4
