import Mathlib.Data.Set.Basic


/-*********
Section 1.1
*********-/
section Section_1_1

-- Definition 1.1 --
def set_equality {α : Type} (A B : Set α) : Prop :=
  ∀ x, x ∈ A ↔ x ∈ B

end Section_1_1


/-*********
Section 1.2
*********-/
section Section_1_2

-- Definition 1.5 --
def subset {α : Type} (A B : Set α) : Prop :=
  ∀ x, x ∈ A → x ∈ B

def proper_subset {α : Type} (A B : Set α) : Prop :=
  subset A B ∧ ¬ set_equality A B

-- Example 1.6 --
theorem subset_self {α : Type} (A : Set α) : subset A A := by
  rw [subset]
  intro x x_in_A
  exact x_in_A

-- Proposition 1.8 --
theorem Proposition_1_8 {α : Type} (A B : Set α) :
  set_equality A B ↔ subset A B ∧ subset B A := by
  rw [set_equality, subset, subset]
  constructor
  . intro A_equals_B
    constructor
    . intro x x_in_A
      apply (A_equals_B x).mp x_in_A
    . intro x x_in_B
      apply (A_equals_B x).mpr x_in_B
  . intro ⟨A_subset_B, B_subset_A⟩ x
    constructor
    . intro x_in_A
      exact A_subset_B x x_in_A
    . intro x_in_B
      exact B_subset_A x x_in_B

-- Definition 1.10 --
def power_set {α : Type} (A : Set α) : Set (Set α) :=
  {B : Set α | subset B A}

end Section_1_2


/-*********
Section 1.4
*********-/
section Section_1_4

-- Definition 1.15 --
def set_union {α : Type} (A B : Set α) : Set α :=
  {x : α | x ∈ A ∨ x ∈ B}

-- Definition 1.17 --
def set_intersection {α : Type} (A B : Set α) : Set α :=
  {x : α | x ∈ A ∧ x ∈ B}

-- Definition 1.22 --
def set_difference {α : Type} (A B : Set α) : Set α :=
  {x : α | x ∈ A ∧ x ∉ B}

end Section_1_4


/-*********
Section 1.5
*********-/
section Section_1_5

-- Definition 1.23 --
def ordered_pair {α : Type} (a b : α) : Set (Set α) :=
  {{a}, {a, b}}

-- Definitino 1.24 --
def cartesian_product {α : Type} (A B : Set α) : Set (Set (Set α)) :=
  {x : Set (Set α) | ∃ a ∈ A, ∃ b ∈ B, x = ordered_pair a b}

end Section_1_5
