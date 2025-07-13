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
  {y : eq_rel.bin_rel.α | y ∈ eq_rel.bin_rel.A ∧
                          ordered_pair x y ∈ eq_rel.bin_rel.R}

-- Proposition 2.12 --
theorem Proposition_2_12 (eq_rel : equivalence_relation)
  (x y : eq_rel.bin_rel.α) (x_in_A : x ∈ eq_rel.bin_rel.A)
  (y_in_A : y ∈ eq_rel.bin_rel.A) : ordered_pair x y ∈ eq_rel.bin_rel.R ↔
  set_equality (equivalence_class eq_rel x x_in_A)
  (equivalence_class eq_rel y y_in_A) := by
  constructor
  . intro xy_in_R z
    have yx_in_R : ordered_pair y x ∈ eq_rel.bin_rel.R := by
      apply eq_rel.er.right.left
      exact ⟨x_in_A, y_in_A⟩
      assumption
    constructor
    . intro z_in_eq_cls_x
      have z_in_A : z ∈ eq_rel.bin_rel.A := by
        exact z_in_eq_cls_x.left
      have xz_in_R : ordered_pair x z ∈ eq_rel.bin_rel.R := by
        exact z_in_eq_cls_x.right
      have yz_in_R : ordered_pair y z ∈ eq_rel.bin_rel.R := by
        apply eq_rel.er.right.right y x z
        exact ⟨y_in_A, x_in_A, z_in_A⟩
        exact ⟨yx_in_R, xz_in_R⟩
      exact ⟨z_in_A, yz_in_R⟩
    . intro z_in_eq_cls_y
      have z_in_A : z ∈ eq_rel.bin_rel.A := by
        exact z_in_eq_cls_y.left
      have yz_in_R : ordered_pair y z ∈ eq_rel.bin_rel.R := by
        exact z_in_eq_cls_y.right
      have xz_in_R : ordered_pair x z ∈ eq_rel.bin_rel.R := by
        apply eq_rel.er.right.right x y z
        exact ⟨x_in_A, y_in_A, z_in_A⟩
        exact ⟨xy_in_R, yz_in_R⟩
      exact ⟨z_in_A, xz_in_R⟩
  . intro x_cls_eq_y_cls
    have y_in_cls_y : y ∈ equivalence_class eq_rel y y_in_A := by
      constructor
      assumption
      exact eq_rel.er.left y y_in_A
    have y_in_cls_x : y ∈ equivalence_class eq_rel x x_in_A := by
      exact (x_cls_eq_y_cls y).mpr y_in_cls_y
    exact y_in_cls_x.right

end Section_2_4


/-*********
Section 2.5
*********-/
section Section_2_5

-- Definition 2.14 --
def is_preorder (bin_rel : binary_relation) : Prop :=
  reflexive bin_rel ∧ transitive bin_rel

structure preorder where
  bin_rel : binary_relation
  po : is_preorder bin_rel

-- Definition 2.15 --
def is_partial_order (bin_rel : binary_relation) : Prop :=
  is_preorder bin_rel ∧ anti_symmetric bin_rel

structure partial_order where
  bin_rel : binary_relation
  po : is_partial_order bin_rel

-- Definition 2.16 --
def is_linear_order (bin_rel : binary_relation) : Prop :=
  is_partial_order bin_rel ∧ connected bin_rel

structure linear_order where
  bin_rel : binary_relation
  lo : is_linear_order bin_rel

-- Definition 2.21 --
def is_strict_order (bin_rel : binary_relation) : Prop :=
  irreflexive bin_rel ∧ asymmetric bin_rel ∧ transitive bin_rel

structure strict_order where
  bin_rel : binary_relation
  so : is_strict_order bin_rel

-- Definition 2.22 --
def is_strict_linear_order (bin_rel : binary_relation) : Prop :=
  is_strict_order bin_rel ∧ connected bin_rel

structure strict_linear_order where
  bin_rel : binary_relation
  sl : is_strict_linear_order bin_rel

def diagonal {α : Type} (A : Set α) : Set (Set (Set α)) :=
  {p : Set (Set α) | ∃ a ∈ A, p = ordered_pair a a}

lemma bin_rel_union_diagonal (bin_rel : binary_relation) :
  is_binary_relation (bin_rel.R ∪ diagonal bin_rel.A) bin_rel.A := by
  rw [is_binary_relation, subset]
  intro x x_in_union
  rcases x_in_union with x_in_R | x_in_diagonal
  apply bin_rel.br
  assumption
  rw [cartesian_product]
  simp
  rw [diagonal] at x_in_diagonal
  simp at x_in_diagonal
  rcases x_in_diagonal with ⟨c, h⟩
  use c, h.1, c, h.1, h.2

def reflexive_closure (bin_rel : binary_relation) : binary_relation :=
  { α := bin_rel.α,
    A := bin_rel.A,
    R := bin_rel.R ∪ diagonal bin_rel.A,
    br := bin_rel_union_diagonal bin_rel}

-- Proposition 2.24 --
theorem Proposition_2_24 (s_order : strict_order) :
  is_partial_order (reflexive_closure s_order.bin_rel) := by
  sorry

end Section_2_5
