# Lean4
import Mathlib

def BelongTo {α : Type} (x : α) (X : Set α) : Prop := x ∈ X
def EmptySet {α : Type }{x : α} : Set α := { x : α | False }
def NotEmptySet {α : Type } (S : Set α) : Prop := ∃ x : α, x ∈ S
def Subset {α : Type _} (A B : Set α) : Prop := ∀ x : α, x ∈ A → x ∈ B
def UnionSet {α : Type} (A B : Set α) : Set α :=
{ x : α | x ∈ A ∨ x ∈ B }
def InterSet {α : Type} (A B : Set α) : Set α :=
  { x : α | x ∈ A ∧ x ∈ B }
axiom choice {α : Type } : ∀ X : Set α, X.Nonempty → ∃ x : α, x ∈ X
def openInterval (a b : ℝ) : Set ℝ :=
  { x : ℝ | a < x ∧ x < b }
notation  "("a ","b ")"  => openInterval a b
def closedInterval (a b : ℝ) : Set ℝ :=
  { x : ℝ | a ≤ x ∧ x ≤ b }
notation "[" a "," b "]"  => closedInterval a b
def LeftOpenRightClosedInterval (a b : ℝ) : Set ℝ :=
  { x : ℝ | a < x ∧ x ≤ b }
notation  "(" a"," b"]" => LeftOpenRightClosedInterval a b
notation  "("a ","b ")"  => openInterval a b
def LeftClosedRightOpenInterval (a b : ℝ) : Set ℝ :=
  { x : ℝ | a ≤ x ∧ x < b }
  notation  "[" a"," b")" => LeftClosedRightOpenInterval a b
def Neighborhood (a : ℝ) (ε : ℝ) (hε : 0 < ε) : Set ℝ :={ x : ℝ | abs (x - a) < ε }
notation "O("a ","ε ")"=> Neighborhood a ε
def deletedNeighborhood (a : ℝ) (ε : ℝ) (hε : 0 < ε): Set ℝ :=
  { x : ℝ | abs (x - a) < ε ∧ x ≠ a }
notation "O*" "(" a "," ε ")" => deletedNeighborhood a ε
def UpperBound (X : Set ℝ) (u : ℝ) : Prop :=
  ∀ x ∈ X, x ≤ u
def LowerBound (X : Set ℝ) (l : ℝ) : Prop :=
  ∀ x ∈ X, l ≤ x
def Infimum (E : Set ℝ) (α : ℝ) : Prop :=
LowerBound E α ∧
(∀ ε > 0, ∃ x₀ ∈ E, x₀ < α + ε)
notation "inf" E=> Infimum E
inductive prod (α β : Type u) : Type u where |mk : α → β → prod α β

notation:60 a ", " b => Prod.mk a b
def Function {α β : Type} (S : Set (Prod α β)) : Prop :=
  ∀ a b1 b2, (a, b1) ∈ S ∧ (a, b2) ∈ S → b1 = b2
def Domain {α : Type u} {β : Type v} (S : Set (α × β)) : Set α :=
  { a : α | ∃ b , (a, b) ∈ S }
def Range {α : Type u} {β : Type v} (S : Set (α × β)) : Set β :=
  { b : β | ∃ a , (a, b) ∈ S }
def LimitAt (x₀ : ℝ) (f : ℝ → ℝ) (A : ℝ) : Prop :=
  ∀ (ε : ℝ), ε > 0 → ∃ (δ : ℝ), δ > 0 ∧ ∀ (x : ℝ), (0 < |x - x₀| ∧ |x - x₀| < δ) → |f x - A| < ε
def ContinuousFunctionAt (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ (ε : ℝ), ε > 0 → ∃ (δ : ℝ), δ > 0 ∧ ∀ (x : ℝ), |x - a| < δ → |f x - f a| < ε
def ContinuousOnClosedInterval (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  a ≤ b ∧ ∀ (x : ℝ), x ∈ closedInterval a b → ContinuousFunctionAt f x
def BoundedFunction (X : Set ℝ) (f : ℝ → ℝ) (A B : ℝ): Prop :=
  ∀ (x : ℝ), x ∈ X → A ≤ f x ∧ f x ≤ B
theorem BoundednessTheorem (f : ℝ → ℝ) (a b : ℝ) :
  ContinuousOnClosedInterval f a b → ∃ (A B : ℝ),BoundedFunction (closedInterval a b) f A B :=by
  sorry
def MaxValue (f : ℝ → ℝ) (S : Set ℝ) (M : ℝ) : Prop :=
  M ∈ S ∧ ∀ (x : ℝ), x ∈ S → f x ≤ f M
def MinValue (f : ℝ → ℝ) (S : Set ℝ) (m : ℝ) : Prop :=
  m ∈ S ∧ ∀ (x : ℝ), x ∈ S → f m ≤ f x
theorem ExtremeValueTheorem (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hcont : ContinuousOnClosedInterval f a b) :
    ∃ M m, MaxValue f (closedInterval a b) M ∧ MinValue f (closedInterval a b) m := by
    sorry
theorem BolzanoTheorem (f : ℝ → ℝ) (a b : ℝ) :
  ContinuousOnClosedInterval f a b →
  (f a * f b ≤ 0) →
  ∃ (ξ: ℝ), ξ ∈ closedInterval a b ∧ f ξ = 0 := by
  sorry
theorem IntermediateValueTheorem (f : ℝ → ℝ) (a b : ℝ) (_ : a ≤ b)
    (hcont : ContinuousOnClosedInterval f a b) (c : ℝ) :
    (∃ m M, MinValue f (closedInterval a b) m ∧ MaxValue f (closedInterval a b) M ∧
      f m ≤ c ∧ c ≤ f M) → ∃ (ξ: ℝ), ξ ∈ closedInterval a b ∧ f ξ = c := by
      sorry
