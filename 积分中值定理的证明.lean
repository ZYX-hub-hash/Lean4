import Mathlib

--基本定义
def ContinuousClose (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ContinuousOn f (Set.Icc a b)
def defIntegral (f : ℝ → ℝ) (a b J : ℝ) : Prop :=
  J = ∫ x in a..b, f x
def MaxValue (f : ℝ → ℝ) (s : Set ℝ) (M : ℝ) : Prop :=
  M ∈ s ∧ ∀ x ∈ s, f x ≤ f M
def MinValue (f : ℝ → ℝ) (s : Set ℝ) (m : ℝ) : Prop :=
  m ∈ s ∧ ∀ x ∈ s, f m ≤ f x
notation "[" a "," b "]" => Set.Icc a b
def IntegrableOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  a ≤ b ∧ ∃ J : ℝ, defIntegral f a b J

--积分不等式的性质
axiom IntegralMonotonicity
  (a b : ℝ) (f g : ℝ → ℝ)
  (hf : IntegrableOn f a b)
  (hg : IntegrableOn g a b):
  (∀ x ∈ ([a, b] : Set ℝ), f x ≤ g x) →
  defIntegral f a b  ≤ defIntegral g a b

axiom IntegralInequality {f : ℝ → ℝ} {a b J m M : ℝ}
  (h1 : defIntegral f a b J)
  (h_min : ∀ x, x ∈ ([a, b] : Set ℝ) → m ≤ f x)
  (h_max : ∀ x, x ∈ ([a, b] : Set ℝ) → f x ≤ M) :
  m * (b - a) ≤ J ∧ J ≤ M * (b - a)

axiom IntegralAbsIneq (a b : ℝ) (f : ℝ → ℝ) (h : IntegrableOn f a b) :
    abs (∫ x in a..b, f x)  ≤ ∫ x in a..b, abs (f x)

--最值定理的证明
theorem ExtremeValueTheorem (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hcont : ContinuousClose f a b) :
    ∃ M m, MaxValue f [a, b] M ∧ MinValue f [a, b] m := by
  have h_compact : IsCompact [a, b] := isCompact_Icc
  have h_nonempty : ([a, b] : Set ℝ).Nonempty := by
    refine ⟨a, ?_⟩
    exact ⟨le_refl a, hab⟩
  rcases h_compact.exists_isMaxOn h_nonempty hcont with ⟨M, hM, hM_max⟩
  rcases h_compact.exists_isMinOn h_nonempty hcont with ⟨m, hm, hm_min⟩
  refine ⟨M, m, ?_, ?_⟩
  · exact ⟨hM, fun x hx => hM_max hx⟩
  · exact ⟨hm, fun x hx => hm_min hx⟩

-- 介值定理的证明
theorem IntermediateValueTheorem (f : ℝ → ℝ) (a b : ℝ) (_ : a ≤ b)
    (hcont : ContinuousClose f a b) (c : ℝ) :
    (∃ m M, MinValue f (Set.Icc a b) m ∧ MaxValue f (Set.Icc a b) M ∧
      f m ≤ c ∧ c ≤ f M) → ∃ ξ ∈ Set.Icc a b, f ξ = c := by
  intro h
  rcases h with ⟨m, M, hm_min, hM_max, hmc, hcM⟩
  have ⟨hm, hmin_prop⟩ := hm_min
  have ⟨hM, hmax_prop⟩ := hM_max
  set F : ℝ → ℝ := fun x => f x - c with hF_def
  have hF_cont : ContinuousClose F a b := by
    unfold ContinuousClose at hcont ⊢
    have : F = f - fun _ => c := by
      ext x; simp [F]
    rw [this]
    exact ContinuousOn.sub hcont continuousOn_const
  have hFm : F m = f m - c := rfl
  have hFM : F M = f M - c := rfl
  have hFm_nonpos : F m ≤ 0 := by
    rw [hFm]
    linarith
  have hFM_nonneg : 0 ≤ F M := by
    rw [hFM]
    linarith
  by_cases hmM : m ≤ M
  · have hsub : Set.Icc m M ⊆ Set.Icc a b :=
      Set.Icc_subset_Icc hm.1 hM.2
    have hF_cont_sub : ContinuousOn F (Set.Icc m M) :=
      hF_cont.mono hsub
    have h_contains : Set.Icc (F m) (F M) ⊆ F '' Set.Icc m M :=
      intermediate_value_Icc hmM hF_cont_sub
    have h_zero_in_interval : (0 : ℝ) ∈ Set.Icc (F m) (F M) :=
      ⟨hFm_nonpos, hFM_nonneg⟩
    have h_mem : (0 : ℝ) ∈ F '' Set.Icc m M :=
      h_contains h_zero_in_interval
    rcases h_mem with ⟨ξ, hξ, hFξ⟩
    refine ⟨ξ, ⟨by linarith [hξ.1, hm.1], by linarith [hξ.2, hM.2]⟩, ?_⟩
    dsimp [F] at hFξ
    linarith
  · have hsub : Set.Icc M m ⊆ Set.Icc a b :=
      Set.Icc_subset_Icc hM.1 hm.2
    have hF_cont_sub : ContinuousOn F (Set.Icc M m) :=
      hF_cont.mono hsub
    have h_contains : Set.Icc (F m) (F M) ⊆ F '' Set.Icc M m :=
      intermediate_value_Icc' (by linarith) hF_cont_sub
    have h_zero_in_interval : (0 : ℝ) ∈ Set.Icc (F m) (F M) :=
      ⟨hFm_nonpos, hFM_nonneg⟩
    have h_mem : (0 : ℝ) ∈ F '' Set.Icc M m :=
      h_contains h_zero_in_interval
    rcases h_mem with ⟨ξ, hξ, hFξ⟩
    refine ⟨ξ, ⟨by linarith [hξ.1, hM.1], by linarith [hξ.2, hm.2]⟩, ?_⟩
    dsimp [F] at hFξ
    linarith

-- 积分中值定理的证明
theorem IntegralMeanValueTheorem (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hcont : ContinuousClose f a b) :
    ∃ ξ ∈ ([a, b] : Set ℝ), (f ξ) * (b - a) = ∫ x in a..b, f x := by

  by_cases h : a = b
  · subst h
    have : ∫ x in a..a, f x = 0 := intervalIntegral.integral_same
    refine ⟨a, ⟨le_refl a, le_refl a⟩, ?_⟩
    simp

  have hlt : a < b := lt_of_le_of_ne hab h

  rcases ExtremeValueTheorem f a b hab hcont with ⟨M, m, hMax, hMin⟩
  let s := ([a, b] : Set ℝ)
  have hM_max : MaxValue f s M := by
    rcases hMax with ⟨hM, hM_max⟩
    exact ⟨hM, hM_max⟩
  have hm_min : MinValue f s m := by
    rcases hMin with ⟨hm, hm_min⟩
    exact ⟨hm, hm_min⟩

  set J := ∫ x in a..b, f x with hJ_def
  have h_integral : defIntegral f a b J := by
    rw [defIntegral]

  have h_lower : ∀ x, x ∈ s → f m ≤ f x := by
    intro x hx
    exact hm_min.2 x hx
  have h_upper : ∀ x, x ∈ s → f x ≤ f M := by
    intro x hx
    exact hM_max.2 x hx

  have h_ineq := IntegralInequality h_integral h_lower h_upper
  rcases h_ineq with ⟨h_left, h_right⟩

  set avg := J / (b - a) with hav_def
  have h_denom_ne_zero : b - a ≠ 0 := by
    linarith [hlt]
  have h_avg_bounds : f m ≤ avg ∧ avg ≤ f M := by
    have hpos : 0 < b - a := sub_pos_of_lt hlt
    constructor
    · unfold avg
      apply le_of_mul_le_mul_right ?_ hpos
      calc f m * (b - a) ≤ J := h_left
       _ = (J / (b - a)) * (b - a) := by field_simp [ne_of_gt hpos]
    · unfold avg
      apply le_of_mul_le_mul_right ?_ hpos
      calc (J / (b - a)) * (b - a) = J := by field_simp [ne_of_gt hpos]
      _ ≤ f M * (b - a) := h_right

  have h_cont_on : ContinuousOn f s := hcont
  have h_avg_mem : avg ∈ Set.Icc (f m) (f M) := by
    exact ⟨h_avg_bounds.left, h_avg_bounds.right⟩

  have h_theorem_condition : ∃ m M, MinValue f s m ∧ MaxValue f s M ∧ f m ≤ avg ∧ avg ≤ f M := by
    refine ⟨m, M, ?_, ?_, h_avg_bounds.left, h_avg_bounds.right⟩
    · exact ⟨hm_min.1, hm_min.2⟩
    · exact ⟨hM_max.1, hM_max.2⟩

  rcases IntermediateValueTheorem f a b hab hcont avg h_theorem_condition with ⟨ξ, hξ, h_eq⟩

  refine ⟨ξ, hξ, ?_⟩
  have : f ξ = J / (b - a) := by
    dsimp [avg] at h_eq
    exact h_eq
  calc
    f ξ * (b - a) = (J / (b - a)) * (b - a) := by rw [this]
    _ = J := by field_simp [ne_of_gt (sub_pos_of_lt hlt)]
