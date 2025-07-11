import Mathlib
import LeanLJ
import LeanLJ.Instance
import LeanLJ.Function
open LeanLJ
namespace LeanLJ

lemma lj_pow_12' (σ r : ℝ) (h : r ≠ 0): deriv (fun r => σ^12 * r ^ (- 12:ℤ) ) r =  σ^12 * (-12:ℤ)  *  r ^ (-13 : ℤ) := by
   rw [deriv_const_mul]
   rw [deriv_zpow]
   rw [show (-12 - 1) = (- 13: ℤ ) by ring]
   ring
   apply DifferentiableAt.zpow
   · apply differentiable_id
   · apply Or.inl
     exact h

lemma lj_pow_6' (σ r : ℝ) (h : r ≠ 0): deriv (fun r => σ^6 * r ^ (- 6:ℤ) ) r =  σ^6 * (-6:ℤ)  *  r ^ (-7 : ℤ) := by
   rw [deriv_const_mul]
   rw [deriv_zpow]
   rw [show (-6 - 1) = (- 7: ℤ ) by ring]
   ring
   apply DifferentiableAt.zpow
   · apply differentiable_id
   · apply Or.inl
     exact h

lemma scale_continuous (ε σ : ℝ) :
  ContinuousOn (fun r => 4 * ε * ((σ / r) ^ 12 - (σ / r) ^ 6)) {r | r > 0} := by
  apply ContinuousOn.mul
  · exact continuous_const.continuousOn
  · apply ContinuousOn.sub <;>
    · apply ContinuousOn.pow
      apply ContinuousOn.div
      · exact continuous_const.continuousOn
      · exact continuous_id.continuousOn
      · exact fun x a => Ne.symm (ne_of_lt a)

theorem Lj_eq (r r_c ε σ : ℝ) : Ljp r r_c ε σ = LJ r r_c ε σ := by
  unfold Ljp
  unfold LJ
  simp
  ring_nf

theorem cutoff_behavior (r r_c ε σ : ℝ)
    (h : r > r_c) : lj_Real r r_c ε σ = 0 := by
  unfold lj_Real
  simp [if_neg (not_le_of_gt h)]


theorem ljp_zero_on_tail (r_c ε σ : ℝ) :
  ∀ r, r > r_c → lj_Real r r_c ε σ = 0 := by
  intro r h
  unfold lj_Real
  simp only [if_neg (not_le_of_gt h)]


theorem ljp_eq_le {r_c ε σ : ℝ} :
  ∀ r ∈ {r | r > 0 ∧ r ≤ r_c }, lj_Real r r_c ε σ = 4 * ε * ((σ / r)^12 - (σ / r)^6) := by
  intro r hr
  have h_r_le_rc : r ≤ r_c := hr.2
  unfold lj_Real
  rw [if_pos h_r_le_rc]
  ring

theorem ljp_eq_gt (r_c ε σ  : ℝ) : ∀ r ∈ {r | r > r_c ∧ r > 0}, lj_Real r r_c ε σ = 0 := by
  intro r hr
  have h_r_gt_rc : r > r_c := hr.1
  have h_r_pos : r > 0 := hr.2
  unfold lj_Real
  rw [if_neg (not_le_of_gt h_r_gt_rc)]


theorem ljp_continuous_closed_domain (r_c ε σ : ℝ) :
  ContinuousOn (fun r => if r ≤ r_c then 4 * ε * (((σ / r) ^ 6) ^ 2 - (σ / r) ^ 6) else 0)
    {r | 0 < r ∧ r ≤ r_c} := by
  have subset_pos : {r | 0 < r ∧ r ≤ r_c} ⊆ {r | r > 0} := by
    intro r hr
    exact hr.1
  have base := (scale_continuous ε σ).mono subset_pos
  apply ContinuousOn.congr base
  intro r hr
  simp [if_pos hr.2]
  left
  ring

theorem ljp_continuous_piecewise (r_c ε σ : ℝ) :
  ContinuousOn (fun r => if r ≤ r_c then 4 * ε * (((σ / r) ^ 6) ^ 2 - (σ / r) ^ 6) else 0)
    {r | 0 < r ∧ r < r_c} := by
  have subset_pos : {r | 0 < r ∧ r < r_c} ⊆ {r | r > 0} := by
    intro r hr
    exact hr.1
  have base := (scale_continuous ε σ).mono subset_pos
  apply ContinuousOn.congr base
  intro r hr
  simp [if_pos (le_of_lt hr.2)]
  left
  ring

theorem ljp_differentiable (r_c ε σ : ℝ) :
  DifferentiableOn ℝ (fun r => if r ≤ r_c then 4 * ε * (((σ / r) ^ 6) ^ 2 - (σ / r) ^ 6) else 0)
    {r | 0 < r ∧ r ≤ r_c} := by
  have subset_pos : {r | 0 < r ∧ r ≤ r_c} ⊆ {r | r > 0} := by
    intro r hr
    exact hr.1
  have base : DifferentiableOn ℝ (fun r => 4 * ε * (((σ / r) ^ 6) ^ 2 - (σ / r) ^ 6)) {r | r > 0} := by
    apply DifferentiableOn.mul
    · intro r hr
      simp only [gt_iff_lt]
      apply differentiableOn_const
      exact hr
    · apply DifferentiableOn.sub
      · apply DifferentiableOn.pow
        · apply DifferentiableOn.pow
          · apply DifferentiableOn.div
            · exact (differentiable_const σ).differentiableOn
            · exact differentiable_id.differentiableOn
            · intro x hx
              exact ne_of_gt hx
      · apply DifferentiableOn.pow
        apply DifferentiableOn.div
        · exact (differentiable_const σ).differentiableOn
        · exact differentiable_id.differentiableOn
        · intro x hx
          exact ne_of_gt hx
  apply DifferentiableOn.congr (base.mono subset_pos)
  · intro r hr
    simp [if_pos hr.2]


theorem ljp_second_derivative (r_c ε σ : ℝ) :
  DifferentiableOn ℝ (fun r => 4 * ε * (156 * σ^12 * r^(-14:ℤ ) - 42 * σ^6 * r^(-8:ℤ))) {r | 0 < r ∧ r ≤ r_c} := by
  apply DifferentiableOn.mul
  · exact (differentiable_const (4 * ε)).differentiableOn
  · apply DifferentiableOn.sub
    · apply DifferentiableOn.const_mul
      apply DifferentiableOn.zpow
      · exact differentiable_id.differentiableOn
      · apply Or.inl
        intro x hx
        exact ne_of_gt hx.1
    · apply DifferentiableOn.const_mul
      apply DifferentiableOn.zpow
      · exact differentiable_id.differentiableOn
      · apply Or.inl
        intro x hx
        exact ne_of_gt hx.1

end LeanLJ
