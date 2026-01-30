import Mathlib
import RateDistortion.Basic
import RateDistortion.GGD.Basic
import RateDistortion.GGD.Moments
import RateDistortion.Axioms.GaussianSmoothing

open scoped BigOperators
open MeasureTheory

noncomputable section
namespace RateDistortion

/-- Score function for GGD (a.e.). -/
def ggdScore (beta alpha x : ℝ) : ℝ :=
  - (beta / (alpha ^ beta)) * Real.sign x * (|x|) ^ (beta - 1)

/-- Fisher information defined via the squared score. -/
def ggdFisherInfo (beta alpha : ℝ) : ℝ :=
  ∫ x : ℝ, (ggdScore beta alpha x) ^ 2 * ggdDensity beta alpha x

/-- Derivative identity for the GGD score. -/
lemma ggdScore_eq_deriv_log {beta alpha : ℝ} (hbeta : 1 < beta) (halpha : 0 < alpha) :
    ∀ x, ggdScore beta alpha x = deriv (fun y => Real.log (ggdDensity beta alpha y)) x := by
  intro x
  have hbeta_pos : 0 < beta := by linarith
  have hGammaPos : 0 < Real.Gamma (1 / beta) := by
    exact Real.Gamma_pos_of_pos (one_div_pos.mpr hbeta_pos)
  have hden : 0 < 2 * alpha * Real.Gamma (1 / beta) := by
    have h2a : 0 < 2 * alpha := by nlinarith [halpha]
    exact mul_pos h2a hGammaPos
  have hCpos : 0 < ggdC beta alpha := by
    unfold ggdC
    exact div_pos hbeta_pos hden
  have hlog :
      (fun y : ℝ => Real.log (ggdDensity beta alpha y)) =
        fun y : ℝ => Real.log (ggdC beta alpha) + (-(|y| / alpha) ^ beta) := by
    funext y
    have hExp : 0 < Real.exp (-(|y| / alpha) ^ beta) := by
      exact Real.exp_pos _
    have hCne : ggdC beta alpha ≠ 0 := ne_of_gt hCpos
    have hExpne : Real.exp (-(|y| / alpha) ^ beta) ≠ 0 := ne_of_gt hExp
    calc
      Real.log (ggdDensity beta alpha y)
          = Real.log (ggdC beta alpha * Real.exp (-(|y| / alpha) ^ beta)) := by
              rfl
      _ = Real.log (ggdC beta alpha) +
            Real.log (Real.exp (-(|y| / alpha) ^ beta)) := by
              simpa using
                (Real.log_mul (x := ggdC beta alpha)
                  (y := Real.exp (-(|y| / alpha) ^ beta)) hCne hExpne)
      _ = Real.log (ggdC beta alpha) + (-(|y| / alpha) ^ beta) := by
            simp
  have hpow_abs :
      HasDerivAt (fun y : ℝ => |y| ^ beta) (beta * |x| ^ (beta - 2) * x) x := by
    simpa using (hasDerivAt_abs_rpow (x := x) (p := beta) hbeta)
  have hdiv_fun :
      (fun y : ℝ => (|y| / alpha) ^ beta) =
        fun y : ℝ => (1 / alpha ^ beta) * (|y| ^ beta) := by
    funext y
    have hy : 0 ≤ |y| := abs_nonneg y
    have ha : 0 ≤ alpha := le_of_lt halpha
    calc
      (|y| / alpha) ^ beta = |y| ^ beta / alpha ^ beta := by
        simpa using (Real.div_rpow hy ha beta)
      _ = (1 / alpha ^ beta) * |y| ^ beta := by
        ring
  have hpow_div :
      HasDerivAt (fun y : ℝ => (|y| / alpha) ^ beta)
        ((1 / alpha ^ beta) * (beta * |x| ^ (beta - 2) * x)) x := by
    simpa [hdiv_fun] using (hpow_abs.const_mul (1 / alpha ^ beta))
  have hneg :
      HasDerivAt (fun y : ℝ => - (|y| / alpha) ^ beta)
        (-((1 / alpha ^ beta) * (beta * |x| ^ (beta - 2) * x))) x := by
    simpa using hpow_div.neg
  have hderiv :
      deriv (fun y : ℝ => Real.log (ggdDensity beta alpha y)) x =
        -((1 / alpha ^ beta) * (beta * |x| ^ (beta - 2) * x)) := by
    have h1 :
        deriv (fun y : ℝ => Real.log (ggdDensity beta alpha y)) x =
          deriv (fun y : ℝ => - (|y| / alpha) ^ beta) x := by
      simpa [hlog] using
        (deriv_const_add (f := fun y : ℝ => - (|y| / alpha) ^ beta)
          (c := Real.log (ggdC beta alpha)) (x := x))
    have h2 :
        deriv (fun y : ℝ => - (|y| / alpha) ^ beta) x =
          -((1 / alpha ^ beta) * (beta * |x| ^ (beta - 2) * x)) := by
      simpa using hneg.deriv
    exact h1.trans h2
  have hsign_abs : Real.sign x * |x| = x := by
    by_cases hx0 : x = 0
    · simp [hx0]
    · have hxlt : x < 0 ∨ 0 < x := lt_or_gt_of_ne hx0
      cases hxlt with
      | inl hlt =>
          simp [Real.sign_of_neg hlt, abs_of_neg hlt, mul_comm, mul_left_comm, mul_assoc]
      | inr hgt =>
          simp [Real.sign_of_pos hgt, abs_of_pos hgt]
  have hpow_sign :
      Real.sign x * |x| ^ (beta - 1) = |x| ^ (beta - 2) * x := by
    by_cases hx0 : x = 0
    · simp [hx0]
    · have hxne : |x| ≠ 0 := by
        simpa [abs_eq_zero] using hx0
      have hpow : |x| ^ (beta - 1) = |x| ^ (beta - 2) * |x| := by
        calc
          |x| ^ (beta - 1) = |x| ^ ((beta - 2) + 1) := by ring_nf
          _ = |x| ^ (beta - 2) * |x| := by
                simpa using (Real.rpow_add_one (x := |x|) (y := beta - 2) hxne)
      calc
        Real.sign x * |x| ^ (beta - 1)
            = Real.sign x * (|x| ^ (beta - 2) * |x|) := by simp [hpow]
        _ = |x| ^ (beta - 2) * (Real.sign x * |x|) := by ring
        _ = |x| ^ (beta - 2) * x := by simp [hsign_abs]
  have hscore :
      ggdScore beta alpha x =
        -((1 / alpha ^ beta) * (beta * |x| ^ (beta - 2) * x)) := by
    unfold ggdScore
    calc
      - (beta / alpha ^ beta) * Real.sign x * |x| ^ (beta - 1)
          = -((1 / alpha ^ beta) * (beta * (Real.sign x * |x| ^ (beta - 1)))) := by
              ring
      _ = -((1 / alpha ^ beta) * (beta * (|x| ^ (beta - 2) * x))) := by
              simp [hpow_sign]
      _ = -((1 / alpha ^ beta) * (beta * |x| ^ (beta - 2) * x)) := by
              ring
  simpa [hscore] using hderiv.symm

/-- GGD has finite Fisher information for β > 1. -/
theorem ggd_hasFiniteFisherInfo {beta alpha : ℝ} (hbeta : 1 < beta) (halpha : 0 < alpha) :
  HasFiniteFisherInfo (ggdDensity beta alpha) := by
  -- The score is -(β/α^β) · sign(x) · |x|^(β-1)
  -- For β > 1, |x|^(β-1) → 0 as x → 0, so score is bounded near 0
  -- Square-integrability follows from exponential tail decay
  classical
  refine ⟨ggdScore beta alpha, ?_, ?_⟩
  · intro x hx
    -- ggdDensity is positive, so hx is unused; compute derivative directly
    simpa using (ggdScore_eq_deriv_log (beta := beta) (alpha := alpha) hbeta halpha x)
  · -- integrability via moment formula
    have hbeta_pos : 0 < beta := by linarith
    have hp : -1 < 2 * (beta - 1) := by linarith
    have hmoment :=
      ggd_abs_moment_integral (beta := beta) (alpha := alpha) (p := 2 * (beta - 1))
        hbeta_pos halpha hp
    have hpow2 : ∀ x : ℝ, (|x| ^ (beta - 1)) ^ 2 = |x| ^ (2 * (beta - 1)) := by
      intro x
      have hxnonneg : 0 ≤ |x| := abs_nonneg x
      calc
        (|x| ^ (beta - 1)) ^ 2 = (|x| ^ (beta - 1)) ^ (2 : ℝ) := by
          symm; exact (Real.rpow_natCast (|x| ^ (beta - 1)) 2)
        _ = |x| ^ ((beta - 1) * 2) := by
          symm; exact (Real.rpow_mul hxnonneg (beta - 1) 2)
        _ = |x| ^ (2 * (beta - 1)) := by ring_nf
    have hsignpow : ∀ x : ℝ, (Real.sign x) ^ 2 * |x| ^ (2 * (beta - 1))
        = |x| ^ (2 * (beta - 1)) := by
      intro x
      by_cases hx0 : x = 0
      · have hne : (2 * (beta - 1)) ≠ 0 := by nlinarith [hbeta]
        simp [hx0, hne]
      · obtain hs | hs := Real.sign_apply_eq_of_ne_zero x hx0 <;> simp [hs]
    have hrew :
        (fun x : ℝ =>
            (ggdScore beta alpha x) ^ 2 * ggdDensity beta alpha x) =
          fun x : ℝ =>
            (beta / alpha ^ beta) ^ 2 *
              |x| ^ (2 * (beta - 1)) * ggdDensity beta alpha x := by
      funext x
      unfold ggdScore
      have hpow2' := hpow2 x
      have hbc :
          (Real.sign x) ^ 2 * (|x| ^ (beta - 1)) ^ 2 = |x| ^ (2 * (beta - 1)) := by
        calc
          (Real.sign x) ^ 2 * (|x| ^ (beta - 1)) ^ 2
              = (Real.sign x) ^ 2 * |x| ^ (2 * (beta - 1)) := by
                  simp [hpow2']
          _ = |x| ^ (2 * (beta - 1)) := by
                simpa using hsignpow x
      calc
        (-(beta / alpha ^ beta) * Real.sign x * |x| ^ (beta - 1)) ^ 2 *
            ggdDensity beta alpha x
            =
            (beta / alpha ^ beta) ^ 2 * (Real.sign x) ^ 2 *
              (|x| ^ (beta - 1)) ^ 2 * ggdDensity beta alpha x := by
                ring
        _ =
            (beta / alpha ^ beta) ^ 2 *
              ((Real.sign x) ^ 2 * (|x| ^ (beta - 1)) ^ 2) *
                ggdDensity beta alpha x := by
            ring_nf
        _ = (beta / alpha ^ beta) ^ 2 *
              |x| ^ (2 * (beta - 1)) * ggdDensity beta alpha x := by
            exact
              congrArg
                (fun t =>
                  (beta / alpha ^ beta) ^ 2 * t * ggdDensity beta alpha x)
                hbc
    have hconst_pos : 0 < (beta / alpha ^ beta) ^ 2 := by
      have hpowpos : 0 < alpha ^ beta := by
        exact Real.rpow_pos_of_pos halpha _
      have hfrac : 0 < beta / alpha ^ beta := by
        exact div_pos hbeta_pos hpowpos
      nlinarith
    have hGammaPos : 0 < Real.Gamma ((2 * (beta - 1) + 1) / beta) := by
      have hnum : 0 < 2 * (beta - 1) + 1 := by linarith
      have harg : 0 < (2 * (beta - 1) + 1) / beta := by
        exact div_pos hnum hbeta_pos
      exact Real.Gamma_pos_of_pos harg
    have hGammaPos' : 0 < Real.Gamma (1 / beta) := by
      exact Real.Gamma_pos_of_pos (one_div_pos.mpr hbeta_pos)
    have halpha_pos : 0 < alpha ^ (2 * (beta - 1)) := by
      exact Real.rpow_pos_of_pos halpha _
    have hmoment_pos :
        0 <
          alpha ^ (2 * (beta - 1)) *
            Real.Gamma ((2 * (beta - 1) + 1) / beta) / Real.Gamma (1 / beta) := by
      exact div_pos (mul_pos halpha_pos hGammaPos) hGammaPos'
    have hval :
        (∫ x : ℝ, |x| ^ (2 * (beta - 1)) * ggdDensity beta alpha x) =
          alpha ^ (2 * (beta - 1)) *
            Real.Gamma ((2 * (beta - 1) + 1) / beta) / Real.Gamma (1 / beta) := by
      simpa using hmoment
    have hcalc :
        (∫ x : ℝ, (ggdScore beta alpha x) ^ 2 * ggdDensity beta alpha x) =
          (beta / alpha ^ beta) ^ 2 *
            (alpha ^ (2 * (beta - 1)) *
              Real.Gamma ((2 * (beta - 1) + 1) / beta) / Real.Gamma (1 / beta)) := by
      have h0 :
          (∫ x : ℝ, (ggdScore beta alpha x) ^ 2 * ggdDensity beta alpha x) =
            (beta / alpha ^ beta) ^ 2 *
              ∫ x : ℝ, |x| ^ (2 * (beta - 1)) * ggdDensity beta alpha x := by
        simpa [hrew, mul_assoc] using
          (MeasureTheory.integral_const_mul
            (r := (beta / alpha ^ beta) ^ 2)
            (f := fun x : ℝ => |x| ^ (2 * (beta - 1)) * ggdDensity beta alpha x))
      simpa [hval] using h0
    have hpos :
        0 <
          (beta / alpha ^ beta) ^ 2 *
            (alpha ^ (2 * (beta - 1)) *
              Real.Gamma ((2 * (beta - 1) + 1) / beta) / Real.Gamma (1 / beta)) := by
      exact mul_pos hconst_pos hmoment_pos
    have hne :
        (∫ x : ℝ, (ggdScore beta alpha x) ^ 2 * ggdDensity beta alpha x) ≠ 0 := by
      nlinarith [hcalc, hpos]
    exact (Integrable.of_integral_ne_zero (μ := volume) hne)

/-- Fisher information closed form (general scale). -/
theorem ggd_fisher_info_formula
  {beta alpha : ℝ} (hbeta : 1 < beta) (halpha : 0 < alpha) :
  ggdFisherInfo beta alpha =
    (beta ^ 2 / alpha ^ 2) * (Real.Gamma (2 - 1 / beta) / Real.Gamma (1 / beta)) := by
  have hbeta_pos : 0 < beta := by linarith
  have hp : -1 < 2 * (beta - 1) := by linarith
  have hmoment :=
    ggd_abs_moment_integral (beta := beta) (alpha := alpha) (p := 2 * (beta - 1))
      hbeta_pos halpha hp
  have hpow2 : ∀ x : ℝ, (|x| ^ (beta - 1)) ^ 2 = |x| ^ (2 * (beta - 1)) := by
    intro x
    have hxnonneg : 0 ≤ |x| := abs_nonneg x
    calc
      (|x| ^ (beta - 1)) ^ 2 = (|x| ^ (beta - 1)) ^ (2 : ℝ) := by
        symm; exact (Real.rpow_natCast (|x| ^ (beta - 1)) 2)
      _ = |x| ^ ((beta - 1) * 2) := by
        symm; exact (Real.rpow_mul hxnonneg (beta - 1) 2)
      _ = |x| ^ (2 * (beta - 1)) := by ring_nf
  have hsignpow : ∀ x : ℝ, (Real.sign x) ^ 2 * |x| ^ (2 * (beta - 1))
      = |x| ^ (2 * (beta - 1)) := by
    intro x
    by_cases hx0 : x = 0
    · have hne : (2 * (beta - 1)) ≠ 0 := by nlinarith [hbeta]
      simp [hx0, hne]
    · obtain hs | hs := Real.sign_apply_eq_of_ne_zero x hx0 <;> simp [hs]
  have hrew :
      (fun x : ℝ => (ggdScore beta alpha x) ^ 2 * ggdDensity beta alpha x) =
        fun x : ℝ =>
          (beta / alpha ^ beta) ^ 2 * |x| ^ (2 * (beta - 1)) * ggdDensity beta alpha x := by
    funext x
    unfold ggdScore
    have hpow2' := hpow2 x
    have hbc :
        (Real.sign x) ^ 2 * (|x| ^ (beta - 1)) ^ 2 = |x| ^ (2 * (beta - 1)) := by
      calc
        (Real.sign x) ^ 2 * (|x| ^ (beta - 1)) ^ 2
            = (Real.sign x) ^ 2 * |x| ^ (2 * (beta - 1)) := by
                simp [hpow2']
        _ = |x| ^ (2 * (beta - 1)) := by
              simpa using hsignpow x
    calc
      (-(beta / alpha ^ beta) * Real.sign x * |x| ^ (beta - 1)) ^ 2 *
          ggdDensity beta alpha x
          =
          (beta / alpha ^ beta) ^ 2 * (Real.sign x) ^ 2 *
            (|x| ^ (beta - 1)) ^ 2 * ggdDensity beta alpha x := by
              ring
      _ =
          (beta / alpha ^ beta) ^ 2 *
            ((Real.sign x) ^ 2 * (|x| ^ (beta - 1)) ^ 2) *
              ggdDensity beta alpha x := by
          ring_nf
      _ = (beta / alpha ^ beta) ^ 2 *
            |x| ^ (2 * (beta - 1)) * ggdDensity beta alpha x := by
          exact
            congrArg
              (fun t =>
                (beta / alpha ^ beta) ^ 2 * t * ggdDensity beta alpha x)
              hbc
  have hgamma :
      (2 * (beta - 1) + 1) / beta = 2 - 1 / beta := by
    have hbne : beta ≠ 0 := by linarith
    field_simp [hbne]; ring
  have hpow2a : (alpha ^ beta) ^ 2 = alpha ^ (2 * beta) := by
    have h := Real.rpow_mul (le_of_lt halpha) beta 2
    have h' : alpha ^ (beta * 2) = (alpha ^ beta) ^ 2 := by
      simpa [Real.rpow_natCast] using h
    simpa [mul_comm] using h'.symm
  have hsub :
      alpha ^ (2 * (beta - 1)) = alpha ^ (2 * beta) / alpha ^ 2 := by
    have hpos : 0 < alpha := halpha
    calc
      alpha ^ (2 * (beta - 1)) = alpha ^ (2 * beta - 2) := by ring_nf
      _ = alpha ^ (2 * beta) / alpha ^ 2 := by
            simpa using (Real.rpow_sub hpos (2 * beta) 2)
  have hconst :
      (beta / alpha ^ beta) ^ 2 * alpha ^ (2 * (beta - 1)) =
        beta ^ 2 / alpha ^ 2 := by
    have hpowpos : 0 < alpha ^ beta := by
      exact Real.rpow_pos_of_pos halpha _
    have hpowne : (alpha ^ beta) ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 (ne_of_gt hpowpos)
    have halphane : alpha ≠ 0 := by exact ne_of_gt halpha
    calc
      (beta / alpha ^ beta) ^ 2 * alpha ^ (2 * (beta - 1))
          = (beta ^ 2 / (alpha ^ beta) ^ 2) * alpha ^ (2 * (beta - 1)) := by
              simp [div_pow]
      _ = (beta ^ 2 / (alpha ^ beta) ^ 2) * (alpha ^ (2 * beta) / alpha ^ 2) := by
              simp [hsub]
      _ = (beta ^ 2 / (alpha ^ beta) ^ 2) * ((alpha ^ beta) ^ 2 / alpha ^ 2) := by
              simp [hpow2a]
      _ = beta ^ 2 / alpha ^ 2 := by
              field_simp [hpowne, halphane]
  unfold ggdFisherInfo
  calc
    (∫ x : ℝ, (ggdScore beta alpha x) ^ 2 * ggdDensity beta alpha x) =
        (beta / alpha ^ beta) ^ 2 *
          ∫ x : ℝ, |x| ^ (2 * (beta - 1)) * ggdDensity beta alpha x := by
      simpa [hrew, mul_assoc] using
        (MeasureTheory.integral_const_mul
          (r := (beta / alpha ^ beta) ^ 2)
          (f := fun x : ℝ => |x| ^ (2 * (beta - 1)) * ggdDensity beta alpha x))
    _ =
        (beta / alpha ^ beta) ^ 2 *
          (alpha ^ (2 * (beta - 1)) *
            Real.Gamma ((2 * (beta - 1) + 1) / beta) / Real.Gamma (1 / beta)) := by
      simp [hmoment]
    _ = (beta ^ 2 / alpha ^ 2) *
          (Real.Gamma (2 - 1 / beta) / Real.Gamma (1 / beta)) := by
      calc
        (beta / alpha ^ beta) ^ 2 *
            (alpha ^ (2 * (beta - 1)) *
              Real.Gamma ((2 * (beta - 1) + 1) / beta) / Real.Gamma (1 / beta)) =
            ((beta / alpha ^ beta) ^ 2 * alpha ^ (2 * (beta - 1))) *
              (Real.Gamma ((2 * (beta - 1) + 1) / beta) / Real.Gamma (1 / beta)) := by
          simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        _ = (beta ^ 2 / alpha ^ 2) *
              (Real.Gamma (2 - 1 / beta) / Real.Gamma (1 / beta)) := by
          simp [hconst, hgamma]

/-- Fisher information formula for unit variance. -/
theorem ggd_fisher_info_unitVar
  {beta : ℝ} (hbeta : 1 < beta) :
  ggdFisherInfo beta (alphaUnitVar beta) =
    beta ^ 2 *
      (Real.Gamma (3 / beta) * Real.Gamma (2 - 1 / beta) /
        (Real.Gamma (1 / beta) ^ 2)) := by
  have hbeta_pos : 0 < beta := by linarith
  have hGamma1 : 0 < Real.Gamma (1 / beta) := by
    exact Real.Gamma_pos_of_pos (one_div_pos.mpr hbeta_pos)
  have hGamma3 : 0 < Real.Gamma (3 / beta) := by
    have hpos : 0 < (3 / beta) := by
      exact div_pos (by norm_num) hbeta_pos
    exact Real.Gamma_pos_of_pos hpos
  have hratio_pos :
      0 < Real.Gamma (1 / beta) / Real.Gamma (3 / beta) := by
    exact div_pos hGamma1 hGamma3
  have halpha : 0 < alphaUnitVar beta := by
    unfold alphaUnitVar
    exact Real.sqrt_pos_of_pos hratio_pos
  have hsq :
      (alphaUnitVar beta) ^ 2 =
        Real.Gamma (1 / beta) / Real.Gamma (3 / beta) := by
    unfold alphaUnitVar
    have hnonneg : 0 ≤ Real.Gamma (1 / beta) / Real.Gamma (3 / beta) := by
      exact le_of_lt hratio_pos
    simpa using (Real.sq_sqrt hnonneg)
  have hinv :
      1 / (alphaUnitVar beta) ^ 2 =
        Real.Gamma (3 / beta) / Real.Gamma (1 / beta) := by
    calc
      1 / (alphaUnitVar beta) ^ 2 = ((alphaUnitVar beta) ^ 2)⁻¹ := by
        simp [one_div]
      _ = (Real.Gamma (1 / beta) / Real.Gamma (3 / beta))⁻¹ := by
        simp [hsq]
      _ = Real.Gamma (3 / beta) / Real.Gamma (1 / beta) := by
        simpa using (inv_div (Real.Gamma (1 / beta)) (Real.Gamma (3 / beta)))
  have hgen :=
    ggd_fisher_info_formula (beta := beta) (alpha := alphaUnitVar beta) hbeta halpha
  calc
    ggdFisherInfo beta (alphaUnitVar beta) =
        (beta ^ 2 / (alphaUnitVar beta) ^ 2) *
          (Real.Gamma (2 - 1 / beta) / Real.Gamma (1 / beta)) := by
      simpa using hgen
    _ =
        (beta ^ 2 * (1 / (alphaUnitVar beta) ^ 2)) *
          (Real.Gamma (2 - 1 / beta) / Real.Gamma (1 / beta)) := by
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    _ =
        (beta ^ 2 * (Real.Gamma (3 / beta) / Real.Gamma (1 / beta))) *
          (Real.Gamma (2 - 1 / beta) / Real.Gamma (1 / beta)) := by
      rw [hinv]
    _ =
        beta ^ 2 *
          ((Real.Gamma (3 / beta) / Real.Gamma (1 / beta)) *
            (Real.Gamma (2 - 1 / beta) / Real.Gamma (1 / beta))) := by
      simp [mul_assoc, mul_left_comm, mul_comm]
    _ =
        beta ^ 2 *
          (Real.Gamma (3 / beta) * Real.Gamma (2 - 1 / beta) /
            (Real.Gamma (1 / beta) ^ 2)) := by
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, pow_two]

/-- GGD Fisher info matches the abstract Fisher info. -/
theorem ggdFisherInfo_eq_fisherInfo {beta alpha : ℝ}
    (hbeta : 1 < beta) (halpha : 0 < alpha) :
    ggdFisherInfo beta alpha = fisherInfo (ggdDensity beta alpha) := by
  have hfi : HasFiniteFisherInfo (ggdDensity beta alpha) :=
    ggd_hasFiniteFisherInfo (beta := beta) (alpha := alpha) hbeta halpha
  have hJ :=
    fisherInfo_eq_of_hasFiniteFisherInfo (f := ggdDensity beta alpha) hfi
  unfold ggdFisherInfo
  calc
    (∫ x : ℝ, (ggdScore beta alpha x) ^ 2 * ggdDensity beta alpha x)
        =
        ∫ x : ℝ,
          (deriv (fun y => Real.log (ggdDensity beta alpha y)) x) ^ 2 *
            ggdDensity beta alpha x := by
      simp [ggdScore_eq_deriv_log (beta := beta) (alpha := alpha) hbeta halpha]
    _ = fisherInfo (ggdDensity beta alpha) := by
      symm
      simpa using hJ

end RateDistortion
