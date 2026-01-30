import Mathlib
import RateDistortion.Basic
import RateDistortion.GGD.Basic
import RateDistortion.GGD.Moments

noncomputable section
namespace RateDistortion
open MeasureTheory

/-- Closed form for differential entropy in nats. -/
def ggdEntropyNats (beta alpha : ℝ) : ℝ :=
  Real.log (2 * alpha * Real.Gamma (1 / beta) / beta) + 1 / beta

/-- Closed form for differential entropy in bits. -/
def ggdEntropyBits (beta alpha : ℝ) : ℝ :=
  log2 (2 * alpha * Real.Gamma (1 / beta) / beta) + 1 / (beta * Real.log 2)

/-- Differential entropy of GGD in nats. -/
theorem ggd_entropy_nats
  {beta alpha : ℝ} (hbeta : 0 < beta) (halpha : 0 < alpha) :
  diffEntropyNats (ggdDensity beta alpha) = ggdEntropyNats beta alpha := by
  -- Expand the definition of entropy and normalize the density constant.
  unfold diffEntropyNats ggdEntropyNats ggdDensity ggdC
  set C : ℝ := beta / (2 * alpha * Real.Gamma (1 / beta)) with hC
  have hGammaPos : 0 < Real.Gamma (1 / beta) := by
    exact Real.Gamma_pos_of_pos (one_div_pos.mpr hbeta)
  have hdenpos : 0 < 2 * alpha * Real.Gamma (1 / beta) := by
    nlinarith [halpha, hGammaPos]
  have hCpos : 0 < C := by
    exact div_pos hbeta hdenpos
  have hCne : C ≠ 0 := ne_of_gt hCpos
  have hbeta0 : beta ≠ 0 := ne_of_gt hbeta
  have hGamma0 : Real.Gamma (1 / beta) ≠ 0 := ne_of_gt hGammaPos
  -- Log of the density: log C minus the power term.
  have hlog :
      ∀ x,
        Real.log (C * Real.exp (-(|x| / alpha) ^ beta)) =
          Real.log C - (|x| / alpha) ^ beta := by
    intro x
    have hExpPos : 0 < Real.exp (-(|x| / alpha) ^ beta) := by
      exact Real.exp_pos _
    calc
      Real.log (C * Real.exp (-(|x| / alpha) ^ beta)) =
          Real.log C + Real.log (Real.exp (-(|x| / alpha) ^ beta)) := by
            simpa using (Real.log_mul hCne (ne_of_gt hExpPos))
      _ = Real.log C - (|x| / alpha) ^ beta := by
            simp [sub_eq_add_neg]
  -- Density integrates to 1.
  have hI :
      (∫ x : ℝ, C * Real.exp (-(|x| / alpha) ^ beta)) = 1 := by
    simpa [ggdDensity, ggdC, hC] using (ggd_integral_eq_one hbeta halpha)
  -- Apply the absolute-moment formula with p = beta.
  have hMoment0 :
      (∫ x : ℝ, |x| ^ beta * (C * Real.exp (-(|x| / alpha) ^ beta))) =
        alpha ^ beta * Real.Gamma ((beta + 1) / beta) / Real.Gamma (1 / beta) := by
    simpa [ggdDensity, ggdC, hC] using
      (ggd_abs_moment_integral (beta := beta) (alpha := alpha) (p := beta)
        hbeta halpha (by linarith))
  -- Gamma recurrence at (1/beta)+1.
  have hGamma :
      Real.Gamma ((beta + 1) / beta) = (1 / beta) * Real.Gamma (1 / beta) := by
    have h1 : (beta + 1) / beta = (1 / beta) + 1 := by
      field_simp [hbeta0]
      ring
    calc
      Real.Gamma ((beta + 1) / beta)
          = Real.Gamma ((1 / beta) + 1) := by simpa [h1]
      _ = (1 / beta) * Real.Gamma (1 / beta) := by
            simpa [one_div] using
              (Real.Gamma_add_one (s := beta⁻¹) (inv_ne_zero hbeta0))
  -- Simplify the moment to alpha^beta / beta.
  have hMoment :
      (∫ x : ℝ, |x| ^ beta * (C * Real.exp (-(|x| / alpha) ^ beta))) =
        alpha ^ beta / beta := by
    calc
      (∫ x : ℝ, |x| ^ beta * (C * Real.exp (-(|x| / alpha) ^ beta)))
          = alpha ^ beta * Real.Gamma ((beta + 1) / beta) /
              Real.Gamma (1 / beta) := hMoment0
      _ = alpha ^ beta * ((1 / beta) * Real.Gamma (1 / beta)) /
            Real.Gamma (1 / beta) := by simp [hGamma]
      _ = alpha ^ beta / beta := by
            field_simp [hGamma0, hbeta0]
  -- Scale by alpha^beta to get E[(|X|/alpha)^beta] = 1/beta.
  have hMoment2 :
      (∫ x : ℝ, (C * Real.exp (-(|x| / alpha) ^ beta)) * (|x| / alpha) ^ beta) =
        1 / beta := by
    have hrew :
        (fun x : ℝ =>
          (C * Real.exp (-(|x| / alpha) ^ beta)) * (|x| / alpha) ^ beta) =
          fun x : ℝ =>
            (1 / alpha ^ beta) * (|x| ^ beta * (C * Real.exp (-(|x| / alpha) ^ beta))) := by
      funext x
      have hdiv :
          (|x| / alpha) ^ beta = |x| ^ beta / alpha ^ beta := by
        simpa using (Real.div_rpow (abs_nonneg x) (le_of_lt halpha) beta)
      calc
        (C * Real.exp (-(|x| / alpha) ^ beta)) * (|x| / alpha) ^ beta
            = (C * Real.exp (-(|x| / alpha) ^ beta)) * (|x| ^ beta / alpha ^ beta) := by
                simp [hdiv]
        _ = (C * Real.exp (-(|x| / alpha) ^ beta)) * (|x| ^ beta * (alpha ^ beta)⁻¹) := by
                simp [div_eq_mul_inv]
        _ = (alpha ^ beta)⁻¹ * (|x| ^ beta * (C * Real.exp (-(|x| / alpha) ^ beta))) := by
                ring
        _ = (1 / alpha ^ beta) * (|x| ^ beta * (C * Real.exp (-(|x| / alpha) ^ beta))) := by
                simp [one_div]
    have hαβ : alpha ^ beta ≠ 0 := by
      exact ne_of_gt (Real.rpow_pos_of_pos halpha _)
    calc
      (∫ x : ℝ, (C * Real.exp (-(|x| / alpha) ^ beta)) * (|x| / alpha) ^ beta)
          = ∫ x : ℝ,
              (1 / alpha ^ beta) *
                (|x| ^ beta * (C * Real.exp (-(|x| / alpha) ^ beta))) := by
                simp [hrew]
      _ = (1 / alpha ^ beta) *
            (∫ x : ℝ, |x| ^ beta * (C * Real.exp (-(|x| / alpha) ^ beta))) := by
            simp [MeasureTheory.integral_const_mul]
      _ = (1 / alpha ^ beta) * (alpha ^ beta / beta) := by
            simp [hMoment]
      _ = 1 / beta := by
            field_simp [hαβ, hbeta0]
  have hInt1 :
      Integrable (fun x : ℝ => (C * Real.exp (-(|x| / alpha) ^ beta)) * Real.log C) := by
    have hIntF : Integrable (fun x : ℝ => C * Real.exp (-(|x| / alpha) ^ beta)) := by
      have h := ggdDensity_integrable hbeta halpha
      refine h.congr ?_
      refine ae_of_all _ ?_
      intro x
      simp [ggdDensity, ggdC, hC]
    simpa [mul_comm] using hIntF.mul_const (Real.log C)
  have hInt2 :
      Integrable (fun x : ℝ => (C * Real.exp (-(|x| / alpha) ^ beta)) * (|x| / alpha) ^ beta) := by
    have hne : (1 / beta : ℝ) ≠ 0 := by
      exact one_div_ne_zero hbeta.ne'
    refine MeasureTheory.Integrable.of_integral_ne_zero ?_
    simpa [hMoment2] using hne
  have hIntEq :
      ∫ x : ℝ, (C * Real.exp (-(|x| / alpha) ^ beta)) *
          Real.log (C * Real.exp (-(|x| / alpha) ^ beta))
        = ∫ x : ℝ,
            (C * Real.exp (-(|x| / alpha) ^ beta)) *
              (Real.log C - (|x| / alpha) ^ beta) := by
    refine MeasureTheory.integral_congr_ae ?_
    refine MeasureTheory.ae_of_all _ ?_
    intro x
    simp [hlog]
  have hIntSub :
      ∫ x : ℝ,
          (C * Real.exp (-(|x| / alpha) ^ beta)) *
            (Real.log C - (|x| / alpha) ^ beta)
        =
          (∫ x : ℝ, (C * Real.exp (-(|x| / alpha) ^ beta)) * Real.log C)
            - (∫ x : ℝ, (C * Real.exp (-(|x| / alpha) ^ beta)) * (|x| / alpha) ^ beta) := by
    have hfun :
        (fun x : ℝ =>
          (C * Real.exp (-(|x| / alpha) ^ beta)) *
            (Real.log C - (|x| / alpha) ^ beta))
          =
          fun x : ℝ =>
            (C * Real.exp (-(|x| / alpha) ^ beta)) * Real.log C
              - (C * Real.exp (-(|x| / alpha) ^ beta)) * (|x| / alpha) ^ beta := by
      funext x
      ring
    simpa [hfun] using
      (MeasureTheory.integral_sub (μ := volume) hInt1 hInt2)
  have hLogCInt :
      ∫ x : ℝ, (C * Real.exp (-(|x| / alpha) ^ beta)) * Real.log C =
        (∫ x : ℝ, C * Real.exp (-(|x| / alpha) ^ beta)) * Real.log C := by
    simp [MeasureTheory.integral_mul_const]
  have hIntSubNeg :
      -∫ x : ℝ,
          (C * Real.exp (-(|x| / alpha) ^ beta)) *
            (Real.log C - (|x| / alpha) ^ beta)
        =
          (∫ x : ℝ, (C * Real.exp (-(|x| / alpha) ^ beta)) * (|x| / alpha) ^ beta)
            - (∫ x : ℝ, (C * Real.exp (-(|x| / alpha) ^ beta)) * Real.log C) := by
    calc
      -∫ x : ℝ,
          (C * Real.exp (-(|x| / alpha) ^ beta)) *
            (Real.log C - (|x| / alpha) ^ beta)
          = -(
              (∫ x : ℝ, (C * Real.exp (-(|x| / alpha) ^ beta)) * Real.log C)
              - (∫ x : ℝ, (C * Real.exp (-(|x| / alpha) ^ beta)) * (|x| / alpha) ^ beta)) := by
              simp [hIntSub]
      _ = (∫ x : ℝ, (C * Real.exp (-(|x| / alpha) ^ beta)) * (|x| / alpha) ^ beta)
            - (∫ x : ℝ, (C * Real.exp (-(|x| / alpha) ^ beta)) * Real.log C) := by
              ring
  have hMain :
      -∫ x : ℝ, (C * Real.exp (-(|x| / alpha) ^ beta)) *
          Real.log (C * Real.exp (-(|x| / alpha) ^ beta))
        = -Real.log C + 1 / beta := by
    calc
      -∫ x : ℝ, (C * Real.exp (-(|x| / alpha) ^ beta)) *
          Real.log (C * Real.exp (-(|x| / alpha) ^ beta))
          = -∫ x : ℝ,
              (C * Real.exp (-(|x| / alpha) ^ beta)) *
                (Real.log C - (|x| / alpha) ^ beta) := by
                simpa [hIntEq]
      _ =
          (∫ x : ℝ, (C * Real.exp (-(|x| / alpha) ^ beta)) * (|x| / alpha) ^ beta)
            - (∫ x : ℝ, (C * Real.exp (-(|x| / alpha) ^ beta)) * Real.log C) := by
              simpa [hIntSubNeg]
      _ = (1 / beta) - (∫ x : ℝ, C * Real.exp (-(|x| / alpha) ^ beta)) * Real.log C := by
            simp [hMoment2, hLogCInt]
      _ = -Real.log C + 1 / beta := by
            have hI' : (∫ x : ℝ, C * Real.exp (-(|x| / alpha) ^ beta)) = 1 := hI
            simp [hI', sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
              mul_assoc]
  have hlogC' :
      -Real.log C = Real.log (2 * alpha * Real.Gamma (1 / beta) / beta) := by
    -- Algebra on logs to rewrite the normalization constant in the final form.
    have hden : (2 * alpha * Real.Gamma (1 / beta)) ≠ 0 := ne_of_gt hdenpos
    have hlog1 :
        Real.log (beta / (2 * alpha * Real.Gamma (1 / beta))) =
          Real.log beta - Real.log (2 * alpha * Real.Gamma (1 / beta)) := by
      simpa using
        (Real.log_div (x := beta) (y := 2 * alpha * Real.Gamma (1 / beta)) hbeta0 hden)
    have hlog2 :
        Real.log (2 * alpha * Real.Gamma (1 / beta) / beta) =
          Real.log (2 * alpha * Real.Gamma (1 / beta)) - Real.log beta := by
      simpa using
        (Real.log_div (x := 2 * alpha * Real.Gamma (1 / beta)) (y := beta) hden hbeta0)
    nlinarith [hlog1, hlog2, hC]
  calc
    diffEntropyNats (fun x : ℝ => C * Real.exp (-(|x| / alpha) ^ beta))
        = -Real.log C + 1 / beta := hMain
    _ = Real.log (2 * alpha * Real.Gamma (1 / beta) / beta) + 1 / beta := by
          simp [hlogC']

/-- Differential entropy of GGD in bits. -/
theorem ggd_entropy_bits
  {beta alpha : ℝ} (hbeta : 0 < beta) (halpha : 0 < alpha) :
  diffEntropyBits (ggdDensity beta alpha) = ggdEntropyBits beta alpha := by
  -- Change of base: log2(x) = log(x) / log 2, then pull the constant outside the integral.
  have hconv :
      diffEntropyBits (ggdDensity beta alpha) =
        (1 / Real.log 2) * diffEntropyNats (ggdDensity beta alpha) := by
    unfold diffEntropyBits diffEntropyNats log2
    have hrew :
        (fun x : ℝ =>
          ggdDensity beta alpha x * (Real.log (ggdDensity beta alpha x) / Real.log 2)) =
          fun x : ℝ =>
            (1 / Real.log 2) * (ggdDensity beta alpha x * Real.log (ggdDensity beta alpha x)) := by
      funext x
      ring
    calc
      -∫ x : ℝ, ggdDensity beta alpha x *
          (Real.log (ggdDensity beta alpha x) / Real.log 2)
          = -∫ x : ℝ,
              (1 / Real.log 2) *
                (ggdDensity beta alpha x * Real.log (ggdDensity beta alpha x)) := by
                simp [hrew]
      _ = -(1 / Real.log 2) *
            ∫ x : ℝ, ggdDensity beta alpha x * Real.log (ggdDensity beta alpha x) := by
            simp [MeasureTheory.integral_const_mul]
      _ = (1 / Real.log 2) *
            (-∫ x : ℝ, ggdDensity beta alpha x * Real.log (ggdDensity beta alpha x)) := by
            ring
  calc
    diffEntropyBits (ggdDensity beta alpha)
        = (1 / Real.log 2) * diffEntropyNats (ggdDensity beta alpha) := hconv
    _ = (1 / Real.log 2) * ggdEntropyNats beta alpha := by
          simp [ggd_entropy_nats hbeta halpha]
    _ = ggdEntropyBits beta alpha := by
          unfold ggdEntropyNats ggdEntropyBits log2
          ring

end RateDistortion
