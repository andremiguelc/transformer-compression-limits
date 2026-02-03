import Mathlib
import RateDistortion.Basic
import RateDistortion.GGD.Basic

noncomputable section
namespace RateDistortion

/-- Log-concavity for beta >= 1. -/
theorem ggd_logconcave
  {beta alpha : ℝ} (hbeta : 1 ≤ beta) (halpha : 0 < alpha) :
  IsLogConcave (ggdDensity beta alpha) := by
  intro x y t ⟨ht_ge, ht_le⟩
  unfold ggdDensity ggdC
  have hbeta_pos : 0 < beta := lt_of_lt_of_le (by norm_num) hbeta
  have hGammaPos : 0 < Real.Gamma (1 / beta) := by
    exact Real.Gamma_pos_of_pos (one_div_pos.mpr hbeta_pos)
  have hdenpos : 0 < 2 * alpha * Real.Gamma (1 / beta) := by
    nlinarith [halpha, hGammaPos]
  have hCpos : 0 < beta / (2 * alpha * Real.Gamma (1 / beta)) := by
    exact div_pos hbeta_pos hdenpos
  have hCne : beta / (2 * alpha * Real.Gamma (1 / beta)) ≠ 0 := ne_of_gt hCpos
  -- The log of the density is: log(C) - (|x|/α)^β
  -- For β ≥ 1, |x|^β is convex, so -(|x|/α)^β is concave
  -- This makes log f concave, i.e., f is log-concave
  --
  -- We need to show:
  -- f(tx + (1-t)y) ≥ exp(t·log f(x) + (1-t)·log f(y))
  --                = f(x)^t · f(y)^(1-t)
  --
  -- Taking logs:
  -- log f(tx + (1-t)y) ≥ t·log f(x) + (1-t)·log f(y)
  --
  -- Expanding:
  -- log C - (|tx + (1-t)y|/α)^β ≥ t·(log C - (|x|/α)^β) + (1-t)·(log C - (|y|/α)^β)
  --
  -- Simplifying (log C terms cancel):
  -- -(|tx + (1-t)y|/α)^β ≥ -t·(|x|/α)^β - (1-t)·(|y|/α)^β
  --
  -- Equivalently:
  -- (|tx + (1-t)y|/α)^β ≤ t·(|x|/α)^β + (1-t)·(|y|/α)^β
  --
  -- This follows from:
  -- 1. Triangle inequality: |tx + (1-t)y| ≤ t|x| + (1-t)|y|
  -- 2. For β ≥ 1, z^β is convex (and monotone increasing on [0,∞))
  have ht1 : 0 ≤ 1 - t := by linarith
  have h1 : |t * x + (1 - t) * y| ≤ t * |x| + (1 - t) * |y| := by
    calc
      |t * x + (1 - t) * y|
          ≤ |t * x| + |(1 - t) * y| := by
              simpa using abs_add_le (t * x) ((1 - t) * y)
      _ = t * |x| + (1 - t) * |y| := by
            simp [abs_mul, abs_of_nonneg ht_ge, abs_of_nonneg ht1]
  have h2 :
      (t * |x| + (1 - t) * |y|) ^ beta ≤
        t * (|x| ^ beta) + (1 - t) * (|y| ^ beta) := by
    -- Convexity of z ↦ z^β on [0, ∞) for β ≥ 1.
    -- Use ConvexOn + Jensen (or pow convexity lemma in Mathlib).
    have hconv := convexOn_rpow (p := beta) hbeta
    have hx0 : |x| ∈ Set.Ici (0:ℝ) := by simp
    have hy0 : |y| ∈ Set.Ici (0:ℝ) := by simp
    have hsum : t + (1 - t) = 1 := by ring
    have hconv' := hconv.2 hx0 hy0 ht_ge ht1 hsum
    -- rewrite scalar multiplication
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hconv'
  -- Now we chain the inequalities to prove log-concavity.
  -- The goal is: (|tx + (1-t)y|/α)^β ≤ t·(|x|/α)^β + (1-t)·(|y|/α)^β
  -- We proceed in three steps:
  -- Step A: Scale the triangle inequality by 1/α
  have hdiv :
      |t * x + (1 - t) * y| / alpha ≤
        t * (|x| / alpha) + (1 - t) * (|y| / alpha) := by
    have h1' := (div_le_div_of_nonneg_right h1 (le_of_lt halpha))
    -- linearity of division by alpha
    simpa [div_eq_mul_inv, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using h1'
  -- Step B: Apply monotonicity of z ↦ z^β on [0,∞) to lift the inequality to powers
  have hpow1 :
      (|t * x + (1 - t) * y| / alpha) ^ beta ≤
        (t * (|x| / alpha) + (1 - t) * (|y| / alpha)) ^ beta := by
    have hnonneg : 0 ≤ |t * x + (1 - t) * y| / alpha := by
      exact div_nonneg (abs_nonneg _) (le_of_lt halpha)
    have hbeta0 : 0 ≤ beta := by linarith
    exact Real.rpow_le_rpow hnonneg hdiv hbeta0
  -- Step C: Apply convexity of z ↦ z^β (for β ≥ 1) to get the Jensen-type inequality:
  -- (t·a + (1-t)·b)^β ≤ t·a^β + (1-t)·b^β
  have hconv2 :
      (t * (|x| / alpha) + (1 - t) * (|y| / alpha)) ^ beta ≤
        t * (|x| / alpha) ^ beta + (1 - t) * (|y| / alpha) ^ beta := by
    -- Convexity of z ↦ z^β on [0, ∞) for β ≥ 1 (from Mathlib's convexOn_rpow)
    have hconv := convexOn_rpow (p := beta) hbeta
    have hx0 : |x| / alpha ∈ Set.Ici (0:ℝ) := by
      have : 0 ≤ |x| / alpha := div_nonneg (abs_nonneg _) (le_of_lt halpha)
      simpa using this
    have hy0 : |y| / alpha ∈ Set.Ici (0:ℝ) := by
      have : 0 ≤ |y| / alpha := div_nonneg (abs_nonneg _) (le_of_lt halpha)
      simpa using this
    have hsum : t + (1 - t) = 1 := by ring
    have hconv' := hconv.2 hx0 hy0 ht_ge ht1 hsum
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hconv'
  -- Combine steps B and C by transitivity: this is the key convexity bound
  have hA :
      (|t * x + (1 - t) * y| / alpha) ^ beta ≤
        t * (|x| / alpha) ^ beta + (1 - t) * (|y| / alpha) ^ beta :=
    le_trans hpow1 hconv2
  have hlog :
      ∀ z : ℝ,
        Real.log (beta / (2 * alpha * Real.Gamma (1 / beta)) *
          Real.exp (-(|z| / alpha) ^ beta)) =
          Real.log (beta / (2 * alpha * Real.Gamma (1 / beta))) - (|z| / alpha) ^ beta := by
    intro z
    have hExpPos : 0 < Real.exp (-(|z| / alpha) ^ beta) := by
      exact Real.exp_pos _
    calc
      Real.log (beta / (2 * alpha * Real.Gamma (1 / beta)) *
          Real.exp (-(|z| / alpha) ^ beta)) =
          Real.log (beta / (2 * alpha * Real.Gamma (1 / beta))) +
            Real.log (Real.exp (-(|z| / alpha) ^ beta)) := by
            simpa using (Real.log_mul hCne (ne_of_gt hExpPos))
      _ = Real.log (beta / (2 * alpha * Real.Gamma (1 / beta))) - (|z| / alpha) ^ beta := by
            simp [sub_eq_add_neg]
  have hlog' :
      ∀ z : ℝ,
        Real.log (beta / (2 * alpha * Real.Gamma beta⁻¹) *
          Real.exp (-(|z| / alpha) ^ beta)) =
          Real.log (beta / (2 * alpha * Real.Gamma beta⁻¹)) - (|z| / alpha) ^ beta := by
    simpa [one_div] using hlog
  have hRHS :
      Real.exp (t * Real.log (ggdDensity beta alpha x) + (1 - t) * Real.log (ggdDensity beta alpha y)) =
        (beta / (2 * alpha * Real.Gamma (1 / beta))) *
          Real.exp (-(t * (|x| / alpha) ^ beta + (1 - t) * (|y| / alpha) ^ beta)) := by
    have hlin :
        t * (Real.log (beta / (2 * alpha * Real.Gamma (1 / beta))) - (|x| / alpha) ^ beta) +
            (1 - t) * (Real.log (beta / (2 * alpha * Real.Gamma (1 / beta))) - (|y| / alpha) ^ beta)
          =
          Real.log (beta / (2 * alpha * Real.Gamma (1 / beta))) -
            (t * (|x| / alpha) ^ beta + (1 - t) * (|y| / alpha) ^ beta) := by
      ring
    have hlin' :
        t * (Real.log (beta / (2 * alpha * Real.Gamma beta⁻¹)) - (|x| / alpha) ^ beta) +
            (1 - t) * (Real.log (beta / (2 * alpha * Real.Gamma beta⁻¹)) - (|y| / alpha) ^ beta)
          =
          Real.log (beta / (2 * alpha * Real.Gamma beta⁻¹)) -
            (t * (|x| / alpha) ^ beta + (1 - t) * (|y| / alpha) ^ beta) := by
      simpa [one_div] using hlin
    calc
      Real.exp (t * Real.log (ggdDensity beta alpha x) + (1 - t) * Real.log (ggdDensity beta alpha y))
          = Real.exp (t * (Real.log (beta / (2 * alpha * Real.Gamma (1 / beta))) - (|x| / alpha) ^ beta) +
              (1 - t) * (Real.log (beta / (2 * alpha * Real.Gamma (1 / beta))) - (|y| / alpha) ^ beta)) := by
                simp [ggdDensity, ggdC, hlog']
      _ = Real.exp (Real.log (beta / (2 * alpha * Real.Gamma (1 / beta))) -
              (t * (|x| / alpha) ^ beta + (1 - t) * (|y| / alpha) ^ beta)) := by
                simpa [hlin']
      _ = Real.exp (Real.log (beta / (2 * alpha * Real.Gamma (1 / beta)))) *
            Real.exp (-(t * (|x| / alpha) ^ beta + (1 - t) * (|y| / alpha) ^ beta)) := by
              simp [sub_eq_add_neg, Real.exp_add]
      _ = (beta / (2 * alpha * Real.Gamma (1 / beta))) *
            Real.exp (-(t * (|x| / alpha) ^ beta + (1 - t) * (|y| / alpha) ^ beta)) := by
              have hCpos' : 0 < beta / (2 * alpha * Real.Gamma beta⁻¹) := by
                simpa [one_div] using hCpos
              simp [Real.exp_log hCpos']
  have hExp :
      Real.exp (-(t * (|x| / alpha) ^ beta + (1 - t) * (|y| / alpha) ^ beta)) ≤
        Real.exp (-(|t * x + (1 - t) * y| / alpha) ^ beta) := by
    have : -(t * (|x| / alpha) ^ beta + (1 - t) * (|y| / alpha) ^ beta) ≤
        -(|t * x + (1 - t) * y| / alpha) ^ beta := by
      exact neg_le_neg hA
    exact Real.exp_le_exp.mpr this
  have hCnonneg : 0 ≤ beta / (2 * alpha * Real.Gamma (1 / beta)) := le_of_lt hCpos
  have hmul :
      (beta / (2 * alpha * Real.Gamma (1 / beta))) *
          Real.exp (-(t * (|x| / alpha) ^ beta + (1 - t) * (|y| / alpha) ^ beta)) ≤
        (beta / (2 * alpha * Real.Gamma (1 / beta))) *
          Real.exp (-(|t * x + (1 - t) * y| / alpha) ^ beta) := by
    exact mul_le_mul_of_nonneg_left hExp hCnonneg
  -- conclude
  have hfinal :
      Real.exp (t * Real.log (ggdDensity beta alpha x) + (1 - t) * Real.log (ggdDensity beta alpha y)) ≤
        (beta / (2 * alpha * Real.Gamma (1 / beta))) *
          Real.exp (-(|t * x + (1 - t) * y| / alpha) ^ beta) := by
    simpa [hRHS] using hmul
  -- rewrite the left-hand side into `ggdDensity` and conclude
  simpa [ggdDensity, ggdC] using hfinal

end RateDistortion
