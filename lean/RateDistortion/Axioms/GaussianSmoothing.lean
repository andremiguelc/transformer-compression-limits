import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Distributions.Gaussian.Real
import RateDistortion.Basic
import RateDistortion.Axioms.RateDistortion

open scoped BigOperators MeasureTheory
open MeasureTheory

noncomputable section
namespace RateDistortion

section GaussianSmoothing
/-- Measure associated to a (real-valued) density. -/
def densityMeasure (f : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (f x))

instance densityMeasure_sfinite (f : ℝ → ℝ) : SFinite (densityMeasure f) := by
  dsimp [densityMeasure]
  infer_instance

/-- Gaussian convolution at the measure level. -/
def gaussConvMeasure (f : ℝ → ℝ) (t : ℝ) : Measure ℝ :=
  densityMeasure f ∗ ProbabilityTheory.gaussianReal 0 (Real.toNNReal t)

/-- Gaussian convolution operator (via measure convolution + RN-derivative). -/
def gaussConv (f : ℝ → ℝ) (t : ℝ) : ℝ → ℝ :=
  if t = 0 then
    f
  else
    fun x =>
      ((gaussConvMeasure f t).rnDeriv volume x).toReal

/-- At t=0, Gaussian convolution is the identity. -/
theorem gaussConv_zero (f : ℝ → ℝ) : gaussConv f 0 = f := by
  simp [gaussConv]

/-- At t=0, Gaussian convolution measure is the original density measure. -/
theorem gaussConvMeasure_zero (f : ℝ → ℝ) : gaussConvMeasure f 0 = densityMeasure f := by
  simp [gaussConvMeasure, ProbabilityTheory.gaussianReal_zero_var]

/-- Additivity of Gaussian smoothing at the measure level for nonnegative times. -/
theorem gaussConvMeasure_add (f : ℝ → ℝ) {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) :
    gaussConvMeasure f (t + u) =
      gaussConvMeasure f t ∗ ProbabilityTheory.gaussianReal 0 (Real.toNNReal u) := by
  unfold gaussConvMeasure
  have hgauss :
      ProbabilityTheory.gaussianReal 0 (Real.toNNReal t) ∗
          ProbabilityTheory.gaussianReal 0 (Real.toNNReal u) =
        ProbabilityTheory.gaussianReal 0 (Real.toNNReal t + Real.toNNReal u) := by
    simpa using
      (ProbabilityTheory.gaussianReal_conv_gaussianReal
        (m₁ := 0) (m₂ := 0) (v₁ := Real.toNNReal t) (v₂ := Real.toNNReal u))
  calc
    densityMeasure f ∗ ProbabilityTheory.gaussianReal 0 (Real.toNNReal (t + u))
        =
        densityMeasure f ∗
          ProbabilityTheory.gaussianReal 0 (Real.toNNReal t + Real.toNNReal u) := by
          simp [Real.toNNReal_add ht hu]
    _ =
        densityMeasure f ∗
          (ProbabilityTheory.gaussianReal 0 (Real.toNNReal t) ∗
            ProbabilityTheory.gaussianReal 0 (Real.toNNReal u)) := by
          simp [hgauss]
    _ =
        (densityMeasure f ∗ ProbabilityTheory.gaussianReal 0 (Real.toNNReal t)) ∗
          ProbabilityTheory.gaussianReal 0 (Real.toNNReal u) := by
          simpa using
            (MeasureTheory.Measure.conv_assoc (densityMeasure f)
              (ProbabilityTheory.gaussianReal 0 (Real.toNNReal t))
              (ProbabilityTheory.gaussianReal 0 (Real.toNNReal u))).symm

/-- Fisher information functional for a density f. -/
axiom fisherInfo (f : ℝ → ℝ) : ℝ

/-- For densities with finite Fisher information, we can compute J via the score. -/
axiom fisherInfo_eq_of_hasFiniteFisherInfo (f : ℝ → ℝ) (hf : HasFiniteFisherInfo f) :
  fisherInfo f = ∫ x, (deriv (fun y => Real.log (f y)) x) ^ 2 * f x

/-- Fisher information is non-negative. -/
axiom fisherInfo_nonneg (f : ℝ → ℝ) : 0 ≤ fisherInfo f

/-- Fisher information of a Gaussian N(0, σ²) is 1/σ². -/
axiom fisherInfo_gaussian (sigma : ℝ) (hsigma : 0 < sigma) :
  fisherInfo (fun x => (1 / (sigma * Real.sqrt (2 * Real.pi))) *
    Real.exp (- x ^ 2 / (2 * sigma ^ 2))) = 1 / sigma ^ 2

/-- Fisher information scaling law: J(f_c) = (1/c²)·J(f), for f_c(x)=1/|c|·f(x/c). -/
axiom fisherInfo_scale (f : ℝ → ℝ) (c : ℝ) (hc : c ≠ 0) :
  fisherInfo (fun x => (1 / |c|) * f (x / c)) = (1 / c ^ 2) * fisherInfo f

/-- de Bruijn identity: ∂h(X_t)/∂t = (1/2)J(X_t). -/
axiom deBruijn (f : ℝ → ℝ) (t : ℝ) (ht : 0 < t) (hf : IsDensity f)
    (hfi : HasFiniteFisherInfo f) :
  deriv (fun s => diffEntropyNats (gaussConv f s)) t =
    (1 / 2) * fisherInfo (gaussConv f t)

/--
Integrated de Bruijn identity starting from t = 0 for regular densities.

Reference: standard de Bruijn identity; see Palomar–Verdú (2006) and related
information/estimation theory treatments for the Gaussian smoothing form.
-/
axiom deBruijn_integrated_from_zero (f : ℝ → ℝ) (D : ℝ) (hD : 0 < D)
    (hf : IsDensity f) (hfi : HasFiniteFisherInfo f) :
  diffEntropyNats (gaussConv f D) - diffEntropyNats f =
    (1 / 2) * ∫ s in (0:ℝ)..D, fisherInfo (gaussConv f s)

/-- Gaussian test channel rate in nats. -/
def gaussianTestChannelRate (f : ℝ → ℝ) (D : ℝ) : ℝ :=
  diffEntropyNats (gaussConv f D) - (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * D)

/--
The Gaussian test channel provides an upper bound on R(D) (nats).

Reference: standard rate–distortion theory (e.g. Cover–Thomas); see also
Gaussian test-channel achievability discussions in classical RD texts.
-/
axiom gaussianTestChannel_achievable (f : ℝ → ℝ) (D : ℝ) (hD : 0 < D)
    (hf : IsDensity f) :
  rateDistortionFunctionNats f D ≤ gaussianTestChannelRate f D

/-- Fisher information along Gaussian smoothing is interval-integrable on [0, D]. -/
axiom fisherInfo_gaussConv_intervalIntegrable (f : ℝ → ℝ) (D : ℝ)
    (hf : IsDensity f) (hfi : HasFiniteFisherInfo f) :
  IntervalIntegrable (fun s => fisherInfo (gaussConv f s)) volume (0:ℝ) D
end GaussianSmoothing

end RateDistortion
