import Mathlib
import RateDistortion.GGD.FisherInfo

noncomputable section
namespace RateDistortion

/-- Closed-form Fisher information for unit-variance GGD (as a function of β). -/
def Jclosed (beta : ℝ) : ℝ :=
  beta ^ 2 *
    (Real.Gamma (3 / beta) * Real.Gamma (2 - 1 / beta) /
      (Real.Gamma (1 / beta) ^ 2))

/--
Monotonicity of the closed-form Fisher information on β ∈ [1, 2].

This is the analytic spine (proved via digamma + integral representation in the writeup).
We keep it as an axiom for now to avoid re-formalizing the special-function calculus.
-/
axiom Jclosed_antitone :
  AntitoneOn Jclosed (Set.Icc (1:ℝ) 2)

/-- Value at β = 2 (Gaussian case). -/
lemma Jclosed_beta_two : Jclosed (2:ℝ) = 1 := by
  have hrec : Real.Gamma (3 / 2 : ℝ) = (2 : ℝ)⁻¹ * Real.Gamma (2 : ℝ)⁻¹ := by
    have h := Real.Gamma_add_one (s := (2 : ℝ)⁻¹) (by norm_num)
    -- h : Real.Gamma (2⁻¹ + 1) = 2⁻¹ * Real.Gamma 2⁻¹
    have h' : (2 : ℝ)⁻¹ + 1 = (3 / 2 : ℝ) := by
      norm_num
    simpa [h'] using h
  have hGamma_ne : Real.Gamma (2 : ℝ)⁻¹ ≠ 0 := by
    have hpos : 0 < Real.Gamma (2 : ℝ)⁻¹ := by
      exact Real.Gamma_pos_of_pos (by norm_num)
    exact ne_of_gt hpos
  have h1 : (2 : ℝ) - (2 : ℝ)⁻¹ = (3 / 2 : ℝ) := by
    norm_num
  have h4 : (2 : ℝ) ^ 2 = 4 := by
    norm_num
  calc
    Jclosed (2 : ℝ) =
        (2 : ℝ) ^ 2 *
          (Real.Gamma (3 / 2) * Real.Gamma (3 / 2) /
            (Real.Gamma (2 : ℝ)⁻¹ ^ 2)) := by
      simp [Jclosed, h1, one_div]
    _ =
        4 *
          (Real.Gamma (3 / 2) * Real.Gamma (3 / 2) /
            (Real.Gamma (2 : ℝ)⁻¹ ^ 2)) := by
      simp [h4]
    _ =
        4 *
          (((2 : ℝ)⁻¹ * Real.Gamma (2 : ℝ)⁻¹) * ((2 : ℝ)⁻¹ * Real.Gamma (2 : ℝ)⁻¹) /
            (Real.Gamma (2 : ℝ)⁻¹ ^ 2)) := by
      simp [hrec]
    _ = 1 := by
      field_simp [hGamma_ne]
      ring

lemma ggdFisherUnitVarClosed_beta_two : Jclosed 2 = 1 := by
  simpa using Jclosed_beta_two

lemma ggdFisher_unitVar_lower_bound {beta : ℝ} (hbeta1 : 1 < beta) (hbeta2 : beta ≤ 2) :
  1 ≤ ggdFisherInfo beta (alphaUnitVar beta) := by
  have hbeta1' : (1:ℝ) ≤ beta := by linarith
  have hmem : beta ∈ Set.Icc (1:ℝ) 2 := ⟨hbeta1', hbeta2⟩
  have hmem2 : (2:ℝ) ∈ Set.Icc (1:ℝ) 2 := by
    exact ⟨by norm_num, by norm_num⟩
  have hle : Jclosed 2 ≤ Jclosed beta :=
    Jclosed_antitone hmem hmem2 hbeta2
  calc
    1 = Jclosed 2 := by
      simpa using ggdFisherUnitVarClosed_beta_two.symm
    _ ≤ Jclosed beta := hle
    _ = ggdFisherInfo beta (alphaUnitVar beta) := by
      simpa [Jclosed] using
        (ggd_fisher_info_unitVar (beta := beta) hbeta1).symm

end RateDistortion
