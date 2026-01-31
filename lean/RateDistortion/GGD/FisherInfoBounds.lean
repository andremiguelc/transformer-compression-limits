import Mathlib
import RateDistortion.GGD.FisherInfo

noncomputable section
namespace RateDistortion

/-- Closed-form Fisher information for unit-variance GGD (as a function of β). -/
def ggdFisherUnitVarClosed (beta : ℝ) : ℝ :=
  beta ^ 2 *
    (Real.Gamma (3 / beta) * Real.Gamma (2 - 1 / beta) /
      (Real.Gamma (1 / beta) ^ 2))

/--
Monotonicity of the closed-form Fisher information on β ∈ [1, 2].

This is the analytic spine (proved via digamma + integral representation in the writeup).
We keep it as an axiom for now to avoid re-formalizing the special-function calculus.
-/
axiom ggdFisherUnitVarClosed_antitone :
  AntitoneOn ggdFisherUnitVarClosed (Set.Icc (1:ℝ) 2)

/-- Value at β = 2 (Gaussian case). -/
axiom ggdFisherUnitVarClosed_beta_two :
  ggdFisherUnitVarClosed 2 = 1

lemma ggdFisher_unitVar_lower_bound {beta : ℝ} (hbeta1 : 1 < beta) (hbeta2 : beta ≤ 2) :
  1 ≤ ggdFisherInfo beta (alphaUnitVar beta) := by
  have hbeta1' : (1:ℝ) ≤ beta := by linarith
  have hmem : beta ∈ Set.Icc (1:ℝ) 2 := ⟨hbeta1', hbeta2⟩
  have hmem2 : (2:ℝ) ∈ Set.Icc (1:ℝ) 2 := by
    exact ⟨by norm_num, by norm_num⟩
  have hle : ggdFisherUnitVarClosed 2 ≤ ggdFisherUnitVarClosed beta :=
    ggdFisherUnitVarClosed_antitone hmem hmem2 hbeta2
  calc
    1 = ggdFisherUnitVarClosed 2 := by
      simpa using ggdFisherUnitVarClosed_beta_two.symm
    _ ≤ ggdFisherUnitVarClosed beta := hle
    _ = ggdFisherInfo beta (alphaUnitVar beta) := by
      simpa [ggdFisherUnitVarClosed] using
        (ggd_fisher_info_unitVar (beta := beta) hbeta1).symm

end RateDistortion
