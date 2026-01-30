import Mathlib
import RateDistortion.GGD.FisherInfo
import RateDistortion.Axioms.GaussianSmoothing

noncomputable section
namespace RateDistortion

section GGD
/-- GGD Fisher info matches the abstract Fisher info. -/
axiom ggdFisherInfo_eq_fisherInfo {beta alpha : ℝ} (hbeta : 0 < beta) (halpha : 0 < alpha) :
  ggdFisherInfo beta alpha = fisherInfo (ggdDensity beta alpha)
end GGD

end RateDistortion
