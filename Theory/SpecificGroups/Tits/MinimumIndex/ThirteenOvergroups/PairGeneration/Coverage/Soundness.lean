module

public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.Coverage.Data

/-!
# Soundness of the compressed normalizer-coverage tests

The finite tests use the already certified base at points 0, 1, 2, and their
normalizing factors are the actual elements proved in `Normalizer`. Thus a
successful test supplies an equality in the fixed ATLAS group.

Source: the ATLAS generators and the ambient Schreier-chain base certificate.
-/

namespace Tits.MinimumIndexThirteen.PairGeneration.CoverageCertificate
open Atlas1600OrderCertificate Theory.GroupTheory

public theorem fastStabilizerRep_eq (j : Fin 144) :
    fastStabilizerRep j = (stabilizerRep j).val := (chainWord_val _).symm

public theorem baseTest_sound {x y : Atlas1600Group}
    (h : baseTest x.val y.val = true) : x = y := by
  simp only [baseTest, Bool.and_eq_true, beq_iff_eq] at h
  exact ConverseLocalCoverage.DoubleCosetCertificate.threePoint_ext h.1.1 h.1.2 h.2

public theorem pointTest_sound (p : Fin 1600) (h : pointTest p = true) :
    (normalWord (pointNormal p)).val ((orbitRep (pointOrbit p)).val 0) = p := by
  simpa only [pointTest, beq_iff_eq, fastNormalWord_eq, fastWord_eq, orbitRep] using h

public theorem transitionTest_sound (i : Fin 6) (j : Fin 144)
    (h : transitionTest i j = true) :
    chainGenerator i * stabilizerRep j =
      stabilizerRep (transitionRep i j) * normalWord (transitionNormal i j) := by
  apply baseTest_sound
  change baseTest ((chainGenerator i).val * (stabilizerRep j).val)
    ((stabilizerRep (transitionRep i j)).val * (normalWord (transitionNormal i j)).val) = true
  change baseTest (L1Gen i * _) (_ * _) = true
  rw [← fastStabilizerRep_eq, ← fastStabilizerRep_eq, ← fastNormalWord_eq]
  exact h

public theorem factorTest_sound (i : Fin 32) (j : Fin 144)
    (h : factorTest i j = true) :
    orbitRep i * stabilizerRep j = normalWord (factorLeft i j) *
      representative (factorRep i j) * normalWord (factorRight i j) := by
  apply baseTest_sound
  change baseTest ((standardWord (orbitCode i)).val * (stabilizerRep j).val)
    ((normalWord (factorLeft i j)).val * (standardWord (representativeCode (factorRep i j))).val *
      (normalWord (factorRight i j)).val) = true
  rw [← fastWord_eq, ← fastStabilizerRep_eq, ← fastWord_eq,
    ← fastNormalWord_eq, ← fastNormalWord_eq]
  exact h

end Tits.MinimumIndexThirteen.PairGeneration.CoverageCertificate
