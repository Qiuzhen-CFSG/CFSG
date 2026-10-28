module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.ContainedCoreModels.G2Dual.NormPairing
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.ContainedCoreModels.CoverDuality
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.BlockModels.G2
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.BlockModels.Marking
public import Theory.Representation.FirstCohomologyG2Natural.BinaryGeneration

/-!
# G₂ contragredient detection and generation of full covering modules

The natural coefficients are the actual trace-zero octonion quotient for
G₂(2)′. The descended polar norm form gives an equivariant self-duality.
Transporting the checked cocycle tests through its inverse proves detection
for the contragredient on O^{3′} of the prescribed null-plane stabilizer.
The concrete binary pair-generation theorem discharges the sole generation
premise of those tests.

Consequently that same marked residual generates every perfect central
cover of the natural module, including its entire central kernel. This is
the coefficient calculation used for the G₂-block branch of
Aschbacher–Smith 15.3.31, printed p.1132 (PDF p.1149), via I.1.5–6 and
C.1.30. Transport to the original short-block core belongs to the source
assembly; the actor and subgroup here retain their literal octonion marking.
-/

public section

open Representation Representation.OneCohomology
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
open CentralCover
namespace ContainedCoreModels.G2
open BlockModels.G2

/-- Norm self-duality restricted to the actual commutator subgroup G₂(2)′. -/
noncomputable def selfDuality : action.Equiv action.dual :=
  Representation.Equiv.mk (Atlas.G2.Natural.quotientNormDualEquiv (ZMod 2)) (by
    intro g
    apply LinearMap.ext
    intro v
    exact Atlas.G2.Natural.quotientNormDualEquiv_equivariant (ZMod 2) g.val v)

/-- The marked O^{3′} residual detects all contragredient-valued cocycles. -/
theorem dual_detected_on_markedPlane_residual :
    DetectedOn action.dual
      ((Subgroup.primeToResidual 3 (BlockModels.planeStabilizer action markedPlane)).map
        (BlockModels.planeStabilizer action markedPlane).subtype) := by
  apply detectedOn_transport action.dual action (MulEquiv.refl Actor)
    selfDuality.symm.toLinearEquiv
    (fun a v => Representation.IntertwiningMap.isIntertwining _ _
      selfDuality.symm.toIntertwiningMap a v)
  change DetectedOn action ((_ : Subgroup Actor).map (MonoidHom.id Actor))
  rw [Subgroup.map_id]
  exact BlockModels.G2.detectedOn_markedPlane_residual
    (Atlas.G2.Natural.binary_pair_generates (ZMod 2) (by simp))

/-- The marked residual generates every full central cover, retaining its kernel. -/
theorem cover_coinvariants
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    {σ : Representation (ZMod 2) Actor U}
    (p : σ.IntertwiningMap action) (hp : IsCover p) :
    Coinvariants.ker (σ.comp
      ((Subgroup.primeToResidual 3 (BlockModels.planeStabilizer action markedPlane)).map
        (BlockModels.planeStabilizer action markedPlane).subtype).subtype) = ⊤ :=
  cover_coinvariants_of_detected_dual p hp _ dual_detected_on_markedPlane_residual

end ContainedCoreModels.G2
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
