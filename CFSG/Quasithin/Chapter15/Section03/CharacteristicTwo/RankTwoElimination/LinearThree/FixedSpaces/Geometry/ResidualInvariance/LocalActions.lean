module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.Basic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.Geometry
/-!
# The component Sylow intersection acts on the literal residuals

S ∩ L normalizes both residuals because it preserves Y and L. The definition
of the section centralizer then puts [Y_C,S ∩ L] in O₂(L). Its normality
inside Y_C puts it in O₂(Y_C), proving triviality on the cubic quotient.
No normalization of L by all of S is used.

Source: Aschbacher–Smith 15.3.23, printed p.1128 (combined manuscript,
1 March 2004), with the residual definitions from 15.3.12.
-/

public section
open Subgroup
open CFSG.Quasithin.Chapter15.Section03.RankTwo
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.ResidualInvariance
variable {G : Type*} [Group G] [Finite G]

private theorem normalizes_residual {H X : Subgroup G}
    (h : X ≤ normalizer (H : Set G)) :
    X ≤ normalizer (Stellmacher.twoResidualAmbient H : Set G) := by
  rw [ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
  exact h.trans (normalizer_le_normalizer_characteristic_image H (pResidual 2 H))

/-- The component Sylow intersection normalizes the intersection residual,
without any S-normalization assumption on the component. -/
theorem componentSylow_normalizes_YL (d : LocalData G) (L : Subgroup G) :
    d.S ⊓ L ≤ normalizer (YL d L : Set G) := by
  apply normalizes_residual
  exact (le_inf (inf_le_left.trans
    (planeStabilizer_normalizes_yplus d.action d.T d.sylow_le 1 d.choice))
    (inf_le_right.trans L.le_normalizer)).trans inf_normalizer_le_normalizer_inf

/-- The same local actor normalizes the genuine section-centralizer residual. -/
theorem componentSylow_normalizes_YC (d : LocalData G) (L : Subgroup G) :
    d.S ⊓ L ≤ normalizer (YC d L : Set G) := by
  have hLN : d.S ⊓ L ≤ normalizer (L : Set G) := inf_le_right.trans L.le_normalizer
  have hcore := normalizer_le_normalizer_characteristic_image L (pCore 2 L)
  have hsection : d.S ⊓ L ≤ normalizer (Chapter4.sectionCentralizer L : Set G) :=
    commutatorPreimage_normalized (normalizer (L : Set G)) L (L.pCoreIn 2) (d.S ⊓ L)
      hcore (hLN.trans (normalizer (L : Set G)).le_normalizer) hLN (hLN.trans hcore)
  apply normalizes_residual
  exact (le_inf (inf_le_left.trans
    (planeStabilizer_normalizes_yplus d.action d.T d.sylow_le 1 d.choice))
    hsection).trans inf_normalizer_le_normalizer_inf

/-- The component Sylow intersection acts trivially modulo O₂(Y_C).
This follows from the literal section-centralizer kernel, not an ordinary
centralizer identification. -/
theorem YC_componentSylow_commutator_le_core (d : LocalData G) (L : Subgroup G) :
    ⁅YC d L, d.S ⊓ L⁆ ≤ (YC d L).pCoreIn 2 := by
  have hc := (Chapter4.le_sectionCentralizer_iff (YC d L) L).mp
    ((ComponentIntersection.centralizerResidual_le d.Yplus L).trans inf_le_right)
  have htwo : IsPGroup 2 (⁅YC d L, d.S ⊓ L⁆ : Subgroup G) :=
    (L.isPGroup_pCoreIn 2).to_le ((commutator_mono le_rfl inf_le_right).trans hc.2)
  exact le_pCoreIn_of_normalizes htwo
    (le_normalizer_iff_commutator_le_left.mp (componentSylow_normalizes_YC d L))
    (normalizer_commutator_ge_left _ _)
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.ResidualInvariance

end
