module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.RepresentativeEnvelope
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter

/-!
# The actual two-core in a representative component envelope

The ambient two-core centralizes the ordinary containing component and hence
L. It therefore normalizes the marked central plane, placing it in I. The
known centralizer of L in I bounds the two-core by that plane. Equality already
forces the whole representative centralizer into I by normality of its core.

Source: Aschbacher–Smith 15.3.38, printed p.1136.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry
variable {G : Type*} [Group G] [Finite G]

/-- An ordinary component envelope bounds the actual ambient two-core. -/
theorem twoCore_le_plane_of_component_envelope (I L V H : Subgroup G)
    (hI : I = normalizer (V : Set G))
    (hC : I ⊓ centralizer (L : Set G) = V) (hVL : V ≤ L)
    (K : Subgroup H) (hK : IsComponent H K) (hLK : L ≤ K.map H.subtype) :
    H.pCoreIn 2 ≤ V := by
  let := pCore_isNilpotent (p := 2) (G := H)
  have hc : pCore 2 H ≤ centralizer (K : Set H) :=
    le_centralizer_iff.mp (hK.le_centralizer_of_solvable_normal (pCore 2 H))
  have hcoreC : H.pCoreIn 2 ≤ centralizer (L : Set G) := by
    rintro _ ⟨a, ha, rfl⟩ l hl
    obtain ⟨k, hk, rfl⟩ := hLK hl
    exact congrArg Subtype.val (hc ha k hk)
  have hcoreI : H.pCoreIn 2 ≤ I := by
    rw [hI]
    exact hcoreC.trans ((centralizer_le hVL).trans (Subgroup.centralizer_le_normalizer _))
  rw [← hC]
  exact le_inf hcoreI hcoreC

omit [Finite G] in
/-- When the full marked plane is the two-core, its normalizer already
contains the actual representative centralizer. -/
theorem representative_le_of_core_plane (I V H : Subgroup G)
    (hI : I = normalizer (V : Set G)) (hcore : H.pCoreIn 2 = V) : H ≤ I := by
  rw [hI, ← hcore]
  exact H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry
end
