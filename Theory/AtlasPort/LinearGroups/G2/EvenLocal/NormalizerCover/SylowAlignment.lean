module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover
public import Theory.AtlasPort.LinearGroups.G2.SylowNormalizer
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Geometry
public import Theory.GroupTheory.SylowNormalizerOvergroupAlignment

/-!
# Simultaneous Sylow and two-subgroup normalizer coverage in G₂

The hexagon places a nonidentity two-subgroup normalizer in a conjugate root
parabolic. The positive-root Sylow normalizer is the Borel, contained in both
standard parabolics. Sylow conjugacy inside the selected parabolic therefore
puts the prescribed Sylow normalizer in the same proper subgroup. Properness
is witnessed by the other simple Weyl element moving the standard point or
plane in the actual octonion representation.

Source: the parabolic step of Aschbacher--Smith 15.3.43(e), printed p.1140.
The octonion and root calculations use the licensed ATLAS port
(`LICENSES/ATLAS.txt`, `LICENSES/ATLAS-CITATION.cff`).
-/

public section

namespace Atlas.G2.EvenLocal.NormalizerCover

open Subgroup LieParabolicSetup Explicit Atlas.SplitOctonion

variable {F : Type*} [Field F]

/-- The other simple Weyl element moves the standard null plane. -/
theorem short_parabolic_ne_top : parabolic₁ (F := F) ≠ ⊤ := by
  intro h
  have hr : (weylR : Model F) ∈ parabolic₁ := h.symm ▸ mem_top _
  have hp := (parabolic₁_le_shortPlaneStabilizer hr).1 (basisVector 1)
    (basis_mem_shortPlane 1 (by decide))
  have hz := hp (2 : Fin 8) (by decide)
  simp [weylR, weylREquiv, weylRLinear, weylRApply, basisVector] at hz

/-- The other simple Weyl element moves the standard singular point. -/
theorem long_parabolic_ne_top : parabolic₂ (F := F) ≠ ⊤ := by
  intro h
  have hs : (weylS : Model F) ∈ parabolic₂ := h.symm ▸ mem_top _
  change (weylS : Model F) ∈ parabolic at hs
  rw [parabolic_eq_pointStabilizer, mem_pointStabilizer_iff] at hs
  obtain ⟨a, ha⟩ := hs
  have hz := congrFun ha 1
  simp [weylS, weylSEquiv, weylSLinear, weylSApply, basisVector] at hz

/-- A Sylow subgroup normalizing a nonidentity two-subgroup has its full
normalizer in a common proper overgroup with that two-subgroup's normalizer. -/
theorem normalizer_sup_lt_top [Finite F] [CharP F 2]
    (P : Sylow 2 (Model F)) (R : Subgroup (Model F))
    (hR : R ≠ ⊥) (hp : IsPGroup 2 R)
    (hP : (P : Subgroup (Model F)) ≤ normalizer (R : Set (Model F))) :
    normalizer (P : Set (Model F)) ⊔ normalizer (R : Set (Model F)) < ⊤ := by
  obtain ⟨g, hg | hg⟩ := normalizer_conjugate_le_parabolic R hR hp
  · refine Sylow.normalizer_sup_lt_top_of_map_le sylow P _ parabolic₁
      (MulAut.conj g) hP hg ?_ (lt_top_iff_ne_top.mpr short_parabolic_ne_top)
    change normalizer (unipotent (K := F) : Set (Model F)) ≤ parabolic₁
    rw [SylowNormalizer.normalizer_unipotent]
    exact borel_le_parabolic₁
  · refine Sylow.normalizer_sup_lt_top_of_map_le sylow P _ parabolic₂
      (MulAut.conj g) hP hg ?_ (lt_top_iff_ne_top.mpr long_parabolic_ne_top)
    change normalizer (unipotent (K := F) : Set (Model F)) ≤ parabolic₂
    rw [SylowNormalizer.normalizer_unipotent]
    exact borel_le_parabolic₂

end Atlas.G2.EvenLocal.NormalizerCover
