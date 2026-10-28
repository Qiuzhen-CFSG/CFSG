module
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original

/-!
# The two original normal-component clauses

The genuine two-core quotient of the selected C-component is its actual
image in H/O₂(H). Normality and H=KT make this image the whole component
layer. The minimal-parabolic core identity therefore identifies the
original J image with its center; this is not an identity in H/J.
Normality also turns the generating join into the literal set product KT.

Source: Aschbacher–Smith E.2.2(2), printed pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Structure
variable {H : Type*} [Group H] [Finite H]

/-- The exact product and center identities for the original normal source component. -/
theorem source_original_normal_clauses
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    (Set.univ : Set H) = (K : Set H) * (T : Set H) ∧
      (ChapterB.minimalParabolicCore T hP).map (QuotientGroup.mk' (pCore 2 H)) =
        (center (K.map (QuotientGroup.mk' (pCore 2 H)))).map
          (K.map (QuotientGroup.mk' (pCore 2 H))).subtype := by
  refine ⟨?_,?_⟩
  · ext x
    constructor
    · intro _
      have hx : x ∈ K ⊔ (T : Subgroup H) := hgen ▸ mem_top x
      obtain ⟨k,hk,t,ht,rfl⟩ := mem_sup_of_normal_left.mp hx
      exact Set.mem_mul.mpr ⟨k,hk,t,ht,rfl⟩
    · intro _
      exact Set.mem_univ x
  · let N := pCore 2 H
    let q := QuotientGroup.mk' N
    have hq := QuotientGroup.mk'_surjective N
    let S := T.mapSurjective hq
    have hk : q.ker ≤ (T : Subgroup H) := by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup.le_sylow_of_normal T
    have hPs := ChapterB.minimalParabolic_surjective T hP q hq hk
    let : Group.IsNilpotent N := (pCore_isPGroup (p := 2) (G := H)).isNilpotent
    have hsX : ¬ Group.IsSolvable (H ⧸ N) := fun hx =>
      hs ((Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance,hx⟩)
    let := hqK
    have hd : IsComponent (H ⧸ N) (K.map q) :=
      ⟨hK.subnormal.map hq,IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK)⟩
    have hgs : K.map q ⊔ (S : Subgroup (H ⧸ N)) = ⊤ := by
      change K.map q ⊔ (T : Subgroup H).map q = ⊤
      rw [← Subgroup.map_sup,hgen,map_top_of_surjective q hq]
    exact (ChapterB.minimalParabolicCore_map T hP q hq hk).trans
      (core_eq_normal_component_center S hPs hsX (pCore_quotient_pCore_eq_bot 2) hd hgs)
end CFSG.Quasithin.ChapterE.Structure
