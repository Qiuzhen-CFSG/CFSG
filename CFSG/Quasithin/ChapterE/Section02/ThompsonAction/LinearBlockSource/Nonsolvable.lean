module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.LinearBlockSource.Source
public import Theory.GroupTheory.SolvableRadical.Transport
/-!
# Removing the alternating-three block in a nonsolvable group

A solvable subnormal subgroup lies in the solvable radical. Consequently,
if it generates the group together with a Sylow two-subgroup, the whole group
is solvable. This excludes the alternating-three factor from the χ₀ source
conclusion whenever the original group is nonsolvable.

Source: the nonsolvable case of Aschbacher--Smith E.2.3(4), pp.216--217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ThompsonAction.LinearBlockSource
open ChapterB ChapterC
variable {G : Type*} [Group G] [Finite G]

theorem solvable_of_subnormal_solvable_sylow_generation
    (L : Subgroup G) (hL : L.IsSubnormal) [Group.IsSolvable L]
    (T : Sylow 2 G) (hgen : L ⊔ (T : Subgroup G) = ⊤) : Group.IsSolvable G := by
  let R := solvableRadical G
  have hLR : L ≤ R := by
    have hr : solvableRadical L = ⊤ := top_unique (le_solvableRadical ⊤ inferInstance inferInstance)
    have hh := map_solvableRadical_subtype_le_of_isSubnormal hL
    simpa only [hr,←MonoidHom.range_eq_map,range_subtype] using hh
  have hRT : R ⊔ (T : Subgroup G) = ⊤ := top_unique
    (hgen.symm.le.trans (sup_le_sup_right hLR _))
  let q := QuotientGroup.mk' R
  let f := q.comp (T : Subgroup G).subtype
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective R x
    have hg : g ∈ R ⊔ (T : Subgroup G) := hRT.symm ▸ mem_top g
    obtain ⟨r,hr,t,ht,he⟩ := mem_sup_of_normal_left.mp hg
    refine ⟨⟨t,ht⟩,?_⟩
    have hqr : q r = 1 := (QuotientGroup.eq_one_iff _).mpr hr
    change q t = q g
    rw [←he,map_mul,hqr,one_mul]
  let : Group.IsNilpotent T := T.isPGroup'.isNilpotent
  let : Group.IsSolvable (G ⧸ R) := Group.isSolvable_of_surjective hf
  exact (Group.isSolvable_iff_subgroup_quotient R).mpr ⟨inferInstance,inferInstance⟩

theorem not_alternatingThree_of_nonsolvable_generation
    (hs : ¬Group.IsSolvable G) (L : Subgroup G) (hL : IsBlock L)
    (T : Sylow 2 G) (hgen : L ⊔ (T : Subgroup G) = ⊤) : ¬IsAlternatingBlock L 3 := by
  intro ha
  obtain ⟨e⟩ := ha.2.2.quotient_iso
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable (L ⧸ pCore 2 L) := Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Group.IsNilpotent (pCore 2 L) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable L := (Group.isSolvable_iff_subgroup_quotient (pCore 2 L)).mpr ⟨inferInstance,inferInstance⟩
  exact hs (solvable_of_subnormal_solvable_sylow_generation L hL.subnormal T hgen)

theorem strict_block_of_baumann_sylow
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hf : generalizedFitting G = pCore 2 G) (hs : ¬Group.IsSolvable G)
    (hno : ∀ C : Subgroup (baumann (T : Subgroup G)), C.Characteristic →
      (C.map (baumann (T : Subgroup G)).subtype).Normal → C = ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G)) (residualBaumannJoin T)) :
    ∃ L : Subgroup G, IsBlock L ∧ ((∃ n, IsL2EvenBlock L n) ∨ IsAlternatingBlock L 5) ∧
      L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      L ⊔ (T : Subgroup G) = ⊤ ∧ ¬L ≤ minimalParabolicMax T hP := by
  obtain ⟨L,hL,hm,hgen,hout⟩ := chiZero_block_of_baumann_sylow hG T hP hf hno hSyl
  refine ⟨L,hL.1,?_,hm,hgen,hout⟩
  rcases hL.2 with hl | h3 | h5
  · exact Or.inl hl
  · exact (not_alternatingThree_of_nonsolvable_generation hs L hL.1 T hgen h3).elim
  · exact Or.inr h5
end CFSG.Quasithin.ChapterE.ThompsonAction.LinearBlockSource
