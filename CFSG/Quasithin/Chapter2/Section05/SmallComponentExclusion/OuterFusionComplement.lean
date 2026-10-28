module
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.OuterSquare
public import Theory.GroupTheory.NormalizedSupCard
/-!
# The actual complement acts as the full automorphism group

The action of A=K⟨y⟩ contains all inner automorphisms and an outer one,
so it is onto Aut(K). Since the selected outer element is an involution, the
product order formula bounds |A| by 2|K|=|Aut(K)|. The action is therefore
bijective. The original inclusion A≤H and conjugation map are retained.
Source: Aschbacher--Smith 2.5.15, printed p.559.
-/

public section


namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup Theory.GroupTheory A6Shadow.Frattini ComponentRefinement ComponentSelection ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M : Subgroup G}
  {S : Sylow 2 H} {z : G}

theorem linear_three_outer_involution_complement_equiv
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (e : K ≃* Matrix.PSL3Three.PSL) (y : H)
    (hyo : MathieuSourceSetup.componentAction c y ∉ MulAut.innerSubgroup K)
    (hy2 : orderOf y = 2) :
    let A := K ⊔ zpowers (y:G)
    ∃ hAH : A≤H, Function.Bijective
      ((MathieuSourceSetup.componentAction c).comp (inclusion hAH)) := by
  let A := K ⊔ zpowers (y:G)
  have hAH : A≤H := sup_le c.component_le (zpowers_le.mpr y.property)
  let α := MathieuSourceSetup.componentAction c
  let f : A →* MulAut K := α.comp (inclusion hAH)
  have hI : MulAut.innerSubgroup K ≤ f.range := by
    rintro _ ⟨k,rfl⟩
    refine ⟨⟨k,mem_sup_left k.property⟩,?_⟩
    ext r
    rfl
  have hi : (MulAut.innerSubgroup K).index=2 := by
    have hh := Matrix.PSL3Three.EightGeometry.inner_index_two
    rw [← MulAut.map_innerSubgroup_congr e,index_map_of_bijective (MulAut.congr e).bijective] at hh
    exact hh
  have hys : α y ∈ f.range := ⟨⟨y,mem_sup_right (mem_zpowers (y:G))⟩,rfl⟩
  have hfs : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    intro a _
    by_cases ha : a∈MulAut.innerSubgroup K
    · exact hI ha
    · have hm : a*(α y)⁻¹∈MulAut.innerSubgroup K := by
        rw [mul_mem_iff_of_index_two hi]
        change α y ∉ MulAut.innerSubgroup K at hyo
        simp only [ha,inv_mem_iff,hyo]
      have hh := f.range.mul_mem (hI hm) hys
      simpa only [inv_mul_cancel_right] using hh
  have hcardK : Nat.card K=5616 := (Nat.card_congr e.toEquiv).trans Matrix.PSL3Three.card_PSL
  have hcardAut : Nat.card (MulAut K)=11232 :=
    (Nat.card_congr (MulAut.congr e).toEquiv).trans
      Matrix.PSL3Three.FourGeometry.card_fullAutomorphismGroup
  have hNK : zpowers (y:G) ≤ normalizer (K:Set G) := (zpowers_le.mpr y.property).trans
    ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance)
  have hmul := card_mul_eq_card_inf_mul_card_sup_of_normalizes K (zpowers (y:G)) hNK
  have hoy : orderOf (y:G)=2 := (Subgroup.orderOf_coe y).trans hy2
  rw [hcardK,Nat.card_zpowers,hoy] at hmul
  have hbound : 1 ≤ Nat.card (K⊓zpowers (y:G) : Subgroup G) := Nat.card_pos
  have hle : Nat.card A≤11232 := by
    change 5616*2=Nat.card (K⊓zpowers (y:G) : Subgroup G)*Nat.card A at hmul
    nlinarith
  have hge := Nat.card_le_card_of_surjective f hfs
  rw [hcardAut] at hge
  refine ⟨hAH,(Nat.bijective_iff_surjective_and_card f).mpr ⟨hfs,?_⟩⟩
  rw [hcardAut]
  omega
end CFSG.Quasithin.Chapter2.Section05
