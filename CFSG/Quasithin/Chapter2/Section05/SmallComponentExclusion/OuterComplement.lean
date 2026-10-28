module
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.OuterSquare
public import Theory.GroupTheory.NormalizedSupCard
/-!
# The actual complement acts as the full automorphism group

The action of A=K⟨y⟩ contains all inner automorphisms and an outer one,
so it is onto Aut(K). Since y has order four with its square in K, the
product order formula bounds |A| by 2|K|=|Aut(K)|. The action is therefore
bijective. The original inclusion A≤H and conjugation map are retained.
Source: Aschbacher--Smith 2.5.15, printed p.559.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup Theory.GroupTheory A6Shadow.Frattini ComponentRefinement ComponentSelection ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M : Subgroup G}
  {S : Sylow 2 H} {z : G}

theorem linear_three_outer_complement_equiv
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (e : K ≃* Matrix.PSL3Three.PSL) (y : H)
    (hyo : MathieuSourceSetup.componentAction c y ∉ MulAut.innerSubgroup K)
    (hy4 : orderOf y = 4) (hy2 : (y:G)^2 ∈ K) :
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
  have hoy : orderOf (y:G)=4 := (Subgroup.orderOf_coe y).trans hy4
  rw [hcardK,Nat.card_zpowers,hoy] at hmul
  have hbound : 2≤Nat.card (K⊓zpowers (y:G) : Subgroup G) := by
    have hz2 : orderOf ((y:G)^2)=2 := by rw [orderOf_pow,hoy]; norm_num
    have hm : zpowers ((y:G)^2) ≤ K⊓zpowers (y:G) :=
      zpowers_le.mpr ⟨hy2,pow_mem (mem_zpowers (y:G)) 2⟩
    have hh := Nat.card_le_card_of_injective (inclusion hm) (inclusion_injective hm)
    rw [Nat.card_zpowers,hz2] at hh
    exact hh
  have hle : Nat.card A≤11232 := by
    change 5616*4=Nat.card (K⊓zpowers (y:G) : Subgroup G)*Nat.card A at hmul
    nlinarith
  have hge := Nat.card_le_card_of_surjective f hfs
  rw [hcardAut] at hge
  refine ⟨hAH,(Nat.bijective_iff_surjective_and_card f).mpr ⟨hfs,?_⟩⟩
  rw [hcardAut]
  omega
end CFSG.Quasithin.Chapter2.Section05
