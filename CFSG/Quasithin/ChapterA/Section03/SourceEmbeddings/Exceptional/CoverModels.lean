module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ClassicalCoverQuotient
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.EvenModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.OddModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.MathieuTwentyTwo
public import Theory.GroupTheory.PerfectCenterFrattini
/-!
# Exceptional local sections exclude the genuine three-cover branch

The source three-cover branch supplies a center of order three. Passing to
the actual central quotient preserves the local component, its full-Sylow
normalization, and its exceptional two-core section. Odd, Bender, alternating,
and M₂₂ quotient rows are excluded by the established model inspections.
In the remaining binary linear-three row, the even rank-two result makes the
mapped local component the whole quotient. A perfect group has no proper
supplement to its center, so the original subgroup is the whole cover.
Its exceptional quotient is centerless, forcing the order-three center into
the two-core, a contradiction.

Source: Aschbacher–Smith A.3.6(2), A.3.12, and 13.6.27, printed pp.43–48
and 934. The order-three center is the actual earlier-source conclusion;
no stronger model-only cover exclusion is asserted.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
private theorem not_model_of_center_three [Group.IsPerfect G]
    (hc : Nonempty (center G ≃* Multiplicative (ZMod 3)))
    (h : IsModel (G ⧸ pCore 2 G)) : False := by
 let π := QuotientGroup.mk' (pCore 2 G)
 let : IsSimpleGroup (G ⧸ pCore 2 G) := h.isSimple
 let : Group.IsPerfect (G ⧸ pCore 2 G) := Group.IsPerfect.ofSurjective (f := π)
   (QuotientGroup.mk'_surjective _)
 have hz : center (G ⧸ pCore 2 G) = ⊥ :=
   (inferInstance : (center (G ⧸ pCore 2 G)).Normal).eq_bot_or_eq_top.resolve_right
     (fun ht => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp ht))
 have hZ : center G ≤ pCore 2 G := by
   intro x hx
   apply (QuotientGroup.eq_one_iff _).mp
   apply mem_bot.mp
   rw [← hz]
   apply mem_center_iff.mpr
   intro y
   obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 G) y
   exact (map_mul π y x).symm.trans
     ((congrArg π (mem_center_iff.mp hx y)).trans (map_mul π x y))
 have hp : IsPGroup 2 (center G) := pCore_isPGroup.of_injective
   (inclusion hZ) (inclusion_injective hZ)
 obtain ⟨n,hn⟩ := hp.exists_card_eq
 have hcard : Nat.card (center G) = 3 := by
   rw [Nat.card_congr hc.some.toEquiv]
   simp
 rw [hcard] at hn
 have hcop := (by decide : Nat.Coprime 3 2).pow_right n
 rw [← hn] at hcop
 norm_num at hcop

private theorem not_section_of_center_three_of_full_image [Group.IsPerfect G]
    (hc : Nonempty (center G ≃* Multiplicative (ZMod 3)))
    {B : Subgroup G} (h : IsModel (B ⧸ pCore 2 B))
    (ht : B.map (QuotientGroup.mk' (center G)) = ⊤) : False := by
 have hsup : B ⊔ center G = ⊤ := by
   have he := congrArg (Subgroup.comap (QuotientGroup.mk' (center G))) ht
   simpa only [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] using he
 have hb : B = ⊤ := eq_top_of_sup_center_eq_top B hsup
 let e : G ≃* B := ((MulEquiv.subgroupCongr hb).trans topEquiv).symm
 have hh : IsModel (G ⧸ pCore 2 G) := h.of_equiv
   (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
 exact not_model_of_center_three hc hh

/-- The original order-three center excludes all three-cover rows for each
of the three exceptional local sections. -/
theorem not_threeCover [IsQuasisimple G]
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : IsModel (B ⧸ pCore 2 B))
    (hc : Nonempty (center G ≃* Multiplicative (ZMod 3)))
    (hm : ThreeCoverModel G) : False := by
 let π := QuotientGroup.mk' (center G)
 let : Group.IsSolvable π.ker := by
   change Group.IsSolvable (QuotientGroup.mk' (center G)).ker
   rw [QuotientGroup.ker_mk']
   exact Group.isSolvable_of_comm fun a b => IsMulCommutative.is_comm.comm a b
 let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
 let T := S.mapSurjective (QuotientGroup.mk'_surjective (center G))
 obtain ⟨hl,hn,ha⟩ := local_section_map hB hSB h π
 have hl' : B.map π ∈ localCComponents T := hl
 have hn' : (T : Subgroup (G ⧸ center G)) ≤ normalizer (B.map π : Set _) := hn
 cases hm with
 | classical unitary q hq hm =>
   rcases ClassicalCoverQuotient.models unitary q hq hm with ho | he | ⟨n,hpos,hr⟩
   · exact not_section_of_odd_model ho (B.map π) ha
   · exact not_section_of_bender_model T (B.map π) hl' hn' ha he
   · have ht := eq_top_of_rankTwo T hl' hn' ha (.linear hpos hr)
     exact not_section_of_center_three_of_full_image hc h ht
 | alternating_six hm =>
   obtain ⟨_,_,⟨e⟩⟩ := hm
   have hd := ambient_card_dvd ha
   rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hd
   norm_num at hd
 | alternating_seven hm =>
   obtain ⟨_,_,⟨e⟩⟩ := hm
   have hd := ambient_card_dvd ha
   rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hd
   norm_num at hd
 | mathieu hm =>
   exact not_mathieu_twentyTwo T (B.map π) hn' ha hm.2.2.some
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
