module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ClassicalCoverQuotient
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.EvenModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.OddModels
public import Theory.Mathieu.M22.Properties.Order

/-!
# The exceptional Hall–Janko seed excludes three-cover containing groups

The actual central quotient map preserves the seed's J₂ two-core quotient,
local-component membership, and full-Sylow normalization. Odd and Bender
quotients are excluded by their existing section arguments. In a binary
linear-three quotient, the even rank-two theorem makes the mapped seed the
whole group. Its order would then be 604800; the unipotent subgroup forces
the field to have order at most four, and both possible orders contradict it.
The remaining A₆, A₇, and M₂₂ quotient rows fail divisibility by 604800.

Source: Aschbacher–Smith A.3.6(2), A.3.12, and the exceptional application
in 13.6.27, printed pp.43–48 and 934. No full embedding classification is assumed.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
private theorem jankoTwo_section_map {H : Type*} [Group H] [Finite H]
    (B : Subgroup G) [Group.IsPerfect B]
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.LeechRelated.J2.Carrier))
    (f : G →* H) [Group.IsSolvable f.ker] :
    Nonempty (((B.map f) ⧸ pCore 2 (B.map f)) ≃* Sporadic.LeechRelated.J2.Carrier) := by
 let : IsSimpleGroup (B ⧸ pCore 2 B) := (show IsModel (B ⧸ pCore 2 B) from .inl h).isSimple
 let g := f.subgroupMap B
 let : Group.IsSolvable g.ker := by
   change Group.IsSolvable (f.subgroupMap B).ker
   rw [Subgroup.ker_subgroupMap]
   exact Group.isSolvable_of_isSolvable_injective
     (f := B.subtype.subgroupComap f.ker) (fun a b he => Subtype.ext (Subtype.ext
       (congrArg (fun x : f.ker => (x : G)) he)))
 exact ⟨(PerfectCoreTwoExtension.solvableKernelQuotientEquiv g
   (f.subgroupMap_surjective B)).symm.trans h.some⟩
omit [Finite G] in
private theorem ambient_jankoTwo_card_dvd {B : Subgroup G}
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.LeechRelated.J2.Carrier)) :
    604800 ∣ Nat.card G := by
 have hd := (card_quotient_dvd_card (pCore 2 B)).trans B.card_subgroup_dvd_card
 rwa [Nat.card_congr h.some.toEquiv,
   Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at hd
omit [Finite G] in
private theorem jankoTwo_card_of_top [IsSimpleGroup G] {B : Subgroup G}
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.LeechRelated.J2.Carrier))
    (ht : B = ⊤) : Nat.card G = 604800 := by
 let e : B ≃* G := (MulEquiv.subgroupCongr ht).trans topEquiv
 let : IsSimpleGroup B := e.isSimpleGroup
 have hc : Nat.card (B ⧸ pCore 2 B) = 604800 := by
   rw [Nat.card_congr h.some.toEquiv,
     Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
 have hb : pCore 2 B = ⊥ := by
   apply (inferInstance : (pCore 2 B).Normal).eq_bot_or_eq_top.resolve_right
   intro he
   rw [he] at hc
   simp at hc
 let q : B ⧸ pCore 2 B ≃* B :=
   (QuotientGroup.quotientMulEquivOfEq hb).trans QuotientGroup.quotientBot
 exact (Nat.card_congr (q.trans e).toEquiv).symm.trans hc
omit [Finite G] in
private theorem not_linear_three_of_jankoTwo_card {n : ℕ} (hn : 1 ≤ n)
    (hm : ClassicalGroup.IsPSL G 3 (2 ^ n)) (hc : Nat.card G = 604800) : False := by
 obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
 have hn2 : n ≤ 2 := by
   by_contra hn2
   have hd := (Matrix.PSL3.LinearThree.unipotent F).card_subgroup_dvd_card
   rw [Matrix.PSL3.LinearThree.card_unipotent,hF,← Nat.card_congr e.toEquiv,hc,← pow_mul] at hd
   have hp : 512 ∣ 2 ^ (n * 3) := Nat.pow_dvd_pow 2 (by omega : 9 ≤ n * 3)
   exact (by decide : ¬ 512 ∣ 604800) (hp.trans hd)
 have he := (Nat.card_congr e.toEquiv).symm.trans hc
 rw [Matrix.PSL3.LinearThree.card_projective,hF] at he
 interval_cases n <;> norm_num at he

/-- The actual J₂ local seed cannot lie in any of the A.3.6 three-cover rows.
The original central quotient map preserves both the seed and its Sylow actor. -/
theorem not_threeCover_of_jankoTwo [IsQuasisimple G]
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.LeechRelated.J2.Carrier))
    (hm : ThreeCoverModel G) : False := by
 let π := QuotientGroup.mk' (center G)
 let : Group.IsSolvable π.ker := by
   change Group.IsSolvable (QuotientGroup.mk' (center G)).ker
   rw [QuotientGroup.ker_mk']
   exact Group.isSolvable_of_comm fun a b => IsMulCommutative.is_comm.comm a b
 let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
 let T := S.mapSurjective (QuotientGroup.mk'_surjective (center G))
 let := local_perfect hB
 have ha := jankoTwo_section_map B h π
 obtain ⟨hl,hn,_⟩ := local_section_map hB hSB (show IsModel (B ⧸ pCore 2 B) from .inl h) π
 have hl' : B.map π ∈ localCComponents T := hl
 have hn' : (T : Subgroup (G ⧸ center G)) ≤ normalizer (B.map π : Set _) := hn
 have hmodel : IsModel ((B.map π) ⧸ pCore 2 (B.map π)) := .inl ha
 cases hm with
 | classical unitary q hq hm =>
   rcases ClassicalCoverQuotient.models unitary q hq hm with ho | he | ⟨n,hpos,hr⟩
   · exact not_section_of_odd_model ho (B.map π) hmodel
   · exact not_section_of_bender_model T (B.map π) hl' hn' hmodel he
   · have ht := eq_top_of_rankTwo T hl' hn' hmodel (.linear hpos hr)
     exact not_linear_three_of_jankoTwo_card hpos hr (jankoTwo_card_of_top ha ht)
 | alternating_six hm =>
   obtain ⟨_,_,⟨e⟩⟩ := hm
   have hd := ambient_jankoTwo_card_dvd ha
   rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hd
   norm_num at hd
 | alternating_seven hm =>
   obtain ⟨_,_,⟨e⟩⟩ := hm
   have hd := ambient_jankoTwo_card_dvd ha
   rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hd
   norm_num at hd
 | mathieu hm =>
   have hd := ambient_jankoTwo_card_dvd ha
   rw [Nat.card_congr hm.2.2.some.toEquiv,Sporadic.Mathieu.m22_order] at hd
   norm_num at hd
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
