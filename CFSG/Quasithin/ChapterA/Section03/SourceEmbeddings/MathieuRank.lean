module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.Sections
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.EvenRankTwoComplete
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.SporadicOrders
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.SpecificGroups.SU3.BinaryG2Comparison
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.SpecificGroups.Held.Model.Transitivity
public import Theory.SpecificGroups.Rudvalis.Model.Order
public import Theory.SpecificGroups.BinaryLinear.AutomorphismTwoRank
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuasisimpleContaining
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ClassicalCoverQuotient
public import Theory.Mathieu.M22.Properties.TwoRank
public import Theory.Alternating.Aut
public import Theory.GroupTheory.PrimeRankOrderBound
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismRank
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.SourceBound
public import Theory.SpecificGroups.SU3.EvenTwoRank.Automorphisms.Unconditional
public import Theory.SpecificGroups.SU3.BinarySylowOrder
public import Theory.SpecificGroups.Suzuki.TwoRank
public import CFSG.Quasithin.ClassificationModels.Families
public import CFSG.Quasithin.ChapterA.Section02.OddModelTwoRank
public import Theory.SpecificGroups.PSL3.OddPrimeActorRank
public import Theory.SpecificGroups.SU3.FiveCentralizerRadical.Outer
public import Theory.Mathieu.M24.Properties.Order
public import Theory.Mathieu.M24.ChapterHStabilizers.ElementaryFusion.Candidates
public import Theory.GroupTheory.PerfectCentralCoverOddPart
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.SL2.OddOrderDivisibility

/-!
# Quasisimple subgroups acted on by a full Mathieu Sylow

The native M₂₄ elementary subgroup of order 64 forces automorphism two-rank
at least six whenever a full Sylow acts faithfully on a normalized subgroup.
Perfectness preserves this obstruction on the actual central quotient.
The original factor seven also survives central descent, since 49 does not
divide the ambient order and cyclic Sylow transfer excludes it from a
perfect central kernel.

The complete A.3.6 three-cover list is thereby excluded. For the remaining
simple subgroup, Theorem C supplies the full carrier catalogue. Native
orders, root subgroup orders and automorphism ranks eliminate every row
except M₂₄ itself. Equality of orders then forces the subgroup to be the
whole ambient group. The final theorem retains the actual normalized
subgroup, full Sylow and SQTK hypothesis; Components/MathieuComplete applies
it to the literal JT/O₂(JT) plane image of source 12.9.3.

Source: Aschbacher--Smith A.2.3, A.3.6 and 12.9.3, printed pp.33,
43--45 and 858--859 of refs/quasithin.pdf. Concrete carrier facts and their
source attribution are inherited from the imported model modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.MathieuRank

private theorem two_exponent_le_ten {k : ℕ} (h : 2 ^ k ∣ 244823040) : k ≤ 10 := by
  by_contra! hk
  have hd : 2048 ∣ 244823040 := (pow_dvd_pow 2 hk).trans h
  norm_num at hd

variable {X : Type*} [Group X] [Finite X]

/-- The binary rank-one carriers cannot have both the native Mathieu order
bound and automorphism two-rank at least six. -/
theorem not_bender_of_mathieu_order
    (hd : Nat.card X ∣ 244823040) (hr : 6 ≤ primeRank 2 (MulAut X)) :
    ¬ ClassificationModels.IsBenderModel X := by
  intro hm
  cases hm with
  | linear n hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (by
      simpa only [Nat.card_eq_fintype_card] using hF)
    have hc : Nat.card X = 2^n * ((2^n)^2 - 1) := by
      rw [Nat.card_congr e.toEquiv,← Nat.card_congr (Theory.PSL2.sl2QuotientEquiv F).toEquiv,
        GorensteinWalter.sl2_card_formula,hF]
    have hn10 : n ≤ 10 := two_exponent_le_ten (by
      apply dvd_trans (dvd_mul_right _ ((2^n)^2 - 1))
      rwa [←hc])
    have hn6 : 6 ≤ n := by
      rw [primeRank_equiv 2 (MulAut.congr e)] at hr
      exact hr.trans (Theory.PSL2.BinaryAutomorphismRank.psl2_automorphism_two_rank_le hn hF)
    rw [hc] at hd
    interval_cases n <;> norm_num at hd
  | unitary n hn hm =>
    obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv X e.toEquiv
    have hc := HermitianForm.BinarySylowOrder.cube_dvd_card_projective J (by omega) hF hconj
    rw [←Nat.card_congr e.toEquiv,←pow_mul] at hc
    have hn10 := two_exponent_le_ten (hc.trans hd)
    rw [primeRank_equiv 2 (MulAut.congr e)] at hr
    have hb := HermitianForm.EvenTwoRank.automorphism_two_rank_le J hn hF hconj
    omega
  | suzuki m hm he =>
    obtain ⟨e⟩ := he
    have hc := (SuzukiRootSubgroup m).card_subgroup_dvd_card
    rw [suzukiRootSubgroup_card m (by omega),←Nat.card_congr e.toEquiv,←pow_mul] at hc
    have hn10 := two_exponent_le_ten (hc.trans hd)
    rw [primeRank_equiv 2 (MulAut.congr e)] at hr
    have hb := suzuki_automorphism_two_rank m (by omega)
    omega

/-- The same constraints exclude every binary PSL₃ carrier. The only degree
allowed by rank and the defining two-part is three, whose order has a factor 73. -/
theorem not_binary_three_of_mathieu_order
    (hd : Nat.card X ∣ 244823040) (hr : 6 ≤ primeRank 2 (MulAut X))
    {n : ℕ} (hn : 1 ≤ n) : ¬ ClassicalGroup.IsPSL X 3 (2^n) := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  have hc := (Matrix.PSL3.LinearThree.unipotent F).card_subgroup_dvd_card
  rw [Matrix.PSL3.LinearThree.card_unipotent F,hF,←pow_mul,←Nat.card_congr e.toEquiv] at hc
  have hn10 := two_exponent_le_ten (hc.trans hd)
  rw [primeRank_equiv 2 (MulAut.congr e),Matrix.PSL3Even.automorphism_two_rank_eq F (by omega) hF] at hr
  have he : n = 3 := by omega
  rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hF,he] at hd
  norm_num at hd

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.MathieuRank

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.MathieuRank

/-- The explicit native elementary subgroup forces two-rank at least six
in every Mathieu Sylow, with no subgroup catalogue premise. -/
theorem six_le_sylow_rank {G : Type*} [Group G] [Finite G]
    (e : G ≃* Sporadic.Mathieu.M24) (S : Sylow 2 G) : 6 ≤ primeRank 2 S := by
  rw [←S.primeRank_eq,primeRank_equiv 2 e]
  have hc := (primeRank_le_iff_elementary_card_le (p := 2) Sporadic.Mathieu.M24).mp le_rfl
    (Sporadic.Mathieu.M24LocalGeometry.EvenCandidates.elementary 0) inferInstance
  rw [Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion.candidate_card] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc

/-- The literal faithful Sylow action imposes the same lower bound on
the full automorphism group of the normalized subgroup. -/
theorem six_le_automorphism_rank {G : Type*} [Group G] [Finite G]
    (e : G ≃* Sporadic.Mathieu.M24) (S : Sylow 2 G) (B : Subgroup G)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hf : (S : Subgroup G) ⊓ centralizer (B : Set G) = ⊥) :
    6 ≤ primeRank 2 (MulAut B) := by
  let f := B.normalizerMonoidHom.comp (inclusion hn)
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro a ha
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hf]
    refine ⟨a.property,?_⟩
    change inclusion hn a ∈ B.normalizerMonoidHom.ker at ha
    rwa [normalizerMonoidHom_ker] at ha
  exact (six_le_sylow_rank e S).trans (Theory.GroupTheory.primeRank_le_of_injective 2 f hi)

/-- Perfectness makes central descent faithful, so the source's actual
central quotient retains the rank-six automorphism obstruction. -/
theorem six_le_central_quotient_automorphism_rank
    {G : Type*} [Group G] [Finite G]
    (e : G ≃* Sporadic.Mathieu.M24) (S : Sylow 2 G) (B : Subgroup G)
    [Group.IsPerfect B]
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hf : (S : Subgroup G) ⊓ centralizer (B : Set G) = ⊥) :
    6 ≤ primeRank 2 (MulAut (B ⧸ center B)) :=
  (six_le_automorphism_rank e S B hn hf).trans
    (Theory.GroupTheory.primeRank_le_of_injective 2 (Subgroup.quotientAut (center B)) MulAut.quotient_center_injective)

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.MathieuRank

namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.MathieuRank
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups

private theorem unitary_odd_automorphism_rank
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    [Finite (ProjectiveSpecialUnitaryMatrixGroup J)]
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    [Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p^2) (hconj : ∀ x, J.conj x = x^p) :
    primeRank 2 (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ 3 := by
  let Y := ProjectiveSpecialUnitaryMatrixGroup J
  have hz : center Y = ⊥ :=
    (inferInstance : (center Y).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => Group.IsPerfect.not_isMulCommutative Y (center_eq_top_iff.mp ht))
  let e : Y ≃* MulAut.innerSubgroup Y :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hz)
  let P : Sylow 2 (MulAut.Outer Y) := Classical.choice inferInstance
  have hcyc : IsCyclic P := HermitianForm.FiveCentralizerRadical.isCyclic_of_outer_injective
    J hp ho hF hconj (P := ↥P) P.isPGroup'
      (P : Subgroup (MulAut.Outer Y)).subtype (P : Subgroup (MulAut.Outer Y)).subtype_injective
  have hout := P.primeRank_le_one_of_isCyclic hcyc
  have hr := primeRank_le_ker_add (p := 2) (QuotientGroup.mk' (MulAut.innerSubgroup Y))
  rw [QuotientGroup.ker_mk',←primeRank_equiv 2 e] at hr
  have hi := Theory.SpecificGroups.OddThreeRank.psu3_primeRank_two_le J hp ho hF hconj
  change primeRank 2 Y ≤ 2 at hi
  change primeRank 2 (MulAut Y) ≤ primeRank 2 Y + primeRank 2 (MulAut.Outer Y) at hr
  change primeRank 2 (MulAut Y) ≤ 3
  omega

/-- All odd-characteristic Theorem C rows have small automorphism two-rank;
the original factor seven excludes the solvable tiny PSL₂ endpoint. -/
theorem not_odd_of_large_automorphism_rank
    {X : Type*} [Group X] [Finite X] [IsSimpleGroup X] [Group.IsPerfect X]
    (h7 : 7 ∣ Nat.card X) (hr : 6 ≤ primeRank 2 (MulAut X)) :
    ¬ ChapterA.Section02.IsTheoremCOddModel X := by
  intro hm
  cases hm with
  | linear_two p n hp ho _ hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    have hn : 0 < n := by
      have hl := Finite.one_lt_card (α := F)
      by_contra! hn
      simp only [Nat.le_zero.mp hn,pow_zero] at hF
      omega
    have hlarge : 3 < Nat.card F := by
      by_contra! hsmall
      have hl := Finite.one_lt_card (α := F)
      have hh := ((Nat.card_congr e.toEquiv) ▸ h7).trans
        (card_quotient_dvd_card (center SL(2,F)))
      rw [GorensteinWalter.sl2_card_formula] at hh
      rcases (show Nat.card F = 2 ∨ Nat.card F = 3 by omega) with h | h <;>
        rw [h] at hh <;> norm_num at hh
    rw [primeRank_equiv 2 (MulAut.congr e)] at hr
    have hb := Theory.PSL2.odd_automorphism_two_rank F ⟨p,n,hp,ho,hn,hF⟩ hlarge
    omega
  | linear_three p hp ho hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
    let : Group.IsPerfect PSL(3,F) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    have hb := Matrix.PSL3.OddPrimeActorRank.automorphism_two_rank
      (Group.IsPerfect.not_isSolvable PSL(3,F)) hp ho hF
    rw [primeRank_equiv 2 (MulAut.congr e)] at hr
    omega
  | unitary_three p hp ho hm =>
    obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv X e.toEquiv
    let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := e.symm.isSimpleGroup
    let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    have hb := unitary_odd_automorphism_rank J hp ho hF hconj
    rw [primeRank_equiv 2 (MulAut.congr e)] at hr
    omega
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.MathieuRank

namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.MathieuRank
open Subgroup Theory.GroupTheory

/-- The factor seven of the original plane section survives its perfect
central quotient: 49 does not divide the ambient Mathieu order. -/
theorem seven_dvd_central_quotient
    {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    (hd : Nat.card G ∣ 244823040) (h7 : 7 ∣ Nat.card G) :
    7 ∣ Nat.card (G ⧸ center G) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let f : PerfectCentralCovering.Cover G (G ⧸ center G) := {
    toMonoidHom := QuotientGroup.mk' (center G)
    surjective := QuotientGroup.mk'_surjective _
    isPerfect := inferInstance
    ker_le_center := (QuotientGroup.ker_mk' _).le }
  have hz : ¬ 7 ∣ Nat.card (center G) := by
    have hk := f.not_dvd_card_kernel_of_square_not_dvd (p := 7) (by
      intro hh
      have := hh.trans ((card_quotient_dvd_card (center G)).trans hd)
      norm_num at this)
    simpa only [f,QuotientGroup.ker_mk'] using hk
  have hc := card_eq_card_quotient_mul_card_subgroup (center G)
  rw [hc] at h7
  exact ((by decide : Nat.Prime 7).dvd_mul.mp h7).resolve_right hz

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.MathieuRank

namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.MathieuRank
open Subgroup Theory.GroupTheory Chapter1.Section02.LocalModels

/-- None of the A.3.6 three-cover rows survives the rank-six central-quotient
obstruction. The small alternating quotient loses seven or has small
symmetric automorphism group; the Mathieu quotient has rank at most five. -/
theorem not_three_cover_of_mathieu_order
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (hd : Nat.card G ∣ 244823040) (h7 : 7 ∣ Nat.card G)
    (hr : 6 ≤ primeRank 2 (MulAut (G ⧸ center G))) : ¬ ThreeCoverModel G := by
  let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
  let : Group.IsPerfect (G ⧸ center G) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center G))
      (QuotientGroup.mk'_surjective _)
  have hdQ := (card_quotient_dvd_card (center G)).trans hd
  have h7Q := seven_dvd_central_quotient hd h7
  intro hm
  cases hm with
  | classical u q hq hm =>
    rcases ClassicalCoverQuotient.models u q hq hm with hm | hm | ⟨n,hn,hm⟩
    · exact not_odd_of_large_automorphism_rank h7Q hr hm
    · exact not_bender_of_mathieu_order hdQ hr hm
    · exact not_binary_three_of_mathieu_order hdQ hr hn hm
  | alternating_six hm =>
    obtain ⟨e⟩ := hm.2.2
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin] at h7Q
    norm_num at h7Q
  | alternating_seven hm =>
    obtain ⟨e⟩ := hm.2.2
    let a : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
      MulEquiv.ofBijective _ (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
        7 (by decide) (by decide))
    rw [primeRank_equiv 2 (MulAut.congr e),←primeRank_equiv 2 a] at hr
    have hb : primeRank 2 (Equiv.Perm (Fin 7)) ≤ 4 :=
      primeRank_le_of_prime_pow_not_dvd (by
        rw [Nat.card_perm,Nat.card_fin]
        norm_num)
    omega
  | mathieu hm =>
    obtain ⟨e⟩ := hm.2.2
    rw [primeRank_equiv 2 (MulAut.congr e)] at hr
    have hb := Sporadic.Mathieu.m22_automorphism_twoRank_le_five
    omega

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.MathieuRank

namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.MathieuRank
open Subgroup Theory.GroupTheory

/-- A quasisimple SQTK group with the surviving Mathieu plane invariants
is simple: the full A.3.6 catalogue supplies and then excludes every cover. -/
theorem simple_of_mathieu_order
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (hsq : IsSQTK KnownSimple.IsKnownSimple G) (hcore : pCore 2 G = ⊥)
    (hd : Nat.card G ∣ 244823040) (h7 : 7 ∣ Nat.card G)
    (hr : 6 ≤ primeRank 2 (MulAut (G ⧸ center G))) : IsSimpleGroup G := by
  let : IsQuasisimple (⊤ : Subgroup G) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have ht : (⊤ : Subgroup G).IsCComponent :=
    (show IsComponent G ⊤ from ⟨.top,inferInstance⟩).isCComponent
  rcases quasisimple_containing_component_models_knownSimple hsq hcore ht with h | h
  · let := h.1
    exact (topEquiv (G := G)).symm.isSimpleGroup
  · have hc := Nat.card_congr (topEquiv (G := G)).toEquiv
    let a : ((⊤ : Subgroup G) ⧸ center (⊤ : Subgroup G)) ≃* (G ⧸ center G) :=
      QuotientGroup.congr _ _ topEquiv (by
        apply le_antisymm
        · rintro _ ⟨x,hx,rfl⟩
          exact (centerCongr topEquiv ⟨x,hx⟩).property
        · intro y hy
          exact ⟨topEquiv.symm y,(centerCongr topEquiv.symm ⟨y,hy⟩).property,rfl⟩)
    exact (not_three_cover_of_mathieu_order (hc.symm ▸ hd) (hc.symm ▸ h7)
      (by rwa [primeRank_equiv 2 (MulAut.congr a)]) h.2).elim

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.MathieuRank
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.MathieuRank
open Subgroup Theory.GroupTheory
open scoped MatrixGroups

private theorem not_small_alternating
    {G : Type*} [Group G] [Finite G]
    (h7 : 7 ∣ Nat.card G) (hr : 6 ≤ primeRank 2 (MulAut G))
    {n : ℕ} (hn : n ≤ 8) (e : G ≃* alternatingGroup (Fin n)) : False := by
  have hn7 : 7 ≤ n := by
    have hh := h7.trans ((Nat.card_congr e.toEquiv).symm ▸
      (alternatingGroup (Fin n)).card_subgroup_dvd_card)
    rw [Nat.card_perm,Nat.card_fin] at hh
    exact (Nat.Prime.dvd_factorial (by decide : Nat.Prime 7)).mp hh
  have hncase : n = 7 ∨ n = 8 := by omega
  rcases hncase with rfl | rfl
  · let a : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
      MulEquiv.ofBijective _ (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
        7 (by decide) (by decide))
    rw [primeRank_equiv 2 (MulAut.congr e),←primeRank_equiv 2 a] at hr
    have hb : primeRank 2 (Equiv.Perm (Fin 7)) ≤ 4 :=
      primeRank_le_of_prime_pow_not_dvd (by rw [Nat.card_perm,Nat.card_fin]; norm_num)
    omega
  · have hb := BinaryLinear.AutomorphismTwoRank.psl4_two_rank_le
    rw [primeRank_equiv 2 (MulAut.congr
      Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)] at hb
    rw [primeRank_equiv 2 (MulAut.congr e)] at hr
    omega

private theorem not_rank_two
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] [Group.IsPerfect G]
    (hd : Nat.card G ∣ 244823040) (h7 : 7 ∣ Nat.card G)
    (hr : 6 ≤ primeRank 2 (MulAut G))
    {n : ℕ} (hm : ChapterA.Section02.IsTheoremCRankTwoModel G n) : False := by
  have hsmall : ¬ 2048 ∣ Nat.card G := by
    intro hh
    have := hh.trans hd
    norm_num at this
  have large_power {a b : ℕ} (hh : 11 ≤ a*b) : 2048 ∣ (2^a)^b := by
    rw [←pow_mul]
    exact pow_dvd_pow 2 hh
  cases hm with
  | linear hn hm => exact not_binary_three_of_mathieu_order hd hr hn hm
  | symplectic hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    let a := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm
    have hu := (Theory.SpecificGroups.SymplecticFour.unipotent (F := F)).card_subgroup_dvd_card
    rw [Theory.SpecificGroups.SymplecticFour.card_unipotent,hF,
      ←Nat.card_congr a.toEquiv,←pow_mul] at hu
    have hn10 := two_exponent_le_ten (hu.trans hd)
    have he : n = 2 := by omega
    rw [Nat.card_congr a.toEquiv,Theory.SpecificGroups.SymplecticFour.card_sp,hF,he] at hd
    norm_num at hd
  | g2 hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    apply hsmall
    rw [Nat.card_congr e.toEquiv,Atlas.G2.card_Model,hF]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (large_power (by omega : 11 ≤ n*6)) _) _
  | triality hn hm =>
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff G n (by omega)).mp hm
    let P := Triality.Standard.binaryParameters n (by omega : 0 < n)
    have hu := (Triality.Standard.Parabolics.unipotent P).card_subgroup_dvd_card
    rw [Triality.Standard.Parabolics.card_unipotent_binary P rfl] at hu
    change (2^n)^12 ∣ Nat.card (Triality.Standard.BinaryCarrier n _) at hu
    rw [←Nat.card_congr e.toEquiv] at hu
    exact hsmall ((large_power (by omega : 11 ≤ n*12)).trans hu)
  | ree_f4 m _ _ he =>
    obtain ⟨e⟩ := he
    have hu := (ReeF4.Parabolics.unipotent m).card_subgroup_dvd_card
    rw [ReeF4.Parabolics.card_unipotent,←Nat.card_congr e.toEquiv] at hu
    exact hsmall ((large_power (by omega : 11 ≤ (2*m+1)*12)).trans hu)
  | symplectic_derived _ he =>
    rw [Nat.card_congr (he.some.trans
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix).toEquiv,
      nat_card_alternatingGroup,Nat.card_fin] at h7
    norm_num at h7
  | g2_derived _ he =>
    obtain ⟨b⟩ := Atlas.G2.nonempty_commutator_binary_equiv_psu3
    have hm : ClassicalGroup.IsPSU G 3 3 := by
      refine ⟨GaloisField 3 2,inferInstance,inferInstance,ABG.unitaryForm 3 3 1 (by decide),
        GaloisField.card 3 2 (by decide),?_,⟨he.some.trans b⟩⟩
      intro x
      change iterateFrobeniusEquiv (GaloisField 3 2) 3 1 x = x^3
      simp only [iterateFrobeniusEquiv_def,pow_one]
    exact not_odd_of_large_automorphism_rank h7 hr (.unitary_three 3 (by decide) (by decide) hm)
  | tits _ he =>
    rw [Nat.card_congr he.some.toEquiv,Tits.parrottGroup_card] at hd
    norm_num at hd

private theorem held_seven_square : 49 ∣ Nat.card Held.He := by
  have ho : MulAction.orbit Held.He (0 : Fin 2058) = Set.univ := by
    ext x
    simp only [Set.mem_univ,iff_true]
    obtain ⟨g,hg⟩ := Held.Transitivity.exists_move_zero x
    exact ⟨g,hg⟩
  have hc := (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Held.He (0 : Fin 2058))).symm
  rw [Nat.card_prod,ho,Nat.card_congr (Equiv.Set.univ _),Nat.card_fin] at hc
  rw [hc]
  exact dvd_mul_of_dvd_left (by decide : 49 ∣ 2058) _

/-- Among the full simple Theorem C catalogue, the actual Mathieu order,
factor seven and rank-six automorphism bound leave only M₂₄ itself. -/
theorem mathieu_of_simple_models
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] [Group.IsPerfect G]
    (hd : Nat.card G ∣ 244823040) (h7 : 7 ∣ Nat.card G)
    (hr : 6 ≤ primeRank 2 (MulAut G))
    (hm : ChapterA.Section02.IsTheoremCModel G) : Nonempty (G ≃* Sporadic.Mathieu.M24) := by
  cases hm with
  | alternating n hn he => exact (not_small_alternating h7 hr hn he.some).elim
  | odd hm => exact (not_odd_of_large_automorphism_rank h7 hr hm).elim
  | bender hm => exact (not_bender_of_mathieu_order hd hr hm).elim
  | rank_two _ hm => exact (not_rank_two hd h7 hr hm).elim
  | linear_binary n hn hm =>
    rcases hn with rfl | rfl
    · exact (not_small_alternating h7 hr (by decide) (AlternatingEight.modelEquiv hm)).elim
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let := Fintype.ofFinite F
      let f : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
        simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
      let a := (e.trans (Atlas.fieldEquivPSL 5 f)).trans (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide))
      have hc : Nat.card (BinaryLinear.OuterCyclic.LinearGroup 5) = 9999360 := by
        rw [←Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear 5).toEquiv,Matrix.card_GL_field]
        decide
      rw [Nat.card_congr a.toEquiv,hc] at hd
      norm_num at hd
  | sporadic hm =>
    change (∃ name : ClassificationModels.SporadicName, name ≠ .j3 ∧
      Nonempty (G ≃* name.Carrier)) ∨ Nonempty (G ≃* Janko1.Model) at hm
    rcases hm with ⟨name,hne,⟨e⟩⟩ | he
    · cases name with
      | m11 =>
        change G ≃* Sporadic.Mathieu.M11 at e
        rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m11_order] at h7
        norm_num at h7
      | m12 =>
        change G ≃* Sporadic.Mathieu.M12 at e
        rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m12_order] at h7
        norm_num at h7
      | m22 =>
        change G ≃* Sporadic.Mathieu.M22 at e
        rw [primeRank_equiv 2 (MulAut.congr e)] at hr
        exact (by have := Sporadic.Mathieu.m22_automorphism_twoRank_le_five; omega)
      | m23 =>
        change G ≃* Sporadic.Mathieu.M23 at e
        rw [primeRank_equiv 2 (MulAut.congr e)] at hr
        exact (by have := Sporadic.Mathieu.m23_automorphism_twoRank_le_four; omega)
      | m24 => exact ⟨e⟩
      | j2 =>
        change G ≃* Sporadic.LeechRelated.J2.Carrier at e
        rw [Nat.card_congr e.toEquiv,Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at hd
        norm_num at hd
      | j3 => exact (hne rfl).elim
      | j4 =>
        change G ≃* Janko4.Model at e
        rw [Nat.card_congr e.toEquiv,Janko4.Cardinality.model_card] at hd
        norm_num at hd
      | hs =>
        change G ≃* Sporadic.LeechRelated.HS.Carrier at e
        rw [Nat.card_congr e.toEquiv,Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier] at hd
        norm_num at hd
      | he =>
        change G ≃* Held.He at e
        have hh := held_seven_square.trans ((Nat.card_congr e.toEquiv) ▸ hd)
        norm_num at hh
      | ru =>
        change G ≃* Rudvalis.Model at e
        rw [Nat.card_congr e.toEquiv,Rudvalis.model_card] at hd
        norm_num at hd
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv,Janko1.card_model] at hd
      norm_num at hd

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.MathieuRank

namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.MathieuRank
open Subgroup Theory.GroupTheory

/-- A quasisimple subgroup containing a seven-section and acted on faithfully
by a full Mathieu Sylow is the whole group. The actual SQTK hypothesis
supplies Theorem C, and all of its model alternatives are discharged. -/
theorem eq_top_of_quasisimple_faithful_sylow
    {G : Type*} [Group G] [Finite G]
    (e : G ≃* Sporadic.Mathieu.M24) (S : Sylow 2 G) (B : Subgroup G)
    [IsQuasisimple B] (hsq : IsSQTK KnownSimple.IsKnownSimple B)
    (hcore : pCore 2 B = ⊥) (h7 : 7 ∣ Nat.card B)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hf : (S : Subgroup G) ⊓ centralizer (B : Set G) = ⊥) : B = ⊤ := by
  have hd : Nat.card B ∣ 244823040 := by
    have hh := B.card_subgroup_dvd_card
    rwa [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m24_order] at hh
  let : IsSimpleGroup B := simple_of_mathieu_order hsq hcore hd h7
    (six_le_central_quotient_automorphism_rank e S B hn hf)
  have hm := ChapterA.Section02.theoremC_knownSimple (G := B) inferInstance
    (Group.IsPerfect.not_isMulCommutative B) hsq.stronglyQuasithin hsq.isKGroup
  obtain ⟨a⟩ := mathieu_of_simple_models hd h7 (six_le_automorphism_rank e S B hn hf) hm
  exact B.eq_top_of_card_eq ((Nat.card_congr a.toEquiv).trans (Nat.card_congr e.toEquiv).symm)

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.MathieuRank
