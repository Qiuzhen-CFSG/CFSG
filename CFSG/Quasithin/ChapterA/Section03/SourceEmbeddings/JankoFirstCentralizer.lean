module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SolvableQuotients
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.EvenCharacteristic
public import CFSG.Quasithin.MainConverse.MathieuLocal.M22Even
public import Theory.Mathieu.M22.Properties.TwoLocalSeven
public import Theory.SpecificGroups.PSL3Two.Automorphisms
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoMathieu
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.QuotientExtension

/-!
# The original PSL₃(2) section cannot lie in the first J₄ centralizer

A local PSL₃(2) section normalized by a full M₂₂ Sylow cannot have
nontrivial two-core: its characteristic-core normalizer would be a
full-Sylow two-local with a factor seven. With trivial two-core, even
characteristic makes the Sylow action faithful, contradicting the order
336 of Aut(PSL₃(2)).

For the actual first J₄ centralizer, restrict the perfect section to the
literal index-two subgroup H. Its full Sylow intersection and the actual
solvable-kernel map H → M₂₂ preserve the original local section. This
proves the centralizer exclusion used by the degree-five plane comparison.

Source: Aschbacher--Smith 12.9.3, printed pp.858--859; GLS3 Table 5.3i.
The native quotient and matrix certificates retain their imported provenance.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoMathieu
open FiveLocalFF.SolvableQuotients

private noncomputable def threeEquiv {X : Type*} [Group X]
    (h : ClassicalGroup.IsPSL X 3 2) : X ≃* Matrix.PSL3Two.PSL := Classical.choice <| by
  obtain ⟨k,_,_,hk,⟨e⟩⟩ := h
  let := Fintype.ofFinite k
  let a : k ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hk)
  exact ⟨e.trans (Atlas.fieldEquivPSL 3 a)⟩

/-- M22 has no local PSL3(2) section normalized by a full Sylow two-subgroup. -/
theorem m22_not_three (S : Sylow 2 Sporadic.Mathieu.M22)
    (A : Subgroup Sporadic.Mathieu.M22) (ha : A ∈ localCComponents S)
    (hn : (S : Subgroup Sporadic.Mathieu.M22) ≤ normalizer (A : Set _))
    (hm : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 3 2) : False := by
  have h168 : Nat.card (A ⧸ pCore 2 A) = 168 := by
    obtain ⟨k,_,_,hk,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hk]
    norm_num
  by_cases hc : pCore 2 A = ⊥
  · let e := (QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hc).symm)).trans (threeEquiv hm)
    let := Atlas.Comparisons.Exceptional.psl3Two_simple
    let : IsSimpleGroup A := e.isSimpleGroup
    let := local_perfect ha
    have hz : center A = ⊥ :=
      (inferInstance : (center A).Normal).eq_bot_or_eq_top.resolve_right
        (fun ht => Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp ht))
    let : IsQuasisimple A :=
      ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
    have hfaith := sylow_centralizer_eq_bot_of_evenCharacteristic S
      (MainConverse.m22_evenCharacteristic S) ha hn
    let f := A.normalizerMonoidHom.comp (inclusion hn)
    have hf : Function.Injective f := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      apply eq_bot_iff.mpr
      intro x hx
      apply Subtype.ext
      apply mem_bot.mp
      rw [←hfaith]
      refine ⟨x.property,?_⟩
      change inclusion hn x ∈ A.normalizerMonoidHom.ker at hx
      rwa [normalizerMonoidHom_ker] at hx
    have hd := card_dvd_of_injective f hf
    rw [Nat.card_congr (MulAut.congr e).toEquiv,Matrix.PSL3Two.Automorphisms.card_aut] at hd
    have h32 : 2^5 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (by
      rw [Sporadic.Mathieu.m22_order]
      norm_num)
    norm_num at hd h32
    exact (by decide : ¬ 32 ∣ 336) (h32.trans hd)
  · let U := (pCore 2 A).map A.subtype
    have hu : U ≠ ⊥ := fun hz => hc ((map_eq_bot_iff_of_injective _ A.subtype_injective).mp hz)
    have hloc : IsTwoLocal (normalizer (U : Set _)) :=
      ⟨U,hu,pCore_isPGroup.map A.subtype,rfl⟩
    have hnU := normalizer_le_normalizer_characteristic_image A (pCore 2 A)
    have hnot := Sporadic.Mathieu.M22TwoLocalOrders.not_seven_dvd_card_twoLocal
      S (normalizer (U : Set _)) hloc (hn.trans hnU)
    have h7 : 7 ∣ Nat.card A := by
      have hd := card_quotient_dvd_card (pCore 2 A)
      rw [h168] at hd
      exact (by decide : 7 ∣ 168).trans hd
    exact hnot (h7.trans (card_dvd_of_le (A.le_normalizer.trans hnU)))

/-- A soluble kernel cannot hide the original local PSL3(2) quotient. -/
theorem not_three_of_m22_surjection {G : Type*} [Group G] [Finite G]
    (q : G →* Sporadic.Mathieu.M22) (hq : Function.Surjective q)
    [Group.IsSolvable q.ker] (S : Sylow 2 G) (A : Subgroup G)
    (ha : A ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (A : Set G))
    (hm : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 3 2) : False := by
  let := local_perfect ha
  let := Atlas.Comparisons.Exceptional.psl3Two_simple
  let : IsSimpleGroup (A ⧸ pCore 2 A) := (threeEquiv hm).isSimpleGroup
  let f := q.subgroupMap A
  let : Group.IsSolvable f.ker := by
    change Group.IsSolvable (q.subgroupMap A).ker
    rw [ker_subgroupMap]
    exact Group.isSolvable_of_isSolvable_injective
      (f := A.subtype.subgroupComap q.ker) (fun x y hh => Subtype.ext (Subtype.ext
        (congrArg (fun z : q.ker => (z : G)) hh)))
  let e := PerfectCoreTwoExtension.solvableKernelQuotientEquiv f (q.subgroupMap_surjective A)
  exact m22_not_three (S.mapSurjective hq) (A.map q)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker ha q)
    ((map_mono (f := q) hn).trans (A.le_normalizer_map q)) (hm.of_mulEquiv e.symm)

open Janko4.InvolutionCentralizers.First
open Janko4.InvolutionCentralizers.First.QuotientExtension
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The native first J4 involution centralizer has no full-Sylow-normalized
local PSL3(2) section. Restriction to its actual index-two subgroup and the
literal projection to M22 retain the section and Sylow intersection. -/
theorem first_centralizer_not_three (S : Sylow 2 centralizer)
    (A : Subgroup centralizer) (ha : A ∈ localCComponents S)
    (hn : (S : Subgroup centralizer) ≤ normalizer (A : Set centralizer))
    (hm : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 3 2) : False := by
  let := local_perfect ha
  let : Group.IsSolvable (centralizer ⧸ H) :=
    Group.isSolvable_of_surjective (f := centralizerQuotientEquivC2.symm.toMonoidHom)
      centralizerQuotientEquivC2.symm.surjective
  have hAH : A ≤ H := le_of_isPerfect_of_solvable_quotient A H
  obtain ⟨P,hP,hAP⟩ := exists_local_sylow_restriction S ha hAH
    (inferInstance : H.Normal).isSubnormal
  let d := subgroupOfEquivOfLe hAH
  let e := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  have hn' : (P : Subgroup H) ≤ normalizer (A.subgroupOf H : Set H) := by
    rw [hP]
    intro s hs
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (hn hs) (a : centralizer)
  let : Group.IsNilpotent (Q.subgroupOf R) :=
    (show IsPGroup 2 (Q.subgroupOf R) from pCore_isPGroup.comap_subtype).isNilpotent
  let : Group.IsSolvable scalarSubgroup := Group.isSolvable_of_surjective
    (f := scalarSubgroupEquivC3.symm.toMonoidHom) scalarSubgroupEquivC3.symm.surjective
  let : Group.IsSolvable R := Group.isSolvable_of_ker_le_range
    (Q.subgroupOf R).subtype scalarProjection (by rw [range_subtype,scalarProjection_ker])
  let : Group.IsSolvable mathieuProjection.ker := by
    rw [mathieuProjection_ker]
    exact Group.isSolvable_of_surjective
      (f := (subgroupOfEquivOfLe R_le_H).symm.toMonoidHom)
      (subgroupOfEquivOfLe R_le_H).symm.surjective
  exact not_three_of_m22_surjection mathieuProjection mathieuProjection_surjective P
    (A.subgroupOf H) hAP hn' (hm.of_mulEquiv e)
/-- Transport the first-centralizer exclusion through an actual equivalence. -/
theorem not_three_of_first_equiv {G : Type*} [Group G] [Finite G]
    (e : G ≃* centralizer) (S : Sylow 2 G) (A : Subgroup G)
    (ha : A ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (A : Set G))
    (hm : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 3 2) : False := by
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  let d := e.subgroupMap A
  let a := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  exact first_centralizer_not_three (S.mapSurjective e.surjective) (A.map e.toMonoidHom)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker ha e.toMonoidHom)
    ((map_mono (f := e.toMonoidHom) hn).trans (A.le_normalizer_map e.toMonoidHom))
    (hm.of_mulEquiv a.symm)

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoMathieu
