module

public import Theory.GroupTheory.SolvableRadical.NormalTwoExtension
public import Theory.GroupTheory.SylowNormalizedSupIntersection
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.InnerFamilies.LocalPair
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.InnerFamilies.TauMembers.AmbientCores
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.InnerFamilies.TauMembers.BinaryLocal
public import Theory.GroupTheory.SolvableResidual.TwoSupplement
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismRank

/-!
# E-members from tau-enlarged PSL₃ locals

A normalized two-extension of a perfect SL₂ local has two-closed radical,
equal to its actual two-core. The local's simple image in the radical
quotient is the entire layer, has two-group quotient, and has full commutator
with every actor surviving that radical. Perfectness of the normal local
identifies O² and the solvable residual, even when the extension is not perfect.
Normality reduces the literal local tau orbit to that one component.

The quotient action embeds the actual two-core quotient into Aut(SL₂(F)).
The existing sharp automorphism two-rank bound therefore includes all outer
field actors. A separate Sylow intersection argument verifies E0.

The final application uses the published `localImage` and `coreImage` through
the original `linearThreeEmbedding`. Faithful conjugation on the simple
generalized Fitting subgroup gives equality of the embedded local and extended
two-cores. In the binary case a normalizing tau lies in the actual S₄ local,
whose S₃ quotient gives all E1 clauses at the prime three.

`tauJoin_isEMemberAt` discharges the E-member input of
`parabolics_le_of_local_calculations`, retaining just its explicit tau-normalizer
premise for the geometric assembly. This local conclusion needs neither SQTK,
G = LT, the large-actor rank bound, nor containment of A in the socle.

Source: Aschbacher--Smith E.1.1--6 and E.1.14(1), printed pp.209--214;
the actual local structures and extensions are F.1.12, printed pp.263--264.
-/

public section

open Subgroup Theory.GroupTheory Matrix.PSL3.LinearThree
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.InnerFamilies

variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

private theorem quotient_rank_of_normalized_sl2 (H U : Subgroup G)
    (hU : IsPGroup 2 U) (hn : U ≤ normalizer H)
    (e : (H ⧸ pCore 2 H) ≃* SL(2,F))
    {f : ℕ} (hf : 2 ≤ f) (hF : Nat.card F = 2^f)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hAJ : A ≤ H ⊔ U)
    (hR : solvableRadical (H ⊔ U : Subgroup G) = pCore 2 (H ⊔ U : Subgroup G)) :
    Group.rank ((A.subgroupOf (H ⊔ U)).map
      (QuotientGroup.mk' (solvableRadical (H ⊔ U : Subgroup G)))) ≤ f := by
  have hz : center (H ⧸ pCore 2 H) = ⊥ := by
    apply (center _).eq_bot_iff_forall.mpr
    intro x hx
    apply e.injective
    have h := (Subgroup.centerCongr e ⟨x,hx⟩).property
    change e x ∈ center SL(2,F) at h
    rw [Theory.PSL2.sl2_center_eq_bot] at h
    simpa only [mem_bot, map_one] using h
  let er := (QuotientGroup.quotientMulEquivOfEq hR).trans
    (pCoreJoinQuotientEquivRange 2 hn hU hz)
  let ι := (MulAut.congr e).toMonoidHom.comp
    ((pCoreJoinAction 2 hn).range.subtype.comp er.toMonoidHom)
  have hi : Function.Injective ι :=
    (MulAut.congr e).injective.comp (Subtype.val_injective.comp er.injective)
  let a := (A.subgroupOf (H ⊔ U)).map
    (QuotientGroup.mk' (solvableRadical (H ⊔ U : Subgroup G)))
  let := hA
  let : IsElementaryAbelian 2 (A.subgroupOf (H ⊔ U)) := IsElementaryAbelian.subgroupOf hAJ
  let : IsElementaryAbelian 2 a := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (a.map ι) := IsElementaryAbelian.map _
  calc
    Group.rank a = Group.rank (a.map ι) :=
      Group.rank_congr (a.equivMapOfInjective ι hi)
    _ ≤ primeRank 2 (MulAut SL(2,F)) :=
      (a.map ι).rank_le_primeRank 2 (IsElementaryAbelian.isPGroup 2 _)
    _ ≤ f := Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le hf hF

/-- Normalized two-extensions of a perfect SL₂ local satisfy E2, provided the
actor survives the actual core of the extension. The quotient-rank proof
includes outer field actors. -/
theorem isEMemberAt_of_perfect_sl2_two_extension
    (T : Sylow 2 G) (H U : Subgroup G) [Group.IsPerfect H]
    (hUT : U ≤ (T : Subgroup G)) (hn : U ≤ normalizer H)
    (e : (H ⧸ pCore 2 H) ≃* SL(2,F))
    {f : ℕ} (hf : 2 ≤ f) (hF : Nat.card F = 2^f)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup G)) (hAJ : A ≤ H ⊔ U)
    (htau : tau (T : Subgroup G) A ≤ H ⊔ U)
    (hSyl : ∃ S : Sylow 2 H, (S : Subgroup H) = (T : Subgroup G).subgroupOf H)
    (hne : ¬ A.subgroupOf (H ⊔ U) ≤ pCore 2 (H ⊔ U : Subgroup G)) :
    IsEMemberAt f (T : Subgroup G) A (H ⊔ U) := by
  have hcard : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show 2^2 ≤ 2^f from Nat.pow_le_pow_right (by decide) hf)
  let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := F) hcard
  let : IsSimpleGroup SL(2,F) := (Theory.PSL2.sl2QuotientEquiv F).isSimpleGroup
  let : IsSimpleGroup (H ⧸ pCore 2 H) := e.isSimpleGroup
  let J := H ⊔ U
  let D := H.subgroupOf J
  let eD : D ≃* H := subgroupOfEquivOfLe le_sup_left
  let : D.Normal := normal_subgroupOf_of_le_normalizer (sup_le H.le_normalizer hn)
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective
    (f := eD.symm.toMonoidHom) eD.symm.surjective
  let eqD := QuotientGroup.congr (pCore 2 D) (pCore 2 H) eD (pCore_map_iso 2 eD)
  let : IsSimpleGroup (D ⧸ pCore 2 D) := eqD.isSimpleGroup
  have hRD : solvableRadical D = pCore 2 D := radical_eq_core_of_perfect_simple_core_quotient
  let erD := QuotientGroup.quotientMulEquivOfEq hRD
  let : IsSimpleGroup (D ⧸ solvableRadical D) := erD.isSimpleGroup
  have hgen : D ⊔ U.subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup (show H ≤ J from le_sup_left) (show U ≤ J from le_sup_right)]
    exact subgroupOf_self J
  have hU : IsPGroup 2 U := T.isPGroup'.to_le hUT
  have hq : IsPGroup 2 (J ⧸ D) :=
    isPGroup_quotient_of_sup_eq_top D (U.subgroupOf J) hU.comap_subtype hgen
  have hR : solvableRadical J = pCore 2 J :=
    radical_eq_core_of_normal_two_quotient D (hRD ▸ pCore_isPGroup) hq
  let Q := J ⧸ solvableRadical J
  let q := QuotientGroup.mk' (solvableRadical J)
  let C := D.map q
  let : C.Normal := (inferInstance : D.Normal).map q (QuotientGroup.mk'_surjective _)
  let ec := normalRadicalQuotientEquivImage D
  let : IsSimpleGroup C := ec.symm.isSimpleGroup
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective (q.subgroupMap_surjective D)
  have hz : center C = ⊥ := by
    rcases (inferInstance : (center C).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative C (center_eq_top_iff.mp h)).elim
  let : IsQuasisimple C := ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  have hqC : IsPGroup 2 (Q ⧸ C) := normal_radical_image_two_quotient D hq
  have hc : IsComponent Q C := ⟨(inferInstance : C.Normal).isSubnormal, inferInstance⟩
  have hl := (SimpleSocle.layer_residuals C hqC).1
  have hcentral := centralizer_eq_bot_of_simple_two_quotient C
    (Group.IsPerfect.not_isMulCommutative C) hqC
    (SimpleSocle.pCore_eq_bot solvableRadical_quotient_solvableRadical 2)
  have ha : (A.subgroupOf J).map q ≠ ⊥ := by
    intro he
    apply hne
    have hh := (Subgroup.map_eq_bot_iff _).mp he
    simpa only [q, QuotientGroup.ker_mk', hR] using hh
  have hclosed : IsTwoClosed (solvableRadical J) := by
    have hp : IsPGroup 2 (solvableRadical J) := hR ▸ pCore_isPGroup
    obtain ⟨S,hS⟩ := (hp.to_subgroup ⊤).exists_le_sylow
    have he : (S : Subgroup (solvableRadical J)) = ⊤ := top_unique hS
    exact ⟨S, he ▸ inferInstance⟩
  apply RankOneUpper.isEMemberAt_of_normal_quotient_component
    (T : Subgroup G) A J hA hAT hAJ htau
    (T.exists_subgroupOf_sup_of_normalized H U hUT hn hSyl) hclosed _
    (pResidual_eq_solvableResidual_of_perfect_sup_twoGroup H U hU hn) C hc hl
    (SimpleSocle.commutator_eq C hcentral _ ha)
    (quotient_rank_of_normalized_sl2 H U hU hn e hf hF A hA hAJ hR)
  rw [hl]
  exact ⟨inferInstance,hqC⟩

/-- The nonbinary source application leaves only equality of the two embedded
cores to the actual PSL₃ outer-extension calculation. -/
theorem tauJoin_isEMemberAt_of_core_eq
    (L : Subgroup G) (e : L ≃* PSL(3,F)) (T : Sylow 2 G)
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2^f)
    (halign : (unipotent F).map (linearThreeEmbedding L e) ≤ (T : Subgroup G))
    (b : Bool) (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup G)) (hne : ¬ A ≤ coreImage L e b)
    (hn : tau (T : Subgroup G) A ≤ normalizer (localImage L e b : Set G))
    (hcore : (pCore 2 (localImage L e b ⊔ tau (T : Subgroup G) A : Subgroup G)).map
      (localImage L e b ⊔ tau (T : Subgroup G) A).subtype = coreImage L e b) :
    IsEMemberAt f (T : Subgroup G) A (localImage L e b ⊔ tau (T : Subgroup G) A) := by
  have hcard : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show 2^2 ≤ 2^f from Nat.pow_le_pow_right (by decide) hf)
  let E : localModel F b ≃* localImage L e b :=
    (localModel F b).equivMapOfInjective (linearThreeEmbedding L e) (embedding_injective L e)
  have hp : Group.IsPerfect (localModel F b) := by
    cases b
    · exact lineLocal_isPerfect F hcard
    · exact pointLocal_isPerfect F hcard
  let := hp
  let : Group.IsPerfect (localImage L e b) :=
    Group.IsPerfect.ofSurjective (f := E.toMonoidHom) E.surjective
  have heq : Nonempty ((localModel F b ⧸ pCore 2 (localModel F b)) ≃* SL(2,F)) := by
    cases b
    · exact ⟨lineLocalCoreQuotientEquiv F⟩
    · exact ⟨pointLocalCoreQuotientEquiv F⟩
  obtain ⟨eq⟩ := heq
  let eq' := (QuotientGroup.congr _ _ E (pCore_map_iso 2 E)).symm.trans eq
  let := hA
  have hAJ : A ≤ localImage L e b ⊔ tau (T : Subgroup G) A :=
    (le_sup_left.trans (sup_pCore_le_tau T A hAT)).trans le_sup_right
  apply isEMemberAt_of_perfect_sl2_two_extension T (localImage L e b)
    (tau (T : Subgroup G) A) (tau_le _ _) hn eq' hf hF A hA hAT hAJ le_sup_right
    (localImage_sylow L e T (by omega) hF halign b)
  intro h
  apply hne
  calc
    A = (A.subgroupOf (localImage L e b ⊔ tau (T : Subgroup G) A)).map
        (localImage L e b ⊔ tau (T : Subgroup G) A).subtype :=
      (map_subgroupOf_eq_of_le hAJ).symm
    _ ≤ (pCore 2 (localImage L e b ⊔ tau (T : Subgroup G) A : Subgroup G)).map
        (localImage L e b ⊔ tau (T : Subgroup G) A).subtype := map_mono h
    _ = coreImage L e b := hcore

omit [CharP F 2] in
/-- The actual tau-enlarged local E-member for a simple PSL₃ generalized
Fitting subgroup. Normalization of the local suffices in both field-size
branches, with no assumption that the elementary actor lies in the socle.
In particular this supplies `hmember` in `parabolics_le_of_local_calculations`
under all the source hypotheses of E.1.14(1). -/
theorem tauJoin_isEMemberAt [IsSimpleGroup (generalizedFitting G)]
    (e : generalizedFitting G ≃* PSL(3,F)) (T : Sylow 2 G)
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (halign : (unipotent F).map (linearThreeEmbedding (generalizedFitting G) e) ≤
      (T : Subgroup G))
    (b : Bool) (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup G)) (hne : ¬ A ≤ coreImage (generalizedFitting G) e b)
    (hn : tau (T : Subgroup G) A ≤
      normalizer (localImage (generalizedFitting G) e b : Set G)) :
    IsEMemberAt f (T : Subgroup G) A
      (localImage (generalizedFitting G) e b ⊔ tau (T : Subgroup G) A) := by
  by_cases hf1 : f = 1
  · subst f
    have hF2 : Nat.card F = 2 := by simpa only [pow_one] using hF
    have htau := AmbientCores.tau_le_localImage_of_card_two e T hF2 b A hn
    rw [sup_eq_left.mpr htau]
    exact localImage_binary_isEMemberAt (generalizedFitting G) e hF2 T halign
      b A hA hAT htau hne
  · let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact tauJoin_isEMemberAt_of_core_eq (generalizedFitting G) e T (by omega)
      hF halign b A hA hAT hne hn (AmbientCores.tauJoin_core_eq e T hf hF b A hn)

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.InnerFamilies
