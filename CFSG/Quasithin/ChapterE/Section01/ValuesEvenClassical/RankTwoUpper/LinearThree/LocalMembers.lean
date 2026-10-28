module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.Assembly
public import Theory.SpecificGroups.PSL3.LinearThreeLocalStructure
public import Theory.SpecificGroups.PSL3.LinearThreeSylow
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.SpecificGroups.SL2.NormalMonolith
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Theory.GroupTheory.SolvableRadical.Transport
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.ElementaryAbelian.GeneratorRank

/-!
# Actual PSL₃ local E-members

For a perfect finite subgroup H whose two-core quotient is SL₂(F), with
|F| = 2^f ≥ 4, the solvable radical equals the two-core. Its simple quotient
is its single component and its layer, while O²(H) = H∞ = H. A nontrivial
quotient image of A acts nontrivially on that component. The elementary
quotient image has order at most |F| by the actual SL₂ Sylow calculation,
so its generator rank is at most f. This checks every E2 clause, including
the local tau orbit and the intrinsic radical quotient.

The final two applications use the literal point and line local groups of
PSL₃(F), their proved quotient equivalences, and the standard matrix Sylow.
Their E0 tau containment follows from containment of that Sylow in each local.
The binary field and enlargement by outer automorphisms require further
calculations; no upper E-generation theorem is asserted by these applications.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.1--5 and the PSL₃ case of E.1.14(1), printed pp.209--210, 214;
the affine local structure is described in F.1.12, printed pp.263--264.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree

private theorem radical_eq_core {H : Type*} [Group H] [Finite H]
    [Group.IsPerfect H] [IsSimpleGroup (H ⧸ pCore 2 H)] :
    solvableRadical H = pCore 2 H := by
  let Q := H ⧸ pCore 2 H
  let q : H →* Q := QuotientGroup.mk' (pCore 2 H)
  let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hR : solvableRadical Q = ⊥ := by
    rcases (inferInstance : (solvableRadical Q).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · have hs : Group.IsSolvable (⊤ : Subgroup Q) := h ▸ inferInstance
      let := hs
      exact (Group.IsPerfect.not_isSolvable Q
        (Group.isSolvable_of_surjective
          (f := (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q).toMonoidHom)
          Subgroup.topEquiv.surjective)).elim
  apply le_antisymm
  · have h := map_solvableRadical_le_of_surjective q (QuotientGroup.mk'_surjective _)
    rw [hR] at h
    intro x hx
    exact (QuotientGroup.eq_one_iff x).mp
      ((Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp h) hx)
  · let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
    exact le_solvableRadical _ inferInstance inferInstance

private theorem residual_eq_of_perfect {H : Type*} [Group H] [Finite H]
    [Group.IsPerfect H] : pResidual 2 H = solvableResidual H := by
  rw [solvableResidual_eq_top, pResidual_eq_top_iff]
  intro N hN hq
  let := hN
  by_contra hn
  let : Nontrivial (H ⧸ N) := QuotientGroup.nontrivial_iff.mpr hn
  let : Group.IsPerfect (H ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (H ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (H ⧸ N) inferInstance

private theorem simple_top_commutator {Q : Type*} [Group Q] [IsSimpleGroup Q]
    [Group.IsPerfect Q] (a : Subgroup Q) (ha : a ≠ ⊥) :
    (⊤ : Subgroup Q) = ⁅(⊤ : Subgroup Q), a⁆ := by
  have hz : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp h)).elim
  let : (⁅(⊤ : Subgroup Q), a⁆).Normal :=
    normalizer_eq_top_iff.mp (top_unique (normalizer_commutator_ge_left ⊤ a))
  rcases (inferInstance : (⁅(⊤ : Subgroup Q), a⁆).Normal).eq_bot_or_eq_top with h | h
  · exact (ha (le_bot_iff.mp (hz ▸ commutator_top_left_eq_bot_iff_le_center.mp h))).elim
  · exact h.symm

variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

private theorem rank_image_le (H : Type*) [Group H] [Finite H]
    (e : H ≃* SL(2,F)) (a : Subgroup H) [IsElementaryAbelian 2 a]
    {f : ℕ} (hF : Nat.card F = 2^f) : Group.rank a ≤ f := by
  apply IsElementaryAbelian.rank_le_of_card_le (p := 2)
  obtain ⟨S, hS⟩ := (IsElementaryAbelian.isPGroup (p := 2) (G := a)).map e.toMonoidHom |>.exists_le_sylow
  calc
    Nat.card a = Nat.card (a.map e.toMonoidHom) :=
      Nat.card_congr (a.equivMapOfInjective e.toMonoidHom e.injective).toEquiv
    _ ≤ Nat.card S := Nat.card_le_card_of_injective (Subgroup.inclusion hS) (Subgroup.inclusion_injective hS)
    _ = Nat.card (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2) :=
      Nat.card_congr (S.equiv (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2)).toEquiv
    _ = 2^f := (Matrix.SpecialLinearGroup.card_upperUnipotent F).trans hF

/-- A perfect local group with the actual simple SL₂ quotient supplies E2. -/
theorem isEMemberAt_of_perfect_sl2_quotient (T A H : Subgroup G)
    [Group.IsPerfect H] (hcard : 4 ≤ Nat.card F)
    (e : (H ⧸ pCore 2 H) ≃* SL(2,F)) {f : ℕ} (hF : Nat.card F = 2^f)
    (hA : IsElementaryAbelian 2 A) (hAT : A ≤ T) (hAH : A ≤ H)
    (htau : tau T A ≤ H)
    (hSyl : ∃ S : Sylow 2 H, (S : Subgroup H) = T.subgroupOf H)
    (hne : ¬ A.subgroupOf H ≤ pCore 2 H) : IsEMemberAt f T A H := by
  let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := F) hcard
  let : IsSimpleGroup SL(2,F) := (Theory.PSL2.sl2QuotientEquiv F).isSimpleGroup
  let : IsSimpleGroup (H ⧸ pCore 2 H) := e.isSimpleGroup
  have hR := radical_eq_core (H := H)
  let Q := H ⧸ solvableRadical H
  let er : Q ≃* (H ⧸ pCore 2 H) := QuotientGroup.quotientMulEquivOfEq hR
  let : IsSimpleGroup Q := er.isSimpleGroup
  let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hz : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp h)).elim
  let : IsQuasisimple Q := ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  let : IsQuasisimple (⊤ : Subgroup Q) := IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm
  have hc : IsComponent Q ⊤ := ⟨.top, inferInstance⟩
  have hl : componentLayer Q = ⊤ := top_unique (le_sSup hc)
  have hp : IsPGroup 2 (solvableRadical H) := hR ▸ pCore_isPGroup
  have hclosed : IsTwoClosed (solvableRadical H) := by
    obtain ⟨S, hS⟩ := (hp.to_subgroup (⊤ : Subgroup (solvableRadical H))).exists_le_sylow
    have he : (S : Subgroup (solvableRadical H)) = ⊤ := top_unique hS
    exact ⟨S, he ▸ inferInstance⟩
  let a : Subgroup Q := (A.subgroupOf H).map (QuotientGroup.mk' (solvableRadical H))
  have ha : a ≠ ⊥ := by
    intro h
    have hh := (Subgroup.map_eq_bot_iff _).mp h
    rw [QuotientGroup.ker_mk', hR] at hh
    exact hne hh
  let := hA
  let : IsElementaryAbelian 2 (A.subgroupOf H) :=
    IsElementaryAbelian.subgroupOf hAH
  let : IsElementaryAbelian 2 a := IsElementaryAbelian.map _
  apply RankOneUpper.isEMemberAt_of_normal_quotient_component T A H hA hAT hAH htau hSyl
    hclosed _ residual_eq_of_perfect ⊤ hc hl (simple_top_commutator a ha)
  · exact rank_image_le Q (er.trans e) a hF
  · rw [hl]
    let : Subsingleton (Q ⧸ (⊤ : Subgroup Q)) := QuotientGroup.subsingleton_quotient_top
    exact ⟨inferInstance, IsPGroup.of_subsingleton 2 _⟩

open Matrix.PSL3.LinearThree

/-- The point local is an E-member whenever the actor is nontrivial modulo
its actual root-plane core. No ambient tau-containment premise is needed. -/
theorem pointLocal_isEMemberAt (hcard : 4 ≤ Nat.card F)
    {f : ℕ} (hF : Nat.card F = 2^f) (hf : 0 < f)
    (A : Subgroup PSL(3,F)) (hA : IsElementaryAbelian 2 A)
    (hAS : A ≤ unipotent F)
    (hne : ¬ A.subgroupOf (pointLocal F) ≤ pCore 2 (pointLocal F)) :
    IsEMemberAt f (unipotent F) A (pointLocal F) := by
  let := pointLocal_isPerfect F hcard
  exact isEMemberAt_of_perfect_sl2_quotient (unipotent F) A (pointLocal F)
    hcard (pointLocalCoreQuotientEquiv F) hF hA hAS
    (hAS.trans (unipotent_le_pointLocal F))
    ((tau_le _ _).trans (unipotent_le_pointLocal F))
    ⟨(unipotentSylow F hf hF).subtype (unipotent_le_pointLocal F), rfl⟩ hne

/-- The line-local counterpart uses the other literal root-plane kernel. -/
theorem lineLocal_isEMemberAt (hcard : 4 ≤ Nat.card F)
    {f : ℕ} (hF : Nat.card F = 2^f) (hf : 0 < f)
    (A : Subgroup PSL(3,F)) (hA : IsElementaryAbelian 2 A)
    (hAS : A ≤ unipotent F)
    (hne : ¬ A.subgroupOf (lineLocal F) ≤ pCore 2 (lineLocal F)) :
    IsEMemberAt f (unipotent F) A (lineLocal F) := by
  let := lineLocal_isPerfect F hcard
  exact isEMemberAt_of_perfect_sl2_quotient (unipotent F) A (lineLocal F)
    hcard (lineLocalCoreQuotientEquiv F) hF hA hAS
    (hAS.trans (unipotent_le_lineLocal F))
    ((tau_le _ _).trans (unipotent_le_lineLocal F))
    ⟨(unipotentSylow F hf hF).subtype (unipotent_le_lineLocal F), rfl⟩ hne

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree
