module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.Assembly
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import CFSG.Quasithin.ChapterE.Section01.Inheritance
public import Theory.SpecificGroups.SymplecticFour.Sylow
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.ElementaryAbelian.GeneratorRank
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Nonbinary symplectic E-generation

For each of the two actual determinant kernels, perfectness and the simple
SL₂ core quotient identify the solvable radical with the two-core. They also
identify the two-residual and solvable residual and verify the component
clause with the literal local tau orbit. The image of an elementary subgroup
in the radical quotient has rank at most the binary field exponent, since
an SL₂ Sylow subgroup has the order of the field.

Fix the standard Sylow subgroup and an invariant elementary family. If some
family member acts nontrivially on a local quotient, that determinant kernel
is an E-member. Otherwise the weak closure lies in the local two-core and
is normalized by that local factor. The Borel normalizes the weak closure
as well, so the two full parabolics give generation.

This proves the intrinsic Sp₄(2^f) case for f > 1. Binary derived groups and
proper outer extensions are separate cases; no claim about them is made here.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.1--E.1.6 and E.1.14(1), printed pp.209--211 and 214, with the concrete
local structure underlying F.1.12(I)(2), printed pp.262--264.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour

private theorem radical_eq_core {K : Type*} [Group K] [Finite K]
    [IsSimpleGroup (K ⧸ pCore 2 K)] [Group.IsPerfect (K ⧸ pCore 2 K)] :
    solvableRadical K = pCore 2 K := by
  have hr : solvableRadical (K ⧸ pCore 2 K) = ⊥ := by
    rcases (inferInstance : (solvableRadical (K ⧸ pCore 2 K)).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · have hs : Group.IsSolvable (K ⧸ pCore 2 K) := by
        exact Group.isSolvable_of_surjective
          (f := (solvableRadical (K ⧸ pCore 2 K)).subtype)
          (by intro q; exact ⟨⟨q, h.symm ▸ Subgroup.mem_top q⟩, rfl⟩)
      exact (Group.IsPerfect.not_isSolvable _ hs).elim
  have : Group.IsSolvable (QuotientGroup.mk' (pCore 2 K)).ker := by
    rw [QuotientGroup.ker_mk']
    let : Group.IsNilpotent (pCore 2 K) := pCore_isPGroup.isNilpotent
    infer_instance
  rw [← comap_solvableRadical_eq_of_solvable_ker (QuotientGroup.mk' (pCore 2 K))
    (QuotientGroup.mk'_surjective _), hr]
  exact QuotientGroup.ker_mk' _

private theorem simple_commutator {Q : Type*} [Group Q] [IsSimpleGroup Q]
    [Group.IsPerfect Q] (A : Subgroup Q) (ha : A ≠ ⊥) :
    (⊤ : Subgroup Q) = ⁅(⊤ : Subgroup Q), A⁆ := by
  have hc : ⁅(⊤ : Subgroup Q), A⁆.Normal :=
    normalizer_eq_top_iff.mp (top_unique (normalizer_commutator_ge_left _ _))
  have hz : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · let := center_eq_top_iff.mp h
      exact (Group.IsPerfect.not_isSolvable Q inferInstance).elim
  apply Eq.symm
  apply hc.eq_bot_or_eq_top.resolve_left
  intro h
  apply ha
  rw [commutator_comm] at h
  have hle := commutator_eq_bot_iff_le_centralizer.mp h
  simpa only [centralizer_univ, coe_top, hz, le_bot_iff] using hle

private theorem twoClosed_of_isPGroup {K : Type*} [Group K] (h : IsPGroup 2 K) :
    IsTwoClosed K := by
  let S : Sylow 2 K := (h.to_subgroup ⊤).toSylow (by simp)
  exact ⟨S, inferInstanceAs (⊤ : Subgroup K).Normal⟩

/-- All E2 clauses for a perfect local group with simple core quotient. -/
theorem eCaseComponent_of_perfect_simple_quotient
    {G : Type*} [Group G] [Finite G] (T A K : Subgroup G)
    [Group.IsPerfect K] [IsSimpleGroup (K ⧸ pCore 2 K)]
    [Group.IsPerfect (K ⧸ pCore 2 K)]
    (hA : ¬ A.subgroupOf K ≤ pCore 2 K) : ECaseComponent T A K := by
  have hrad := radical_eq_core (K := K)
  have he : IsSimpleGroup (K ⧸ solvableRadical K) := (QuotientGroup.quotientMulEquivOfEq hrad).isSimpleGroup
  let := he
  have hp : Group.IsPerfect (K ⧸ solvableRadical K) := inferInstance
  let Q := K ⧸ solvableRadical K
  have hz : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · let := center_eq_top_iff.mp h
      exact (Group.IsPerfect.not_isSolvable Q inferInstance).elim
  let : IsQuasisimple Q := ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  let : IsQuasisimple (⊤ : Subgroup Q) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have hcomp : IsComponent Q ⊤ := ⟨(inferInstance : (⊤ : Subgroup Q).Normal).isSubnormal,
    inferInstance⟩
  have hlayer : componentLayer Q = ⊤ := top_unique (le_sSup hcomp)
  have hr : pResidual 2 K = solvableResidual K := by
    rw [solvableResidual_eq_top]
    apply (pResidual_eq_top_iff _ _).mpr
    intro N hN hNq
    let := hN
    apply top_unique
    intro k _
    apply (QuotientGroup.eq_one_iff k).mp
    by_contra h
    have : Nontrivial (K ⧸ N) := ⟨⟨QuotientGroup.mk k, 1, h⟩⟩
    exact Group.IsPerfect.not_isNilpotent _ hNq.isNilpotent
  have ha : (A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K)) ≠ ⊥ := by
    intro h
    apply hA
    have hh := (Subgroup.map_eq_bot_iff _).mp h
    simpa only [QuotientGroup.ker_mk', hrad] using hh
  refine ⟨?_, ?_, hr, ⊤, hcomp, ?_, Or.inl (simple_commutator _ ha)⟩
  · rw [hrad]
    exact twoClosed_of_isPGroup pCore_isPGroup
  · change HasTwoGroupQuotient (componentLayer Q)
    rw [hlayer]
    let := QuotientGroup.subsingleton_quotient_top (G := Q)
    exact ⟨inferInstance, IsPGroup.of_subsingleton 2 _⟩
  · change componentLayer Q = conjugateJoin _ ⊤
    rw [RankOneUpper.conjugateJoin_eq_of_normal, hlayer]

open Theory.SpecificGroups.SymplecticFour

private theorem rank_SL2_image {F : Type*} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) [IsElementaryAbelian 2 A] :
    Group.rank A ≤ f := by
  obtain ⟨S, hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  apply IsElementaryAbelian.rank_le_of_card_le (p := 2)
  calc
    Nat.card A ≤ Nat.card S := Nat.card_le_card_of_injective (Subgroup.inclusion hAS) (Subgroup.inclusion_injective hAS)
    _ = Nat.card F := Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 S).toEquiv.symm
    _ = 2 ^ f := hF

/-- The literal radical quotient image has rank at most the field exponent. -/
theorem local_quotient_rank {G F : Type*} [Group G] [Finite G]
    [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hf : 1 < f) (A K : Subgroup G) [IsElementaryAbelian 2 A]
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    [Group.IsPerfect K] (hAK : A ≤ K) :
    Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K))) ≤ f := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (show 2 ^ 1 < 2 ^ f from Nat.pow_lt_pow_right (by decide) hf)
  let := NaturalExtension.model_simple hq
  let : IsSimpleGroup (K ⧸ pCore 2 K) := e.isSimpleGroup
  let r : (K ⧸ solvableRadical K) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq (radical_eq_core (K := K))).trans e
  let a := (A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K))
  have : IsElementaryAbelian 2 (A.subgroupOf K) := IsElementaryAbelian.subgroupOf hAK
  have : IsElementaryAbelian 2 a := IsElementaryAbelian.map _
  have : IsElementaryAbelian 2 (a.map r.toMonoidHom) := IsElementaryAbelian.map _
  calc
    Group.rank a = Group.rank (a.map r.toMonoidHom) :=
      Group.rank_congr (Subgroup.equivMapOfInjective a r.toMonoidHom r.injective)
    _ ≤ f := rank_SL2_image hF _

/-- A perfect local with an actual SL₂ core quotient is an E-member whenever
an elementary subgroup of the Sylow acts nontrivially on that quotient. -/
theorem isEMemberAt_local {G F : Type*} [Group G] [Finite G]
    [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hf : 1 < f) (T : Sylow 2 G) (A K : Subgroup G)
    [IsElementaryAbelian 2 A] [Group.IsPerfect K]
    (hAT : A ≤ (T : Subgroup G)) (hTK : (T : Subgroup G) ≤ K)
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hA : ¬ A.subgroupOf K ≤ pCore 2 K) :
    IsEMemberAt f (T : Subgroup G) A K := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (show 2 ^ 1 < 2 ^ f from Nat.pow_lt_pow_right (by decide) hf)
  let := NaturalExtension.model_simple hq
  let : IsSimpleGroup (K ⧸ pCore 2 K) := e.isSimpleGroup
  have hc := eCaseComponent_of_perfect_simple_quotient (T : Subgroup G) A K hA
  exact ⟨⟨inferInstance, hAT, hAT.trans hTK,
    le_inf (tau_le _ _) ((tau_le _ _).trans hTK), ⟨T.subtype hTK, rfl⟩, Or.inr hc⟩,
    Or.inr ⟨hc, local_quotient_rank hF hf A K e (hAT.trans hTK)⟩⟩

/-- Either the local is an E-member for some family member, or its normal
core contains the weak closure and the local normalizes that weak closure. -/
theorem local_le_eFamily_sup_normalizer {G : Type*} [Group G] [Finite G]
    {i : ℕ} (T : Subgroup G) (K Q : Subgroup G) (hQT : Q ≤ T)
    (hKQ : K ≤ normalizer (Q : Set G))
    (hm : ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ T → ¬ A ≤ Q →
      IsEMemberAt i T A K)
    (Ω : Set (Subgroup G)) (hΩ : IsElementaryFamily Ω) :
    K ≤ eFamilySubgroup i T Ω ⊔ normalizer (weakClosure T Ω : Set G) := by
  classical
  by_cases hex : ∃ A : Subgroup G, A ∈ Ω ∧ A ≤ T ∧ ¬ A ≤ Q
  · obtain ⟨A, hA, hAT, hAQ⟩ := hex
    exact (show K ≤ eSubgroup i T A from le_sSup (hm A (hΩ.1 A hA) hAT hAQ)).trans
      ((le_iSup (fun B : {B : Subgroup G // B ∈ Ω ∧ B ≤ T} => eSubgroup i T B.1)
        ⟨A, hA, hAT⟩).trans le_sup_left)
  · have hW : weakClosure T Ω ≤ Q := by
      apply sSup_le
      rintro A ⟨hA, hAT⟩
      by_contra h
      exact hex ⟨A, hA, hAT, h⟩
    have he : weakClosure T Ω = weakClosure Q Ω := le_antisymm
      (SubgroupFamily.span_le_span_of_span_le hW) (SubgroupFamily.span_mono Ω hQT)
    rw [he]
    exact (hKQ.trans (RankOneUpper.normalizer_le_weakClosure_normalizer Q hΩ)).trans
      le_sup_right

private theorem local_core_normalized {G : Type*} [Group G] (K : Subgroup G) :
    K ≤ normalizer ((pCore 2 K).map K.subtype : Set G) := by
  intro k hk
  apply Subgroup.le_normalizer_map K.subtype
  exact ⟨⟨k, hk⟩, by rw [normalizer_eq_top]; trivial, rfl⟩

private theorem local_core_le_sylow {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (K : Subgroup G) (hTK : (T : Subgroup G) ≤ K) :
    (pCore 2 K).map K.subtype ≤ T := by
  have h := (pCore_isPGroup (p := 2) (G := K)).le_sylow_of_normal (T.subtype hTK)
  exact (map_mono h).trans (by simp [Subgroup.map_subgroupOf_eq_of_le hTK])

/-- Each nonbinary determinant kernel is available to the generation proof,
including the branch in which it normalizes the weak closure. -/
theorem perfect_SL2_local_le_generated {G F : Type*} [Group G] [Finite G]
    [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hf : 1 < f) (T : Sylow 2 G) (K : Subgroup G)
    [Group.IsPerfect K] (hTK : (T : Subgroup G) ≤ K)
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (Ω : Set (Subgroup G)) (hΩ : IsElementaryFamily Ω) :
    K ≤ eFamilySubgroup f (T : Subgroup G) Ω ⊔
      normalizer (weakClosure (T : Subgroup G) Ω : Set G) := by
  apply local_le_eFamily_sup_normalizer (T : Subgroup G) K ((pCore 2 K).map K.subtype)
    (local_core_le_sylow T K hTK) (local_core_normalized K) _ Ω hΩ
  intro A hA hAT hAQ
  let := hA
  apply isEMemberAt_local hF hf T A K hAT hTK e
  intro h
  apply hAQ
  rw [← Subgroup.map_subgroupOf_eq_of_le (hAT.trans hTK)]
  exact map_mono h

/-- The full symplectic matrix group is E-generated for every nonbinary
field of characteristic two. This theorem has no outer-action hypothesis. -/
theorem isEGenerated_sp_nonbinary {F : Type*} [Field F] [Finite F]
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 < f) : IsEGenerated f (Sp F) := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let T := unipotentSylow hF (by omega : 1 ≤ f)
  have hpoint : (T : Subgroup (Sp F)) ≤ pointLocal := inf_le_left
  have hplane : (T : Subgroup (Sp F)) ≤ planeLocal := inf_le_right
  let := pointLocal_perfect hF hf
  let := planeLocal_perfect hF hf
  apply IsEGeneratedAt.isEGenerated (T := T)
  intro Ω hΩ
  have h1 := perfect_SL2_local_le_generated hF hf T pointLocal hpoint
    (pointLocalCoreQuotientEquiv hF hf) Ω hΩ
  have h2 := perfect_SL2_local_le_generated hF hf T planeLocal hplane
    (planeLocalCoreQuotientEquiv hF hf) Ω hΩ
  have hB : borel (F := F) ≤ eFamilySubgroup f (T : Subgroup (Sp F)) Ω ⊔
      normalizer (weakClosure (T : Subgroup (Sp F)) Ω : Set (Sp F)) := by
    rw [borel_eq_normalizer_unipotent]
    exact (RankOneUpper.normalizer_le_weakClosure_normalizer (T : Subgroup (Sp F)) hΩ).trans
      le_sup_right
  apply top_unique
  rw [← parabolics_sup_eq_top (F := F), pointParabolic_eq_pointLocal_sup_borel,
    planeParabolic_eq_planeLocal_sup_borel]
  exact sup_le (sup_le h1 hB) (sup_le h2 hB)

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour
