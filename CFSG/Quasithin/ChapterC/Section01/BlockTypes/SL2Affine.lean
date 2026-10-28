module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.SpecificGroups.SL2.Affine.Action
public import Theory.SpecificGroups.SL2.Affine.Core
public import Theory.Representation.SL2NaturalFirstCohomology
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Natural L₂-blocks from affine coordinates

An isomorphism with the special affine plane group identifies the two-core
with translations. The natural action is irreducible even on additive
subgroups, and it is nontrivial. Consequently its commutator layer is the
whole translation plane and has no central fixed points. These identities
construct the literal quotient and module isomorphisms, with conjugation
intertwining the natural matrix action.

The final constructor is conditional only on perfectness and the equality
F*(L) = O₂(L). The local-group assembly supplies these two structural facts;
this module proves every other short-group clause and the natural-module
identification, without importing the separate affine structure development.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, C.1.7 and C.1.12, printed pp.123–124;
application to the L₃(q) local groups in F.1.12(I)(1), printed pp.262–264.
-/

@[expose] public section

open Subgroup Theory.GroupTheory Matrix Matrix.SL2
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.SL2Affine
variable {L : Type*} [Group L] {F : Type*} [Field F] [Finite F] [CharP F 2]
variable (e : L ≃* Affine F)
include e

/-- Vector coordinates on the actual two-core, transported through the given affine isomorphism. -/
noncomputable def coreEquiv : Multiplicative (Fin 2 → F) ≃* pCore 2 L :=
  (translationsEquiv F).trans ((e.symm.subgroupMap (translations F)).trans
    (MulEquiv.subgroupCongr (by rw [← affine_twoCore_eq F]; exact pCore_map_iso 2 e.symm)))

/-- The two-core coordinates retain the specified affine marking. -/
@[simp] theorem coreEquiv_apply (v : Multiplicative (Fin 2 → F)) :
    e (coreEquiv e v : L) = SemidirectProduct.inl v := by
  change e (e.symm _) = _
  simp

/-- Conjugation in L becomes the natural action of its affine linear part. -/
theorem coreEquiv_action (l : L) (v : Multiplicative (Fin 2 → F)) :
    (coreEquiv e (naturalAction F (e l).right v) : L) =
      l * (coreEquiv e v : L) * l⁻¹ := by
  apply e.injective
  simp only [map_mul, map_inv, coreEquiv_apply, conjugate_inl]

/-- Every L-normal subgroup inside its translation core is trivial or the full core. -/
theorem normal_core_dichotomy (N : Subgroup L) [N.Normal] (hle : N ≤ pCore 2 L) :
    N = ⊥ ∨ N = pCore 2 L := by
  let i := (pCore 2 L).subtype.comp (coreEquiv e).toMonoidHom
  have hV : ∀ g v, v ∈ N.comap i → naturalAction F g v ∈ N.comap i := by
    intro g v hv
    change (coreEquiv e (naturalAction F g v) : L) ∈ N
    have ha := coreEquiv_action e (e.symm (SemidirectProduct.inr g)) v
    simp only [MulEquiv.apply_symm_apply, SemidirectProduct.right_inr] at ha
    rw [ha]
    exact (inferInstance : N.Normal).conj_mem _ hv _
  rcases naturalAction_irreducible F (N.comap i) hV with h | h
  · left
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro x hx
    obtain ⟨v, hv⟩ := (coreEquiv e).surjective ⟨x, hle hx⟩
    have hm : v ∈ N.comap i := by change (coreEquiv e v : L) ∈ N; rw [hv]; exact hx
    have hv1 : v = 1 := by simpa [h] using hm
    have hh := congrArg Subtype.val hv
    simpa [hv1] using hh.symm
  · right
    apply le_antisymm hle
    intro x hx
    obtain ⟨v, hv⟩ := (coreEquiv e).surjective ⟨x, hx⟩
    have hm : v ∈ N.comap i := by rw [h]; trivial
    change (coreEquiv e v : L) ∈ N at hm
    simpa only [hv] using hm

/-- Faithfulness and a nonidentity transvection exclude a central translation plane. -/
theorem core_not_le_center : ¬ pCore 2 L ≤ center L := by
  intro h
  have ha (g : SL(2,F)) : naturalAction F g = 1 := by
    ext v : 1
    apply (coreEquiv e).injective
    apply Subtype.ext
    have hc := Subgroup.mem_center_iff.mp (h (coreEquiv e v).property)
      (e.symm (SemidirectProduct.inr g))
    have he := coreEquiv_action e (e.symm (SemidirectProduct.inr g)) v
    simp only [MulEquiv.apply_symm_apply, SemidirectProduct.right_inr] at he
    rw [he, hc, mul_inv_cancel_right]
    rfl
  have hall (g : SL(2,F)) : g = 1 :=
    naturalAction_injective F ((ha g).trans (map_one _).symm)
  let g : SL(2,F) := ⟨!![1,1;0,1], by simp [det_fin_two]⟩
  have hh := congrArg (fun a : SL(2,F) => a.val 0 1) (hall g)
  change (1 : F) = 0 at hh
  exact one_ne_zero hh

/-- The translation plane has no global fixed subgroup. -/
theorem core_inf_center : pCore 2 L ⊓ center L = ⊥ := by
  rcases normal_core_dichotomy e (pCore 2 L ⊓ center L) inf_le_left with h | h
  · exact h
  · exact (core_not_le_center e (h ▸ inf_le_right)).elim

/-- The source commutator U(L) is the whole two-core. -/
theorem blockU_eq_core : blockU L = pCore 2 L := by
  rcases normal_core_dichotomy e (blockU L) blockU_le_core with h | h
  · exact (core_not_le_center e ((commutator_top_right_eq_bot_iff_le_center).mp h)).elim
  · exact h

/-- Under the specified affine isomorphism, U(L) is exactly the translation plane. -/
theorem blockU_map : (blockU L).map e.toMonoidHom = translations F := by
  rw [blockU_eq_core e, pCore_map_iso, affine_twoCore_eq]

/-- The intrinsic fixed subgroup C_U(L) is trivial. -/
theorem fixed_eq_bot : blockFixed L = ⊥ := by
  apply Subgroup.map_injective (blockU L).subtype_injective
  rw [blockFixed_map, blockU_eq_core e, core_inf_center e, Subgroup.map_bot]

/-- The actual core quotient, with its prescribed linear part. -/
noncomputable def quotientEquiv : (L ⧸ pCore 2 L) ≃* SL(2,F) :=
  (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans (affineCoreQuotientEquiv F)

@[simp] theorem quotientEquiv_mk (l : L) :
    quotientEquiv e (QuotientGroup.mk' (pCore 2 L) l) = (e l).right := rfl

/-- The commutator layer is the full natural plane. -/
noncomputable def blockEquiv : blockU L ≃* Multiplicative (Fin 2 → F) :=
  (MulEquiv.subgroupCongr (blockU_eq_core e)).trans (coreEquiv e).symm

@[simp] theorem blockEquiv_inl (u : blockU L) :
    SemidirectProduct.inl (blockEquiv e u) = e (u : L) := by
  have h := coreEquiv_apply e (blockEquiv e u)
  simpa only [blockEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    MulEquiv.subgroupCongr_apply] using h.symm

theorem blockEquiv_conjugate (l : L) (u : blockU L) :
    blockEquiv e (blockConjugate L l u) = naturalAction F (e l).right (blockEquiv e u) := by
  apply (SemidirectProduct.inl_injective (φ := naturalAction F))
  rw [blockEquiv_inl, ← conjugate_inl, blockEquiv_inl]
  change e (l * (u : L) * l⁻¹) = _
  simp only [map_mul, map_inv]

/-- Quotienting the commutator layer by its trivial fixed subgroup gives the plane. -/
noncomputable def moduleEquiv : BlockModule L ≃* Multiplicative (Fin 2 → F) :=
  ((QuotientGroup.quotientMulEquivOfEq (fixed_eq_bot e)).trans
    QuotientGroup.quotientBot).trans (blockEquiv e)

@[simp] theorem moduleEquiv_mk (u : blockU L) :
    moduleEquiv e (QuotientGroup.mk' (blockFixed L) u) = blockEquiv e u := rfl

/-- The literal quotient and module identifications intertwine conjugation. -/
noncomputable def blockModuleModel : BlockModuleModel L (naturalAction F) where
  quotientIso := quotientEquiv e
  moduleIso := moduleEquiv e
  intertwining l u := by
    rw [moduleEquiv_mk, quotientEquiv_mk, moduleEquiv_mk]
    exact blockEquiv_conjugate e l u

/-- The precise normal-subgroup interval required in C.1.7 is irreducible. -/
theorem block_irreducible : BlockModuleIrreducible L := by
  have hi : blockU L ⊓ center L = ⊥ := by rw [blockU_eq_core e, core_inf_center e]
  constructor
  · rw [hi, bot_lt_iff_ne_bot, blockU_eq_core e]
    intro h
    exact core_not_le_center e (by rw [h]; exact bot_le)
  · intro N hN _ hle
    let := hN
    rw [blockU_eq_core e] at hle
    rw [hi, blockU_eq_core e]
    exact normal_core_dichotomy e N hle

/-- The commutator layer is elementary abelian in characteristic two. -/
theorem block_elementary : IsElementaryAbelian 2 (blockU L) :=
  IsElementaryAbelian.of_surjective (blockEquiv e).symm.toMonoidHom
    (blockEquiv e).symm.surjective

/-- The commutator layer centralizes the actual two-core. -/
theorem block_central : blockU L ≤ centralizer (pCore 2 L : Set L) := by
  intro u hu
  apply mem_centralizer_iff.mpr
  intro v hv
  obtain ⟨a, ha⟩ := (coreEquiv e).surjective ⟨u, blockU_le_core hu⟩
  obtain ⟨b, hb⟩ := (coreEquiv e).surjective ⟨v, hv⟩
  have hh := congrArg (fun w => (coreEquiv e w : L)) (mul_comm b a)
  simpa only [map_mul, Subgroup.coe_mul, ha, hb] using hh

/-- The two supplied structural premises complete all the short-group clauses. -/
theorem isShort (hcard : 4 ≤ Nat.card F) (hperfect : Group.IsPerfect L)
    (hfitting : generalizedFitting L = pCore 2 L) : IsShort L := by
  let : Finite (Affine F) := Finite.of_equiv
    (Multiplicative (Fin 2 → F) × SL(2,F)) SemidirectProduct.equivProd.symm
  let : Finite L := Finite.of_equiv (Affine F) e.symm.toEquiv
  let := hperfect
  have ht : IsPPerfect 2 L := by
    intro N hN hq
    let := hN
    by_contra hne
    let : Nontrivial (L ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (L ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (L ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (L ⧸ N) inferInstance
  have hq : IsQuasisimple (L ⧸ pCore 2 L) := by
    let : Group.IsPerfect (L ⧸ pCore 2 L) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
    let : Group.IsPerfect SL(2,F) :=
      Group.IsPerfect.ofSurjective (f := (quotientEquiv e).toMonoidHom)
        (quotientEquiv e).surjective
    let : IsQuasisimple SL(2,F) := {
      toIsPerfect := inferInstance
      simple := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcard }
    exact IsQuasisimple.of_mulEquiv (quotientEquiv e).symm
  exact ⟨inferInstance, ht, hfitting, block_elementary e, block_central e,
    Or.inl hq, block_irreducible e⟩

end CFSG.Quasithin.ChapterC.SL2Affine

namespace CFSG.Quasithin.ChapterC
open SL2Affine
variable {L : Type*} [Group L] {F : Type} [Field F] [Finite F] [CharP F 2]

/-- Construct an L₂(2^n)-block from affine coordinates and the two structural premises. -/
theorem isL2EvenBlock_of_affine {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : L ≃* Affine F) (hperfect : Group.IsPerfect L)
    (hfitting : generalizedFitting L = pCore 2 L) : IsL2EvenBlock L n := by
  have hc : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show 2 ^ 2 ≤ 2 ^ n from Nat.pow_le_pow_right (by decide) hn)
  refine ⟨hn, SL2Affine.isShort e hc hperfect hfitting, F, inferInstance, inferInstance,
    hF, ?_, ?_⟩
  · exact ⟨F, inferInstance, inferInstance, hF,
      ⟨(quotientEquiv e).trans (Representation.SL2NaturalH1.projectiveEquiv (K := F)).symm⟩⟩
  · exact ⟨naturalAction F, ⟨blockModuleModel e⟩, fun _ _ => rfl⟩

end CFSG.Quasithin.ChapterC


end
