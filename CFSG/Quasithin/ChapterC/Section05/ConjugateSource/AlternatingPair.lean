module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.PairNormalizer

/-!
# The two-block alternating-five source configuration

This record collects only the preceding C.5.3–4 data on the literal blocks,
Baumann subgroup and marked action. The two-block transvection construction
then preserves the original conjugate module and produces the even exchange
from the actual block Sylow subgroup. Thus the noncommuting conjugate fixes
exactly four elements of U, without assuming that R preserves either block.

Source: Aschbacher–Smith, C.5.4 and the A₅ branch of C.5.6, printed pp.155–157.
The C.5.3–5 owner constructs these preceding data; none of the conjugate
factorizations, indices, fixed spaces or maximum elementary families is a field.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G]

structure AlternatingPairSetup (R K L : Subgroup G) where
  twoGroup : IsPGroup 2 R
  block : IsAlternatingBlock K 5
  commute : L ≤ centralizer (K : Set G)
  module_le : sourceModule K ≤ ChapterB.baumann R
  normalizes : ChapterB.baumann R ≤ normalizer (K : Set G)
  core : (K ⊔ ChapterB.baumann R).pCoreIn 2 =
    ChapterB.baumann R ⊓ centralizer (sourceModule K : Set G)
  product : (K ⊔ ChapterB.baumann R).pCoreIn 2 =
    sourceModule K ⊔ (ChapterB.baumann R ⊓ centralizer (K : Set G))
  permutes : ∀ r ∈ R, K.map (MulAut.conj r).toMonoidHom = K ∨
    K.map (MulAut.conj r).toMonoidHom = L
  sylow : Sylow 2 K
  sylow_image : (sylow : Subgroup K).map K.subtype = R ⊓ K
  action : (K ⊔ ChapterB.baumann R : Subgroup G) →* FivePerm
  coordinates : sourceModule K ≃* Multiplicative (BinaryPermutation.core (Fin 5))
  block_image : (K.subgroupOf (K ⊔ ChapterB.baumann R)).map action = alternatingGroup (Fin 5)
  baumann_image : ((ChapterB.baumann R).subgroupOf (K ⊔ ChapterB.baumann R)).map action = ChapterB.Offenders.D 5
  equivariant : ∀ (s : (K ⊔ ChapterB.baumann R : Subgroup G)) (u : sourceModule K),
    (coordinates.symm (Multiplicative.ofAdd
      (coreRepresentation (Fin 5) (action s) (coordinates u).toAdd)) : G) =
      (s : G) * (u : G) * (s : G)⁻¹

private theorem range_restrict (N B : Subgroup G) (hBN : B ≤ N) (a : N →* FivePerm) :
    (a.comp (inclusion hBN)).range = (B.subgroupOf N).map a := by
  ext p
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨inclusion hBN b, b.property, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hb⟩, rfl⟩

variable [Finite G] {R K L : Subgroup G}

/-- The C.5.4 marked action discharges every input of the initial R⁺ argument. -/
theorem AlternatingPairSetup.transvection_normalizes
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G)) :
    transvectionRadical R ≤ normalizer (sourceModule K : Set G) ∧
    transvectionRadical R ≤
      normalizer ((sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom : Set G) ∧
    R ⊓ K ≤ transvectionRadical R := by
  let a := h.action.comp (inclusion (show ChapterB.baumann R ≤ K ⊔ ChapterB.baumann R from le_sup_right))
  have himage : a.range = ChapterB.Offenders.D 5 :=
    (range_restrict _ _ le_sup_right h.action).trans h.baumann_image
  have he (s : ChapterB.baumann R) (u : sourceModule K) :
      (h.coordinates.symm (Multiplicative.ofAdd
        (coreRepresentation (Fin 5) (a s) (h.coordinates u).toAdd)) : G) =
        (s : G) * (u : G) * (s : G)⁻¹ :=
    h.equivariant (inclusion le_sup_right s) u
  have hn := alternating_transvection_normalizes_modules R K L h.block h.commute
    h.module_le h.permutes a h.coordinates himage he x hx
  exact ⟨hn.2.1, hn.2.2, alternating_blockSylow_le_transvectionRadical R K
    h.twoGroup h.block h.normalizes h.module_le h.core h.product a h.coordinates himage he⟩

/-- The actual block Sylow lift yields the exchange used to exclude a lone
transposition; no exchange witness is an input of the source configuration. -/
theorem AlternatingPairSetup.pairExchange_mem
    (h : AlternatingPairSetup R K L) :
    pairExchange ∈ ((R ⊓ K).subgroupOf (K ⊔ ChapterB.baumann R)).map h.action :=
  pairExchange_mem_blockSylow_image R (ChapterB.baumann R) K _ h.twoGroup inf_le_left le_sup_left
    h.action h.block_image h.baumann_image h.sylow h.sylow_image

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open Subgroup BinaryPermutation Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

/-- The noncommuting right conjugate fixes precisely four elements of the
original module in the two-block A₅ branch of C.5.6. -/
theorem AlternatingPairSetup.conjugate_fixed_card
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    Nat.card (sourceModule K ⊓
      centralizer ((sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom : Set G) : Subgroup G) = 4 := by
  let S := ChapterB.baumann R
  let N := K ⊔ S
  let U := sourceModule K
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  have hS : S.map (MulAut.conj x⁻¹).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp
      (Stellmacher.normalizer_le_normalizer_baumann R ((normalizer (R : Set G)).inv_mem hx))
  have hVS : V ≤ S := (map_mono h.module_le).trans_eq hS
  have hVN : V ≤ N := hVS.trans le_sup_right
  let av : V →* FivePerm := h.action.comp (inclusion hVN)
  have hav : av.range = (V.subgroupOf N).map h.action := range_restrict N V hVN h.action
  have hB : (V.subgroupOf N).map h.action ≤ ChapterB.Offenders.D 5 := by
    rw [← h.baumann_image]
    exact map_mono (subgroupOf_mono N hVS)
  have hne : (V.subgroupOf N).map h.action ≠ ⊥ := by
    intro hbot
    apply hnc
    intro v hv u hu
    let vN : N := ⟨v, hVN hv⟩
    have hvone : h.action vN = 1 := by
      have hh := mem_map_of_mem h.action (show vN ∈ V.subgroupOf N from hv)
      rw [hbot, mem_bot] at hh
      exact hh
    have he := h.equivariant vN ⟨u, hu⟩
    rw [hvone, map_one, Module.End.one_apply] at he
    change (h.coordinates.symm (h.coordinates ⟨u, hu⟩) : G) = v * u * v⁻¹ at he
    rw [h.coordinates.symm_apply_apply] at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  have hn := h.transvection_normalizes x hx
  have hf := fixedSpace_conjugate_image hn.2.1 hn.2.2 h.action hB hne h.pairExchange_mem
  have he (v : V) (u : U) :
      (h.coordinates.symm (Multiplicative.ofAdd
        (coreRepresentation (Fin 5) (av v) (h.coordinates u).toAdd)) : G) =
        (v : G) * (u : G) * (v : G)⁻¹ := h.equivariant (inclusion hVN v) u
  rw [marked_centralizer_card V U av h.coordinates he, hav, hf]
  exact pair_actor_fixed_card

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open Subgroup BinaryPermutation
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

omit [Finite G] in
/-- The full original A₅ block module has sixteen elements in these coordinates. -/
theorem AlternatingPairSetup.module_card (h : AlternatingPairSetup R K L) :
    Nat.card (sourceModule K) = 16 := by
  rw [Nat.card_congr h.coordinates.toEquiv, Nat.card_congr Multiplicative.toAdd,
    Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_core]
  norm_num

/-- The noncommuting conjugate acts on the original module with index four. -/
theorem AlternatingPairSetup.module_conjugate_index
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    (centralizer ((sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom : Set G)).relIndex
      (sourceModule K) = 4 := by
  have hc := h.conjugate_fixed_card x hx hnc
  have hm := relIndex_mul_relIndex (⊥ : Subgroup G)
    (sourceModule K ⊓ centralizer ((sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom : Set G))
    (sourceModule K) bot_le inf_le_left
  rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_left, hc, h.module_card] at hm
  omega

omit [Finite G] in
private theorem map_centralizer (U : Subgroup G) (e : G ≃* G) :
    (centralizer (U : Set G)).map e.toMonoidHom = centralizer (U.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro g hg
    refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
    intro u hu
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hg (e u) (mem_map_of_mem _ hu)

omit [Finite G] in
private theorem map_inverse_cancel (U : Subgroup G) (x : G) :
    (U.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = U := by
  rw [map_map]
  have he : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom = MonoidHom.id G := by
    ext u
    simp [MulAut.conj_apply, mul_assoc]
  rw [he, map_id]

/-- Symmetry transports the fixed-plane index onto the literal conjugate actor. -/
theorem AlternatingPairSetup.conjugate_action_index
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    (centralizer (sourceModule K : Set G)).relIndex
      ((sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom) = 4 := by
  have hi : ¬ (sourceModule K).map (MulAut.conj x).toMonoidHom ≤ centralizer (sourceModule K : Set G) := by
    intro hc
    have hh := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hc
    rw [map_inverse_cancel, map_centralizer] at hh
    exact hnc (le_centralizer_iff.mp hh)
  have hindex := h.module_conjugate_index x⁻¹ ((normalizer (R : Set G)).inv_mem hx)
    (by simpa only [inv_inv] using hi)
  simp only [inv_inv] at hindex
  have he := relIndex_map_map_of_injective (f := (MulAut.conj x⁻¹).toMonoidHom)
    (centralizer ((sourceModule K).map (MulAut.conj x).toMonoidHom : Set G))
    (sourceModule K) (MulAut.conj x⁻¹).injective
  rw [map_centralizer, map_inverse_cancel] at he
  exact he.trans hindex

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
