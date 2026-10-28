module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Family.Thompson
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.CoverModel
public import Theory.GroupTheory.NormalizedSupCard
/-!
# The rank-one centralizer cardinal bound

The centralizer D and its disjoint conjugate both lie in the intersection
of the two elementary cores. The genuine action indices give
|Q|=|F|²|D| and |Q∩Qˣ|=|F||D|, so counting DDˣ gives |D|≤|F|.
The quotient projection also recovers the exact field order from the
original block type, including any central layer in its full module.

Source: Aschbacher--Smith C.6.1(3), printed pp.164--165.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K : Subgroup G} {F : Type*} [Field F]

omit [Finite G] in
private theorem count (Q A : Subgroup G) :
    Nat.card (Q ⊓ A : Subgroup G) * Q.relIndex A = Nat.card A := by
  simpa only [relIndex_bot_left,inf_relIndex_right] using
    relIndex_mul_relIndex (⊥ : Subgroup G) (Q ⊓ A) A bot_le inf_le_right

theorem Setup.centralizer_card_bound (h : Setup R K F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (hphi : Phi R K = ⊥)
    (hdis : D R K ⊓ (D R K).map (MulAut.conj x⁻¹).toMonoidHom = ⊥) :
    Nat.card (D R K) ≤ Nat.card F := by
  let Q' := (Q R K).map (MulAut.conj x⁻¹).toMonoidHom
  let D' := (D R K).map (MulAut.conj x⁻¹).toMonoidHom
  let I := Q R K ⊓ Q'
  let : IsElementaryAbelian 2 (Q R K) := h.core_elementary hx hnc hphi
  have hp := h.factorization hx hnc
  have hDcentral := h.centralizer_centralizes_baumann hx hnc hphi
  have hDQ : D R K ≤ Q R K := hp.core ▸ le_sup_right
  have hD'central : D' ≤ centralizer (S R : Set G) := by
    have hh := (map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hDcentral).trans
      (map_centralizer_le_centralizer_image _ _)
    change D' ≤ centralizer ((S R).map (MulAut.conj x⁻¹).toMonoidHom : Set G) at hh
    rwa [h.stable hx] at hh
  have hD'S : D' ≤ S R := (map_mono inf_le_left).trans_eq (h.stable hx)
  have hDI : D R K ≤ I := le_inf hDQ (by
    change D R K ≤ (Q R K).map (MulAut.conj x⁻¹).toMonoidHom
    rw [h.conjugate_core hx]
    exact le_inf inf_le_left hp.centralizes)
  have hD'I : D' ≤ I := le_inf
    (by rw [h.core]; exact le_inf hD'S (hD'central.trans (centralizer_le h.module_le)))
    (map_mono hDQ)
  have hDD : Nat.card (D R K) * Nat.card (D R K) ≤ Nat.card I := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes (D R K) D'
      ((hD'central.trans (centralizer_le (show D R K ≤ S R from inf_le_left))).trans
        (Subgroup.centralizer_le_normalizer _))
    rw [card_map_of_injective (MulAut.conj x⁻¹).injective,hdis,card_bot,one_mul] at hh
    exact hh.trans_le (card_le_of_le (sup_le hDI hD'I))
  have hqi : (Q R K).relIndex (S R) = Nat.card F := by
    rw [h.core,inf_relIndex_left]
    exact actor_index h.coordinates
  have hQcard : Nat.card (Q R K) = Nat.card F * Nat.card F * Nat.card (D R K) := by
    have hm := count (centralizer (K : Set G)) (U K)
    rw [projection_index h.coordinates] at hm
    have hi : U K ⊓ D R K = U K ⊓ centralizer (K : Set G) := by
      change U K ⊓ (S R ⊓ centralizer (K : Set G)) = _
      rw [←inf_assoc,inf_eq_left.mpr h.module_le]
    have hp' := card_mul_eq_card_inf_mul_card_sup_of_normalizes (U K) (D R K)
      ((inf_le_right.trans (centralizer_le (map_subtype_le _))).trans
        (Subgroup.centralizer_le_normalizer _))
    rw [hi,←hp.core] at hp'
    have hc : 0 < Nat.card (U K ⊓ centralizer (K : Set G) : Subgroup G) := Nat.card_pos
    rw [inf_comm] at hm
    nlinarith
  have hIcard : Nat.card I * Nat.card F = Nat.card (Q R K) := by
    have hc := count (Q R K) (S R)
    rw [inf_eq_left.mpr (h.core ▸ inf_le_left),hqi] at hc
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes (Q R K) Q'
      (((h.conjugate_core hx).le.trans inf_le_left).trans (S_normalizes_Q R K))
    rw [card_map_of_injective (MulAut.conj x⁻¹).injective,←h.core_span hx hnc,←hc] at hh
    have hp : 0 < Nat.card (Q R K) := Nat.card_pos
    change _ = Nat.card I * _ at hh
    nlinarith
  have hqpos : 0 < Nat.card F := by
    have hp : 0 < Nat.card (Q R K) := Nat.card_pos
    nlinarith [hQcard]
  have hIeq : Nat.card I = Nat.card F * Nat.card (D R K) := by
    nlinarith [hIcard,hQcard]
  have hdpos : 0 < Nat.card (D R K) := Nat.card_pos
  rw [hIeq] at hDD
  nlinarith

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne

open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] {R K : Subgroup G} {F : Type*} [Field F]

theorem ActionCoordinates.field_square_card (c : ActionCoordinates R K F) :
    Nat.card F * Nat.card F = Nat.card (BlockModule K) := by
  let q : U K →* BlockModule K := (QuotientGroup.mk' (blockFixed K)).comp
    (intrinsicEquiv K).symm.toMonoidHom
  have hs : Function.Surjective q :=
    (QuotientGroup.mk'_surjective _).comp (intrinsicEquiv K).symm.surjective
  have hk : q.ker = (centralizer (K : Set G)).subgroupOf (U K) := by
    ext u
    obtain ⟨v,rfl⟩ := (intrinsicEquiv K).surjective u
    change q (intrinsicEquiv K v) = 1 ↔ _
    simp only [q,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply]
    change v ∈ (QuotientGroup.mk' (blockFixed K)).ker ↔ _
    rw [QuotientGroup.ker_mk']
    change (v : K) ∈ center K ↔ (∀ y ∈ K, y * ((v : K) : G) = ((v : K) : G) * y)
    rw [mem_center_iff]
    constructor
    · intro hv y hy
      exact congrArg Subtype.val (hv ⟨y,hy⟩)
    · intro hv y
      exact Subtype.ext (hv y y.property)
  have hc := index_ker q
  rw [hk,q.range_eq_top_of_surjective hs,Nat.card_congr (topEquiv.toEquiv)] at hc
  exact (projection_index c).symm.trans hc

theorem ActionCoordinates.field_card_of_linear (c : ActionCoordinates R K F)
    {n : ℕ} (hK : IsL2EvenBlock K n) : Nat.card F = 2 ^ n := by
  have hc := c.field_square_card
  rw [hK.module_card,pow_mul] at hc
  exact Nat.pow_left_injective (by decide : 2 ≠ 0) (by simpa only [pow_two] using hc)

theorem ActionCoordinates.field_card_of_cubic (c : ActionCoordinates R K F)
    (hK : IsAlternatingBlock K 3) : Nat.card F = 2 := by
  have hc := c.field_square_card
  rw [hK.module_card_odd (by decide : Odd 3)] at hc
  norm_num at hc
  nlinarith
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne

