module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Triality.LowerObstruction.HeadFamily
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.Sp4.ECaseReduction
public import Mathlib.GroupTheory.Schreier

/-!
# Literal two-core intersections for triality E-members

The two-closed radical in the component case makes its intersection with an
elementary actor equal to the actor's intersection with the two-core. Thus
both source quotient-rank alternatives bound the image modulo O₂(K).
Counting the kernel shows that an actor of order 2^a has an intersection
with the embedded two-core of order greater than 2^b when b+i<a.

Intersecting that core with the normal triality copy retains normalization
by the original K and containment in the prescribed ambient Sylow subgroup.
For the full cubic-root actor family and i=3f-1, the intersection with the actor is
larger than 2^(2f), but the actor is not contained in the core. These are inputs
to a geometric confinement argument; no confinement is assumed or asserted.

Source: Aschbacher--Smith E.1.2 and E.1.5, printed p.210, and E.1.14(2),
printed p.214 (citing Asc82a, Lemma 4.7).
-/

public section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.Triality.LowerObstruction
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem member_core_image_card_le {T A K : Subgroup G} {i : ℕ}
    (hK : IsEMemberAt i T A K) :
    Nat.card ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) ≤ 2 ^ i := by
  let _ := hK.1.1
  let _ : IsElementaryAbelian 2 (A.subgroupOf K) :=
    IsElementaryAbelian.subgroupOf hK.1.2.2.1
  let a := (A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))
  let _ : IsElementaryAbelian 2 a := IsElementaryAbelian.map _
  let _ : CommGroup a := IsMulCommutative.instCommGroup
  have hdvd : Nat.card a ∣ 2 ^ Group.rank a := card_dvd_exponent_pow_rank' a
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 a))
  exact (Nat.le_of_dvd (by positivity) hdvd).trans
    (Nat.pow_le_pow_right (by decide)
      (ValuesEvenClassical.Sp4Lower.member_core_rank_le hK))

theorem member_core_intersection_card_gt {T A K L : Subgroup G} {a b i : ℕ}
    (hK : IsEMemberAt i T A K) (hAL : A ≤ L)
    (hcard : Nat.card A = 2 ^ a) (hgap : b + i < a) :
    2 ^ b < Nat.card ((((pCore 2 K).map K.subtype) ⊓ L) ⊓ A : Subgroup G) := by
  let AK := A.subgroupOf K
  let N := pCore 2 K
  let H := N.subgroupOf AK
  have hindex : H.index = Nat.card (AK.map (QuotientGroup.mk' N)) := by
    simpa only [QuotientGroup.ker_mk', relIndex, H] using
      relIndex_ker AK (QuotientGroup.mk' N)
  have hprod : Nat.card H * Nat.card (AK.map (QuotientGroup.mk' N)) = Nat.card A := by
    rw [← hindex, H.card_mul_index]
    exact Nat.card_congr (subgroupOfEquivOfLe hK.1.2.2.1).toEquiv
  have hmap : Nat.card H = Nat.card (((N.map K.subtype) ⊓ L) ⊓ A : Subgroup G) := by
    have heq : H.map (K.subtype.comp AK.subtype) =
        ((N.map K.subtype) ⊓ L) ⊓ A := by
      rw [← Subgroup.map_map]
      change ((N.subgroupOf AK).map AK.subtype).map K.subtype = _
      rw [Subgroup.subgroupOf_map_subtype, Subgroup.map_inf N AK K.subtype K.subtype_injective]
      rw [show AK.map K.subtype = A from map_subgroupOf_eq_of_le hK.1.2.2.1]
      rw [inf_assoc, inf_eq_right.mpr hAL]
    have hinj : Function.Injective (K.subtype.comp AK.subtype) :=
      fun x y h => Subtype.ext (Subtype.ext h)
    rw [← heq, Subgroup.card_map_of_injective hinj]
  rw [← hmap]
  by_contra hnot
  have hle : Nat.card H ≤ 2 ^ b := Nat.le_of_not_gt hnot
  have hbound := Nat.mul_le_mul hle (member_core_image_card_le hK)
  have hpowlt : 2 ^ b * 2 ^ i < 2 ^ a := by
    rw [← Nat.pow_add]
    exact Nat.pow_lt_pow_right (by decide) hgap
  rw [hprod, hcard] at hbound
  exact (Nat.not_lt_of_ge hbound) hpowlt

theorem member_core_socle_le_sylow (T : Sylow 2 G) {A K L : Subgroup G} {i : ℕ}
    (hK : IsEMemberAt i (T : Subgroup G) A K) :
    ((pCore 2 K).map K.subtype) ⊓ L ≤ (T : Subgroup G) ⊓ L := by
  obtain ⟨S, hS⟩ := hK.1.2.2.2.2.1
  have hcoreS : pCore 2 K ≤ (S : Subgroup K) :=
    pCore_isPGroup.le_sylow_of_normal S
  apply inf_le_inf_right
  exact (map_mono hcoreS).trans (by
    rw [hS, subgroupOf_map_subtype]
    exact inf_le_left)

omit [Finite G] in
theorem member_core_socle_normalized (L K : Subgroup G) [L.Normal] :
    K ≤ normalizer (((pCore 2 K).map K.subtype ⊓ L : Subgroup G) : Set G) := by
  have hC : K ≤ normalizer (((pCore 2 K).map K.subtype : Subgroup G) : Set G) := by
    have h := Subgroup.le_normalizer_map (H := pCore 2 K) K.subtype
    simpa only [normalizer_eq_top_iff.mpr inferInstance, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] using h
  exact (le_inf hC le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf

/-- The actor retains a core intersection larger than q² at the predecessor bound,
but its active source clause prevents it from lying wholly in that core. -/
theorem head_member_core_intersection (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) {f : ℕ} {hf : 0 < f}
    (e : L ≃* _root_.Triality.Standard.BinaryCarrier f hf)
    {A K : Subgroup G} (hA : A ∈ ambientHeadFamily L e)
    (hK : IsEMemberAt (3 * f - 1) (T : Subgroup G) A K) :
    let Q := ((pCore 2 K).map K.subtype) ⊓ L
    Q ≤ (T : Subgroup G) ⊓ L ∧ K ≤ normalizer (Q : Set G) ∧
      2 ^ (2 * f) < Nat.card (Q ⊓ A : Subgroup G) ∧ ¬ A ≤ Q := by
  refine ⟨member_core_socle_le_sylow T hK, member_core_socle_normalized L K, ?_, ?_⟩
  · exact member_core_intersection_card_gt
      (b := 2 * f) hK (ambientHeadFamily_le hA) (ambientHeadFamily_card hA) (by omega)
  · intro hAQ
    apply ValuesEvenClassical.Sp4Lower.member_not_le_core hK.1
    intro a ha
    obtain ⟨c, hc, he⟩ := (hAQ ha).1
    exact (Subtype.ext he : c = a) ▸ hc

end CFSG.Quasithin.ChapterE.ExceptionalValues.Triality.LowerObstruction
