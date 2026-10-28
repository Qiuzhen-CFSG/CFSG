module

public import Theory.ElementaryAbelian.UniqueLift
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Odd automorphisms preserve elementary subgroups of index two

A self-centralizing elementary abelian subgroup Q of index two has at most
one other self-centralizing elementary subgroup of the same order. The
unique-lift argument detects all fixed points on Q using a single actor
outside Q. Hence an automorphism permutes at most two such subgroups, and
an odd-order automorphism fixes Q. The ambient form retains the literal
conjugator and subgroup inclusions.

Source: Aschbacher–Smith B.2.21, pp.82–83; the odd-action argument in
3.3.31, printed p.602.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem centralizer_map_equiv (Q : Subgroup G) (e : G ≃* G) :
    centralizer (Q.map e.toMonoidHom : Set G) =
      (centralizer (Q : Set G)).map e.toMonoidHom := by
  apply le_antisymm
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro q hq
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e q) (mem_map_of_mem _ hq)
  · exact map_centralizer_le_centralizer_image _ _

omit [Finite G] in
private theorem index_two_image_eq_top (Q A : Subgroup G)
    (hi : Q.index = 2) [Q.Normal] (hn : ¬ A ≤ Q) :
    A.map (QuotientGroup.mk' Q) = ⊤ := by
  obtain ⟨a, ha, hao⟩ := SetLike.not_le_iff_exists.mp hn
  apply top_unique
  intro z _
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective Q z
  by_cases hb : b ∈ Q
  · change (b : G ⧸ Q) ∈ _
    rw [(QuotientGroup.eq_one_iff b).mpr hb]
    exact (A.map (QuotientGroup.mk' Q)).one_mem
  · have hab : a⁻¹ * b ∈ Q := (Q.mul_mem_iff_of_index_two hi).mpr
      (iff_of_false (fun hh => hao (Q.inv_mem_iff.mp hh)) hb)
    have he : QuotientGroup.mk' Q a = QuotientGroup.mk' Q b :=
      QuotientGroup.eq.mpr hab
    rw [← he]
    exact mem_map_of_mem _ ha

private theorem elementary_index_two_lift_unique (Q A B : Subgroup G)
    [IsElementaryAbelian 2 Q] [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hi : Q.index = 2) (hA : centralizer (A : Set G) ≤ A)
    (hB : centralizer (B : Set G) ≤ B) (ha : ¬ A ≤ Q) (hb : ¬ B ≤ Q)
    (hc : Nat.card A = Nat.card B) : B = A := by
  let : Q.Normal := Q.normal_of_index_eq_two hi
  obtain ⟨a, haA, haQ⟩ := SetLike.not_le_iff_exists.mp ha
  apply eq_of_le_of_card_ge ?_ hc.le
  apply IsElementaryAbelian.le_of_same_image_of_centralizer_singleton
    (QuotientGroup.mk' Q) Q A B (QuotientGroup.ker_mk' Q)
    (inf_le_right.trans hA) (inf_le_right.trans hB)
    ((index_two_image_eq_top Q A hi ha).trans (index_two_image_eq_top Q B hi hb).symm)
    a haA
  apply le_antisymm
  · exact inf_le_inf_left Q (centralizer_le (Set.singleton_subset_iff.mpr haA))
  · rintro x ⟨hxQ, hxa⟩
    refine ⟨hxQ, ?_⟩
    intro b _
    by_cases hbQ : b ∈ Q
    · exact setLike_mul_comm hbQ hxQ
    · have hab : a⁻¹ * b ∈ Q := (Q.mul_mem_iff_of_index_two hi).mpr
        (iff_of_false (fun hh => haQ (Q.inv_mem_iff.mp hh)) hbQ)
      have hc1 : Commute a x := hxa a (Set.mem_singleton a)
      have hc2 : Commute (a⁻¹ * b) x := setLike_mul_comm hab hxQ
      simpa using (hc1.mul_left hc2).eq

/-- An odd automorphism fixes a self-centralizing elementary subgroup of index two. -/
theorem elementary_index_two_fixed_of_odd (Q : Subgroup G)
    [IsElementaryAbelian 2 Q] (hi : Q.index = 2)
    (hself : centralizer (Q : Set G) = Q)
    (e : MulAut G) (ho : Odd (orderOf e)) : Q.map e.toMonoidHom = Q := by
  let A := Q.map e.toMonoidHom
  let B := A.map e.toMonoidHom
  have hA : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  let := hA
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  let := hB
  have hAc : centralizer (A : Set G) = A := by
    change centralizer (Q.map e.toMonoidHom : Set G) = Q.map e.toMonoidHom
    rw [centralizer_map_equiv Q e, hself]
  have hBc : centralizer (B : Set G) = B := by
    change centralizer (A.map e.toMonoidHom : Set G) = A.map e.toMonoidHom
    rw [centralizer_map_equiv A e, hAc]
  have hcardA : Nat.card A = Nat.card Q := card_map_of_injective e.injective
  have hcardB : Nat.card B = Nat.card A := card_map_of_injective e.injective
  have map_mul (f g : MulAut G) : Q.map (f * g).toMonoidHom =
      (Q.map g.toMonoidHom).map f.toMonoidHom := by rw [Subgroup.map_map]; rfl
  have htwo : Q.map (e ^ 2).toMonoidHom = Q := by
    rw [pow_two, map_mul]
    change B = Q
    by_cases ha : A = Q
    · dsimp [B]
      rw [ha]
      exact ha
    by_contra hb
    have ha' : ¬ A ≤ Q := fun hh => ha (eq_of_le_of_card_ge hh hcardA.ge)
    have hb' : ¬ B ≤ Q := fun hh => hb (eq_of_le_of_card_ge hh (hcardB.trans hcardA).ge)
    have he : B = A := elementary_index_two_lift_unique Q A B hi hAc.le hBc.le
      ha' hb' hcardB.symm
    exact ha (map_injective e.injective he)
  obtain ⟨m, hm⟩ := exists_pow_eq_pow_two_mul (pow_orderOf_eq_one e) ho 1
  rw [pow_one] at hm
  rw [hm, pow_mul]
  clear hm
  induction m with
  | zero => change Q.map (MonoidHom.id G) = Q; exact map_id Q
  | succ n ih =>
    rw [pow_succ, map_mul]
    rw [htwo, ih]
end Subgroup

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Ambient form, preserving relative normality and the actual conjugator. -/
theorem elementary_relIndex_two_normalized_of_odd (Q S : Subgroup G)
    [IsElementaryAbelian 2 Q] (hQS : Q ≤ S) (hi : Q.relIndex S = 2)
    (hself : S ⊓ centralizer (Q : Set G) = Q)
    (d : G) (hd : d ∈ normalizer (S : Set G)) (ho : Odd (orderOf d)) :
    d ∈ normalizer (Q : Set G) := by
  let P := Q.subgroupOf S
  let e : MulAut S := S.normalizerMonoidHom ⟨d, hd⟩
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.subgroupOf hQS
  have hP : centralizer (P : Set S) = P := by
    apply le_antisymm
    · intro x hx
      have hx' : (x : G) ∈ S ⊓ centralizer (Q : Set G) := by
        refine ⟨x.property, ?_⟩
        intro q hq
        exact congrArg S.subtype (hx ⟨q, hQS hq⟩ hq)
      change (x : G) ∈ Q
      exact hself ▸ hx'
    · exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  have heo : Odd (orderOf e) := ho.of_dvd_nat (by
    simpa only [← Subgroup.orderOf_coe] using
      orderOf_map_dvd S.normalizerMonoidHom (⟨d, hd⟩ : normalizer (S : Set G)))
  have he := elementary_index_two_fixed_of_odd P hi hP e heo
  apply mem_normalizer_iff_map_conj_eq.mpr
  calc
    Q.map (MulAut.conj d).toMonoidHom =
        (P.map e.toMonoidHom).map S.subtype := by
      rw [← map_subgroupOf_eq_of_le hQS, map_map, map_map]
      rfl
    _ = Q := by rw [he]; exact map_subgroupOf_eq_of_le hQS
end Subgroup
