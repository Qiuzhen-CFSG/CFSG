module
public import Glauberman.QuadraticOffenderSelection

/-!
# Sharp maximum-abelian replacement

Let V be an abelian subgroup of Q centralizing Q, where Q is normalized
by S. Maximal abelian order gives |V:C_V(A)| <= |A:A intersect Q| for
every maximum abelian subgroup A of S. If a marked module section gives
the reverse lower bound |S:Q|, both inequalities are equalities. Thus A
supplements Q and (A intersect Q)V has the same maximum abelian order,
both in S and in Q. All groups, intersections, and relative indices are
literal ambient subgroups.

Source: Niles, *Pushing-up in finite groups* (1979), Lemmas 4.3 and 7.4,
printed pp.44 and60–61. The module lower bound is supplied separately by
the natural-module theorem2.9; it is not asserted for arbitrary modules.
-/

public section
open Subgroup
namespace Glauberman
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem abelian_intersection_sup {A Q V : Subgroup G}
    (hAc : IsMulCommutative A) (hVc : IsMulCommutative V)
    (hcentral : V ≤ centralizer (Q : Set G)) :
    IsMulCommutative (A ⊓ Q ⊔ V : Subgroup G) := by
  let _ := hAc
  let _ := hVc
  let _ : IsMulCommutative (A ⊓ Q : Subgroup G) :=
    IsMulCommutative.of_setLike_mul_comm fun _ hx _ hy => setLike_mul_comm hx.1 hy.1
  have hBV : V ≤ centralizer (A ⊓ Q : Set G) :=
    hcentral.trans (centralizer_le inf_le_right)
  apply le_centralizer_iff_isMulCommutative.mp
  apply sup_le
  · exact le_centralizer_iff.mpr (sup_le (A ⊓ Q).le_centralizer hBV)
  · exact le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp hBV) V.le_centralizer)

/-- When the fixed-space lower bound reaches the full quotient order,
the abelian replacement has the original maximum order. -/
theorem maximum_abelian_saturation {S Q V A : Subgroup G}
    (hA : A ∈ thompsonAbelianSubgroups S) (hQS : Q ≤ S) (hVQ : V ≤ Q)
    (hVc : IsMulCommutative V) (hcentral : V ≤ centralizer (Q : Set G))
    (hlower : Q.relIndex S ≤ (V ⊓ centralizer (A : Set G)).relIndex V) :
    (V ⊓ centralizer (A : Set G)).relIndex V = Q.relIndex S ∧
    Q.relIndex A = Q.relIndex S ∧
    Nat.card ↥(A ⊓ Q ⊔ V) = Nat.card A ∧
    A ⊓ Q ⊔ V ∈ thompsonAbelianSubgroups S ∧
    A ⊓ Q ⊔ V ∈ thompsonAbelianSubgroups Q := by
  have hVS := hVQ.trans hQS
  have hupper := maximum_abelian_offender_bound hA hVS hVQ hVc hcentral
  have hle : Q.relIndex A ≤ Q.relIndex S :=
    relIndex_le_of_le_right hA.1 (show Q.relIndex S ≠ 0 from index_ne_zero_of_finite)
  have hi : (V ⊓ centralizer (A : Set G)).relIndex V = Q.relIndex S :=
    le_antisymm (hupper.trans hle) hlower
  have hiA : Q.relIndex A = Q.relIndex S := le_antisymm hle (hlower.trans hupper)
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes (A ⊓ Q) V
    ((hcentral.trans (centralizer_le inf_le_right)).trans (centralizer_le_normalizer _))
  have hinter : (A ⊓ Q) ⊓ V = A ⊓ V := by
    ext x
    exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,hVQ h.2⟩,h.2⟩⟩
  rw [hinter] at hprod
  have hVcard := relIndex_mul_relIndex (⊥ : Subgroup G) (A ⊓ V) V bot_le inf_le_right
  have hAcard := relIndex_mul_relIndex (⊥ : Subgroup G) (A ⊓ Q) A bot_le inf_le_left
  simp only [relIndex_bot_left,inf_relIndex_left] at hVcard hAcard
  have hfixed : (A ⊓ V).relIndex V = Q.relIndex A := by
    rw [←centralizer_intersection_maximum_abelian hA hVS,hi,hiA]
  rw [hfixed] at hVcard
  have hcard : Nat.card ↥(A ⊓ Q ⊔ V) = Nat.card A := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥(A ⊓ V)))
    calc
      Nat.card ↥(A ⊓ V) * Nat.card ↥(A ⊓ Q ⊔ V) =
          Nat.card ↥(A ⊓ Q) * Nat.card V := hprod.symm
      _ = Nat.card ↥(A ⊓ V) * Nat.card A := by
        rw [←hVcard,←hAcard]
        ac_rfl
  have hjoin : A ⊓ Q ⊔ V ∈ thompsonAbelianSubgroups S :=
    ⟨sup_le (inf_le_left.trans hA.1) hVS,
      abelian_intersection_sup hA.2.1 hVc hcentral,
      fun B hB hBc => hcard ▸ hA.2.2 B hB hBc⟩
  exact ⟨hi,hiA,hcard,hjoin,
    ⟨sup_le inf_le_right hVQ,hjoin.2.1,fun B hB hBc => hjoin.2.2 B (hB.trans hQS) hBc⟩⟩

/-- The same saturation forces the original maximum abelian subgroup to
supplement the normal subgroup Q. -/
theorem maximum_abelian_supplements_normal {S Q V A : Subgroup G}
    (hA : A ∈ thompsonAbelianSubgroups S) (hQS : Q ≤ S) (hVQ : V ≤ Q)
    (hVc : IsMulCommutative V) (hcentral : V ≤ centralizer (Q : Set G))
    (hn : S ≤ normalizer (Q : Set G))
    (hlower : Q.relIndex S ≤ (V ⊓ centralizer (A : Set G)).relIndex V) :
    A ⊔ Q = S := by
  have he := (maximum_abelian_saturation hA hQS hVQ hVc hcentral hlower).2.1
  let _ : (Q.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer hn
  have hr := relIndex_sup_right (A.subgroupOf S) (Q.subgroupOf S)
  rw [←subgroupOf_sup hA.1 hQS,relIndex_subgroupOf (sup_le hA.1 hQS),
    relIndex_subgroupOf hA.1] at hr
  have hm := relIndex_mul_relIndex Q (A ⊔ Q) S le_sup_right (sup_le hA.1 hQS)
  rw [hr,he] at hm
  have hone : (A ⊔ Q).relIndex S = 1 := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (show Q.relIndex S ≠ 0 from index_ne_zero_of_finite))
    simpa only [mul_one] using hm
  exact le_antisymm (sup_le hA.1 hQS) (relIndex_eq_one.mp hone)

/-- Niles 4.3 and 7.4, stated with the precise lower fixed-space bound
supplied by the natural module theorem. -/
theorem maximum_abelian_replacement_of_fixedIndex {S Q V A : Subgroup G}
    (hA : A ∈ thompsonAbelianSubgroups S) (hQS : Q ≤ S) (hVQ : V ≤ Q)
    (hVc : IsMulCommutative V) (hcentral : V ≤ centralizer (Q : Set G))
    (hn : S ≤ normalizer (Q : Set G))
    (hlower : Q.relIndex S ≤ (V ⊓ centralizer (A : Set G)).relIndex V) :
    A ⊔ Q = S ∧
    A ⊓ Q ⊔ V ∈ thompsonAbelianSubgroups S ∧
    A ⊓ Q ⊔ V ∈ thompsonAbelianSubgroups Q ∧
    Nat.card ↥(A ⊓ Q ⊔ V) = Nat.card A ∧
    (A ⊓ V).relIndex V = Q.relIndex S ∧
    thompsonAbelianSubgroups Q ⊆ thompsonAbelianSubgroups S := by
  obtain ⟨hi,_,hc,hS,hQ⟩ := maximum_abelian_saturation hA hQS hVQ hVc hcentral hlower
  exact ⟨maximum_abelian_supplements_normal hA hQS hVQ hVc hcentral hn hlower,
    hS,hQ,hc,by rwa [centralizer_intersection_maximum_abelian hA (hVQ.trans hQS)] at hi,
    fun B hB => ⟨hB.1.trans hQS,hB.2.1,fun C hC hCc =>
      (hS.2.2 C hC hCc).trans (hB.2.2 _ hQ.1 hQ.2.1)⟩⟩
end Glauberman
