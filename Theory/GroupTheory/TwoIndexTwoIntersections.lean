module
public import Theory.GroupTheory.IndexTwoIntersectionLine

/-!
# Two different relative index-two subgroups

Let A and B lie in X, with A contained in Q but not in R and B contained
in R but not in Q. If Q and R each have relative index two in X, their
common intersection with X has relative index four. Moreover A, B and
that intersection generate X. Normality of Q or R in the original ambient
group is not assumed.

Work intrinsically in X, where the two index-two subgroups are normal.
The crossing subgroup A shows that R has relative index two in Q, so the
intersection has index four. The line-intersection lemma and multiplication
of relative indices show that A together with the intersection generates Q.
Adding B, which crosses Q, then generates X. Map the generating equality
through the subtype inclusion and identify the actual ambient intersection.

This is the elementary index calculation in the V0 paragraph of
Stellmacher (8.2), Journal of Algebra 190 (1997), p.38;
source: `refs/latex/stellmacher-n-group.tex`.
-/

namespace Subgroup

private theorem indexTwo_generate
    {G : Type*} [Group G] (A B Q R : Subgroup G)
    (hAQ : A ≤ Q) (_hBR : B ≤ R) (hAR : ¬ A ≤ R) (hBQ : ¬ B ≤ Q)
    (hQ : Q.index = 2) (hR : R.index = 2) :
    ⊤ = A ⊔ B ⊔ (Q ⊓ R) ∧ (Q ⊓ R).index = 4 := by
  let _ : Q.Normal := Q.normal_of_index_eq_two hQ
  let _ : R.Normal := R.normal_of_index_eq_two hR
  have hRQ : R.relIndex Q = 2 :=
    subgroupOf_index_eq_two R Q hR (fun hQR => hAR (hAQ.trans hQR))
  have hnq : (Q ⊓ R).relIndex Q = 2 := by
    rwa [inf_relIndex_left]
  have hnA : (Q ⊓ R).relIndex A = 2 := by
    simpa using intersection_relIndex_eq_two_of_not_le ⊤ Q R A le_top hAQ hAR
      (by simpa using hR)
  have hNAQ : A ⊔ (Q ⊓ R) ≤ Q := sup_le hAQ inf_le_left
  have hnAn : (Q ⊓ R).relIndex (A ⊔ (Q ⊓ R)) = 2 := by
    rw [relIndex_sup_right]
    exact hnA
  have heqA : Q = A ⊔ (Q ⊓ R) := by
    have hm := relIndex_mul_relIndex (Q ⊓ R) (A ⊔ (Q ⊓ R)) Q le_sup_right hNAQ
    rw [hnAn, hnq] at hm
    exact le_antisymm (relIndex_eq_one.mp (by omega)) hNAQ
  have hqb : Q.relIndex B = 2 := subgroupOf_index_eq_two Q B hQ hBQ
  have ht : Q ⊔ B = ⊤ := by
    have hm := relIndex_mul_index (H := Q) (K := Q ⊔ B) le_sup_left
    rw [relIndex_sup_left, hqb, hQ] at hm
    exact index_eq_one.mp (by omega)
  constructor
  · calc
      ⊤ = Q ⊔ B := ht.symm
      _ = (A ⊔ (Q ⊓ R)) ⊔ B := congrArg (fun C : Subgroup G => C ⊔ B) heqA
      _ = A ⊔ B ⊔ (Q ⊓ R) := by ac_rfl
  · have hm := relIndex_mul_index (H := Q ⊓ R) (K := Q) inf_le_left
    rw [hnq, hQ] at hm
    exact hm.symm

public theorem sup_intersection_eq_and_relIndex_four
    {G : Type*} [Group G] [Finite G] (X A B Q R : Subgroup G)
    (hAX : A ≤ X) (hBX : B ≤ X) (hAQ : A ≤ Q) (hBR : B ≤ R)
    (hAR : ¬ A ≤ R) (hBQ : ¬ B ≤ Q)
    (hQ : Q.relIndex X = 2) (hR : R.relIndex X = 2) :
    X = A ⊔ B ⊔ (X ⊓ Q ⊓ R) ∧ (X ⊓ Q ⊓ R).relIndex X = 4 := by
  have hAQX : A.subgroupOf X ≤ Q.subgroupOf X := fun _ ha => hAQ ha
  have hBRX : B.subgroupOf X ≤ R.subgroupOf X := fun _ hb => hBR hb
  have hARX : ¬ A.subgroupOf X ≤ R.subgroupOf X := by
    intro hle
    exact hAR fun a ha => hle (show (⟨a, hAX ha⟩ : X) ∈ A.subgroupOf X from ha)
  have hBQX : ¬ B.subgroupOf X ≤ Q.subgroupOf X := by
    intro hle
    exact hBQ fun b hb => hle (show (⟨b, hBX hb⟩ : X) ∈ B.subgroupOf X from hb)
  obtain ⟨hgen, hidx⟩ := indexTwo_generate (A.subgroupOf X) (B.subgroupOf X)
    (Q.subgroupOf X) (R.subgroupOf X) hAQX hBRX hARX hBQX hQ hR
  have hQR : Q.subgroupOf X ⊓ R.subgroupOf X = (X ⊓ Q ⊓ R).subgroupOf X := by
    ext x
    change (x : G) ∈ Q ∧ (x : G) ∈ R ↔
      ((x : G) ∈ X ∧ (x : G) ∈ Q) ∧ (x : G) ∈ R
    exact ⟨fun hx => ⟨⟨x.property, hx.1⟩, hx.2⟩, fun hx => ⟨hx.1.2, hx.2⟩⟩
  rw [hQR] at hgen hidx
  constructor
  · have hm := congrArg (map X.subtype) hgen
    simpa only [← MonoidHom.range_eq_map, X.range_subtype, map_sup, map_subgroupOf_eq_of_le hAX,
      map_subgroupOf_eq_of_le hBX,
      map_subgroupOf_eq_of_le (inf_le_left.trans inf_le_left : X ⊓ Q ⊓ R ≤ X)] using hm
  · exact hidx
end Subgroup
