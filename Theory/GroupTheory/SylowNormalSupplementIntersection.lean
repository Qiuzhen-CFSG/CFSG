module
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Sylow intersections above a normal supplement

Let S be a Sylow p-subgroup of a finite group G. If a normal subgroup N
supplements S, then S intersect C is Sylow in every subgroup C containing N.
This does not assume that C is normal.

Set A=S intersect C. Factoring elements through N and S gives N join A=C.
Relative-index multiplication in the two subgroup diamonds yields
[C:A]=[G:S]. The latter index is prime to p, so the p-subgroup A is Sylow.

This standard finite-group transfer is used with the two-residual inside
an element centralizer in Stellmacher (6.4), journal p32 of
refs/latex/stellmacher-n-group.tex. Its abstract statement preserves the
supplied subgroup and does not require any campaign action or classification.
-/

public theorem Sylow.exists_map_eq_inf_of_normal_supplement
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (N C : Subgroup G) [N.Normal]
    (hNS : N ⊔ (S : Subgroup G) = ⊤) (hNC : N ≤ C) :
    ∃ T : Sylow p C, (T : Subgroup C).map C.subtype = (S : Subgroup G) ⊓ C := by
  let A : Subgroup G := (S : Subgroup G) ⊓ C
  have hNA : N ⊔ A = C := by
    apply le_antisymm (sup_le hNC inf_le_right)
    intro c hc
    have ht : c ∈ N ⊔ (S : Subgroup G) := hNS.ge (Subgroup.mem_top c)
    obtain ⟨n, hn, s, hs, hns⟩ := Subgroup.mem_sup_of_normal_left.mp ht
    have hsC : s ∈ C := by
      have hh := C.mul_mem (C.inv_mem (hNC hn)) hc
      rwa [← hns, inv_mul_cancel_left] at hh
    rw [← hns]
    exact (N ⊔ A).mul_mem ((le_sup_left : N ≤ N ⊔ A) hn)
      ((le_sup_right : A ≤ N ⊔ A) ⟨hs, hsC⟩)
  have hAN : A ⊓ N = (S : Subgroup G) ⊓ N := by
    dsimp [A]
    ext x
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, hNC h.2⟩, h.2⟩
  have hindex (R : Subgroup G) : R.relIndex (N ⊔ R) = (R ⊓ N).relIndex N := by
    have hn : N.relIndex (N ⊔ R) = (R ⊓ N).relIndex R := by
      rw [Subgroup.relIndex_sup_left, Subgroup.inf_relIndex_left]
    have hleft := Subgroup.relIndex_mul_relIndex (R ⊓ N) R (N ⊔ R) inf_le_left le_sup_right
    have hright := Subgroup.relIndex_mul_relIndex (R ⊓ N) N (N ⊔ R) inf_le_right le_sup_left
    rw [hn] at hright
    have hpos : 0 < (R ⊓ N).relIndex R := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    nlinarith
  have hi : A.relIndex C = (S : Subgroup G).index := by
    rw [← hNA, hindex A, hAN, ← hindex (S : Subgroup G), hNS,
      Subgroup.relIndex_top_right]
  have hAp : IsPGroup p (A.subgroupOf C) :=
    (S.isPGroup'.to_le (inf_le_left : A ≤ (S : Subgroup G))).of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ≤ C)).symm
  have hnot : ¬ p ∣ (A.subgroupOf C).index := by
    change ¬ p ∣ A.relIndex C
    rw [hi]
    exact S.not_dvd_index
  refine ⟨hAp.toSylow hnot, ?_⟩
  rw [IsPGroup.toSylow_coe, Subgroup.map_subgroupOf_eq_of_le inf_le_right]

