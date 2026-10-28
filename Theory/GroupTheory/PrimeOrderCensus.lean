module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Counting prime-order elements when Sylow subgroups have prime order

Each element of order `p` generates its unique Sylow `p`-subgroup. Thus the
set of such elements is the disjoint union of the generators of these Sylow
subgroups, each contributing `p - 1` elements. This is the elementary Sylow
count used in Wong (1964), Appendix (b), p.108.
-/

open Subgroup
namespace Sylow
noncomputable section
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

omit [Finite G] hp in
/-- An element of prime order belongs to a Sylow subgroup. -/
public theorem exists_mem_of_orderOf_eq {x : G} (hx : orderOf x = p) :
    ∃ P : Sylow p G, x ∈ P := by
  have h : IsPGroup p (zpowers x) := IsPGroup.of_card
    (show Nat.card (zpowers x) = p ^ 1 by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨P, hP⟩ := h.exists_le_sylow
  exact ⟨P, hP (mem_zpowers x)⟩

omit hp in
/-- In a Sylow subgroup of prime order, any element of that order generates it. -/
public theorem zpowers_eq_of_card_eq (P : Sylow p G) (hP : Nat.card P = p)
    {x : G} (hx : orderOf x = p) (hmem : x ∈ P) : zpowers x = (P : Subgroup G) := by
  apply eq_of_le_of_card_ge (zpowers_le.mpr hmem)
  rw [Nat.card_zpowers, hx, hP]

omit hp in
/-- A Sylow subgroup of prime order is uniquely determined by a nontrivial generator. -/
public theorem eq_of_mem_of_orderOf_eq (hP : ∀ P : Sylow p G, Nat.card P = p)
    {P Q : Sylow p G} {x : G} (hx : orderOf x = p) (hxp : x ∈ P) (hxq : x ∈ Q) :
    P = Q := by
  apply Sylow.ext
  exact (P.zpowers_eq_of_card_eq (hP P) hx hxp).symm.trans
    (Q.zpowers_eq_of_card_eq (hP Q) hx hxq)

/-- Prime-order elements counted by their unique prime-order Sylow subgroup. -/
public theorem card_orderOf_eq_of_card (hP : ∀ P : Sylow p G, Nat.card P = p) :
    Nat.card {x : G // orderOf x = p} = Nat.card (Sylow p G) * (p - 1) := by
  classical
  let f : (Σ P : Sylow p G, {x : P // orderOf x = p}) → {x : G // orderOf x = p} :=
    fun z => ⟨z.2.1, by simpa only [Subgroup.orderOf_coe] using z.2.2⟩
  have hinj : Function.Injective f := by
    rintro ⟨P, x⟩ ⟨Q, y⟩ hxy
    have he : (x.val : G) = (y.val : G) := congrArg Subtype.val hxy
    have hx : orderOf (x.val : G) = p := by simpa only [Subgroup.orderOf_coe] using x.property
    have hPQ : P = Q := eq_of_mem_of_orderOf_eq hP hx x.val.property
      (he ▸ y.val.property)
    subst Q
    congr 1
    exact Subtype.ext (Subtype.ext he)
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨P, hPx⟩ := exists_mem_of_orderOf_eq x.property
    refine ⟨⟨P, ⟨⟨x.val, hPx⟩, ?_⟩⟩, rfl⟩
    exact (Subgroup.orderOf_coe (⟨x.val, hPx⟩ : (P : Subgroup G))).symm.trans x.property
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)]
  let : Fintype (Sylow p G) := Fintype.ofFinite _
  rw [Nat.card_sigma]
  have hf (P : Sylow p G) : Nat.card {x : P // orderOf x = p} = p - 1 := by
    let : Fintype P := Fintype.ofFinite _
    have : IsCyclic P := isCyclic_of_prime_card (hP P)
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [IsCyclic.card_orderOf_eq_totient (by
      rw [← Nat.card_eq_fintype_card]
      change p ∣ Nat.card (P : Subgroup G)
      rw [hP P])]
    exact Nat.totient_prime hp.out
  simp only [hf, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

end
end Sylow
