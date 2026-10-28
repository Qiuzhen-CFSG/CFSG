module

public import Theory.SpecificGroups.ONan.ProjectiveOrder.SubgroupOrder.LinearSetup
public import Theory.GroupTheory.PresentedGroupBounds
public import Theory.GroupTheory.WordSubgroup.FiniteCover

/-!
# Certificate interfaces for the linear local subgroup

The two lifted ATLAS words generate the subgroup as an abstract group. Thus
checked coset transitions in that group give upper bounds. Independently,
subgroups of orders 64, 9, 343 and 19 give divisibility by their product,
3753792. This lower-bound route does not require a faithful permutation action
or an identification with a classical group.

The actual generator words and their attribution are in
`ProjectiveOrder/source/`; the matrices are in `refs/original/onan/`.
-/

namespace ONan.OrderCertificate

/-- The lifted words regarded as generators of their own subgroup. -/
@[expose] public def linearLocalGenerators : Bool → linearLocalSubgroup
  | false => ⟨linearLocalA, linearLocalA_mem⟩
  | true => ⟨linearLocalB, linearLocalB_mem⟩

public theorem closure_linearLocalGenerators :
    Subgroup.closure (Set.range linearLocalGenerators) = ⊤ := by
  have hs : Set.range linearLocalGenerators =
      linearLocalSubgroup.subtype ⁻¹' ({linearLocalA, linearLocalB} : Set _) := by
    ext x
    change (∃ b, linearLocalGenerators b = x) ↔
      (x.val = linearLocalA ∨ x.val = linearLocalB)
    constructor
    · rintro ⟨b, rfl⟩
      cases b
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (h | h)
      · exact ⟨false, Subtype.ext h.symm⟩
      · exact ⟨true, Subtype.ext h.symm⟩
  rw [hs]
  exact Subgroup.closure_preimage_eq_top _

/-- A checked cover may use any already certified subgroup at its bottom. -/
public theorem linearLocalSubgroup_card_le_of_cover {n : Nat}
    (K : Subgroup linearLocalSubgroup)
    (C : Subgroup.GeneratorCosetCover K linearLocalGenerators (Fin n)) :
    Nat.card linearLocalSubgroup ≤ Nat.card K * n := by
  simpa only [Nat.card_fin] using (C.finite_card_le closure_linearLocalGenerators).2

/-- The four independent prime-power certificates imply the full order divisor. -/
public theorem linearLocalSubgroup_order_dvd_of_prime_powers
    (h2 : 64 ∣ Nat.card linearLocalSubgroup)
    (h3 : 9 ∣ Nat.card linearLocalSubgroup)
    (h7 : 343 ∣ Nat.card linearLocalSubgroup)
    (h19 : 19 ∣ Nat.card linearLocalSubgroup) :
    3753792 ∣ Nat.card linearLocalSubgroup := by
  have h := Nat.lcm_dvd (Nat.lcm_dvd (Nat.lcm_dvd h2 h3) h7) h19
  norm_num at h
  exact h

/-- A nonzero finite group order is at least each of its divisors. -/
public theorem linearLocalSubgroup_card_ge_of_dvd
    (h : 3753792 ∣ Nat.card linearLocalSubgroup) :
    3753792 ≤ Nat.card linearLocalSubgroup :=
  Nat.le_of_dvd Nat.card_pos h

end ONan.OrderCertificate
