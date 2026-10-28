module

public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Frattini quotient profiles and automorphism groups

For a finite p-group, the kernel of the automorphism action on the Frattini
quotient is a p-group. Consequently, any profile on that quotient which is
preserved by every automorphism and has p-group stabilizer forces the full
automorphism group to be a p-group.

Source: the Burnside basis-kernel theorem in
`PGroup.FrattiniAutomorphismKernel`.
-/

namespace Subgroup

/-- Number of elements in a Frattini coset with a specified element order
and centralizer size. -/
@[expose] public noncomputable def orderCentralizerFiberCard
    {G : Type*} [Group G] (v : G ⧸ frattini G) (n m : ℕ) : ℕ :=
  Nat.card {x : G // QuotientGroup.mk' (frattini G) x = v ∧
    orderOf x = n ∧ Nat.card {y : G // y * x = x * y} = m}

private theorem centralizerCard_map {G : Type*} [Group G] (f : MulAut G) (x : G) :
    Nat.card {y : G // y * f x = f x * y} =
      Nat.card {y : G // y * x = x * y} := by
  apply Nat.card_congr
  refine {
    toFun := fun y => ⟨f.symm y, ?_⟩
    invFun := fun y => ⟨f y, ?_⟩
    left_inv := fun y => Subtype.ext (f.apply_symm_apply y)
    right_inv := fun y => Subtype.ext (f.symm_apply_apply y) }
  · apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using y.property
  · simpa only [map_mul] using congrArg f y.property

/-- Every automorphism preserves the order-centralizer profile on its
Frattini quotient. -/
public theorem orderCentralizerFiberCard_map {G : Type*} [Group G]
    (f : MulAut G) (v : G ⧸ frattini G) (n m : ℕ) :
    orderCentralizerFiberCard (quotientAut (frattini G) f v) n m =
      orderCentralizerFiberCard v n m := by
  unfold orderCentralizerFiberCard
  apply Nat.card_congr
  refine {
    toFun := fun x => ⟨f.symm x, ?_⟩
    invFun := fun x => ⟨f x, ?_⟩
    left_inv := fun x => Subtype.ext (f.apply_symm_apply x)
    right_inv := fun x => Subtype.ext (f.symm_apply_apply x) }
  · have hq : QuotientGroup.mk' (frattini G) (f.symm x) = v := by
      apply (quotientAut (frattini G) f).injective
      rw [quotientAut_apply_mk, f.apply_symm_apply]
      exact x.property.1
    refine ⟨hq, ?_, ?_⟩
    · simpa only [f.symm.orderOf_eq] using x.property.2.1
    · exact (centralizerCard_map f.symm x).trans x.property.2.2
  · refine ⟨?_, ?_, ?_⟩
    · rw [← quotientAut_apply_mk, x.property.1]
    · rw [f.orderOf_eq]
      exact x.property.2.1
    · rw [centralizerCard_map f]
      exact x.property.2.2

/-- A profile on the Frattini quotient with p-power-order stabilizer
controls the full automorphism group of a finite p-group. -/
public theorem isPGroup_mulAut_of_frattini_profile_general
    {G P : Type*} [Group G] [Finite G] {p : ℕ}
    (hG : IsPGroup p G) (profile : (G ⧸ frattini G) → P)
    (hpres : ∀ (f : MulAut G) (v : G ⧸ frattini G),
      profile (quotientAut (frattini G) f v) = profile v)
    (hcert : ∀ a : MulAut (G ⧸ frattini G),
      (∀ v, profile (a v) = profile v) → ∃ k : ℕ, a ^ (p ^ k) = 1) :
    IsPGroup p (MulAut G) := by
  let ρ := quotientAut (frattini G)
  have hrange : IsPGroup p ρ.range := by
    rintro ⟨a, f, rfl⟩
    obtain ⟨k, hk⟩ := hcert (ρ f) (hpres f)
    exact ⟨k, Subtype.ext hk⟩
  have hkernel : IsPGroup p ρ.ker :=
    isPGroup_quotientAut_frattini_kernel hG
  have ht := hrange.comap_of_ker_isPGroup ρ hkernel
  have htop : ρ.range.comap ρ = ⊤ := by ext f; simp
  rw [htop] at ht
  exact ht.of_surjective (⊤ : Subgroup (MulAut G)).subtype
    (fun f => ⟨⟨f, trivial⟩, rfl⟩)

end Subgroup
