module

public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel

/-!
# Power counts in Frattini cosets constrain automorphisms

For a homomorphism π, count the elements in each fiber satisfying xⁿ = 1.
An automorphism of the source and a compatible automorphism of the target
preserve these counts. If π identifies a finite p-group's Frattini quotient,
and every automorphism preserving all the counts has p-power order, then the
source's full automorphism group is a p-group.

The proof transports the characteristic Frattini quotient action through the
first isomorphism theorem and applies the Burnside basis-kernel theorem from
`FrattiniAutomorphismKernel`. The counting step is an explicit bijection of
fibers. This provides a finite-certificate interface without assuming that all
count-preserving maps lift to source automorphisms.
-/

namespace MonoidHom
variable {G V : Type*} [Group G] [Group V]

/-- Number of solutions of a power equation in a specified homomorphism fiber. -/
@[expose] public noncomputable def powerFiberCard (π : G →* V) (v : V) (n : ℕ) : ℕ :=
  Nat.card {x : G // π x = v ∧ x ^ n = 1}

/-- Compatible automorphisms preserve the number of power-equation solutions in each fiber. -/
public theorem powerFiberCard_map (π : G →* V) (f : MulAut G) (a : MulAut V)
    (h : ∀ x, π (f x) = a (π x)) (v : V) (n : ℕ) :
    powerFiberCard π (a v) n = powerFiberCard π v n := by
  apply Nat.card_congr
  refine {
    toFun := fun x => ⟨f.symm x, ?_⟩
    invFun := fun x => ⟨f x, ?_⟩
    left_inv := fun x => Subtype.ext (f.apply_symm_apply x)
    right_inv := fun x => Subtype.ext (f.symm_apply_apply x) }
  · constructor
    · apply a.injective
      rw [← h, f.apply_symm_apply]
      exact x.property.1
    · apply f.injective
      simpa only [map_pow, f.apply_symm_apply, map_one] using x.property.2
  · constructor
    · rw [h, x.property.1]
    · rw [← map_pow, x.property.2, map_one]

/-- A p-power-order certificate for the power-count stabilizer on a Frattini quotient
forces the entire automorphism group to be a p-group. -/
public theorem isPGroup_mulAut_of_frattini_powerFiber [Finite G] {p : ℕ}
    (hG : IsPGroup p G) (π : G →* V) (hπ : Function.Surjective π)
    (hker : π.ker = frattini G)
    (cert : ∀ a : MulAut V,
      (∀ v n, powerFiberCard π (a v) n = powerFiberCard π v n) →
      ∃ k : ℕ, a ^ (p ^ k) = 1) : IsPGroup p (MulAut G) := by
  let e : (G ⧸ frattini G) ≃* V :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  have he (x : G) : e (QuotientGroup.mk' (frattini G) x) = π x := rfl
  let ρ : MulAut G →* MulAut V :=
    (MulAut.congr e).toMonoidHom.comp (Subgroup.quotientAut (frattini G))
  have hρ (f : MulAut G) (x : G) : ρ f (π x) = π (f x) := by
    change e (Subgroup.quotientAut (frattini G) f (e.symm (π x))) = _
    rw [← he x, e.symm_apply_apply, Subgroup.quotientAut_apply_mk, he]
  have hrange : IsPGroup p ρ.range := by
    rintro ⟨a, f, rfl⟩
    obtain ⟨k, hk⟩ := cert (ρ f) (powerFiberCard_map π f (ρ f) (fun x => (hρ f x).symm))
    exact ⟨k, Subtype.ext hk⟩
  have hkernel : IsPGroup p ρ.ker := by
    have hEq : ρ.ker = (Subgroup.quotientAut (frattini G)).ker := by
      ext f
      change MulAut.congr e (Subgroup.quotientAut (frattini G) f) = 1 ↔ _
      exact (MulAut.congr e).map_eq_one_iff
    rw [hEq]
    exact Subgroup.isPGroup_quotientAut_frattini_kernel hG
  have ht := hrange.comap_of_ker_isPGroup ρ hkernel
  have htop : ρ.range.comap ρ = ⊤ := by ext f; simp
  rw [htop] at ht
  exact ht.of_surjective (⊤ : Subgroup (MulAut G)).subtype (fun f => ⟨⟨f, trivial⟩, rfl⟩)
end MonoidHom
