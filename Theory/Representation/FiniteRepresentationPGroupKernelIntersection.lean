module

public import Theory.PGroup
public import Theory.Representation.kerRepresentation

/-!
# Finite representation kernel intersections

A finite family of representations whose kernel quotients are p-groups has a
p-group source whenever the family is jointly faithful.  The proof packages
the family into the product of the faithful kernel quotients, observes that a
finite product of p-groups is a p-group by its cardinality, and pulls the
property back along the product injection.  Thus no individual constituent is
assumed faithful; only the intersection of all constituent kernels is trivial.
-/

namespace Representation

variable {p : ℕ} {G : Type*} [Group G] [Fact p.Prime]

private theorem isPGroup_pi {ι : Type*} [Fintype ι]
    (H : ι → Type*) [∀ i, Group (H i)] [∀ i, Finite (H i)]
    (hH : ∀ i, IsPGroup p (H i)) : IsPGroup p (∀ i, H i) := by
  rw [IsPGroup.iff_card]
  choose exponents hpow using fun i => IsPGroup.exists_card_eq (hH i)
  refine ⟨∑ i, exponents i, ?_⟩
  rw [Nat.card_pi]
  simp_rw [hpow]
  exact Finset.prod_pow_eq_pow_sum Finset.univ exponents p

/-- A finite jointly faithful family of p-group kernel quotients has p-group
source. -/
public theorem isPGroup_of_finite_ker_quotients
    {ι : Type*} [Fintype ι] {H : ι → Type*}
    [∀ i, Group (H i)] [∀ i, Finite (H i)]
    (φ : ∀ i, G →* H i)
    (hquot : ∀ i, IsPGroup p (G ⧸ (φ i).ker))
    (hker : ∀ g : G, (∀ i, g ∈ (φ i).ker) → g = 1) : IsPGroup p G := by
  let ψ : G →* (∀ i, G ⧸ (φ i).ker) :=
    MonoidHom.pi (fun i => QuotientGroup.mk' (φ i).ker)
  have hψ : Function.Injective ψ := by
    intro g h hEq
    have hdiff : ψ (g * h⁻¹) = 1 := by
      rw [map_mul, map_inv, hEq]
      simp
    have hkerdiff : g * h⁻¹ = 1 := hker (g * h⁻¹) (by
      intro i
      exact (QuotientGroup.eq_one_iff (g * h⁻¹)).mp (by
        simpa [ψ] using congrArg (fun x => x i) hdiff))
    exact mul_inv_eq_one.mp hkerdiff
  exact (isPGroup_pi (fun i => G ⧸ (φ i).ker) hquot).of_injective ψ hψ


set_option linter.style.haveILetI false in
/-- Kernel-intersection form for a finite list of representation constituents.
The subgroups `K i` may be proper nontrivial kernels; joint faithfulness is
exactly the displayed intersection condition. -/
public theorem isPGroup_of_finite_kernel_intersection
    {ι : Type*} [Fintype ι] {K : ι → Subgroup G} [Finite G]
    (hNormal : ∀ i, (K i).Normal)
    (hquot : ∀ i, IsPGroup p (G ⧸ K i))
    (hinter : ∀ g : G, (∀ i, g ∈ K i) → g = 1) : IsPGroup p G := by
  letI (i : ι) : (K i).Normal := hNormal i
  let ψ : G →* (∀ i, G ⧸ K i) :=
    MonoidHom.pi (fun i => QuotientGroup.mk' (K i))
  have hψ : Function.Injective ψ := by
    intro g h hEq
    have hdiff : ψ (g * h⁻¹) = 1 := by
      rw [map_mul, map_inv, hEq]
      simp
    have hkerdiff : g * h⁻¹ = 1 := hinter (g * h⁻¹) (by
      intro i
      exact (QuotientGroup.eq_one_iff (g * h⁻¹)).mp (by
        simpa [ψ] using congrArg (fun x => x i) hdiff))
    exact mul_inv_eq_one.mp hkerdiff
  exact (isPGroup_pi (fun i => G ⧸ K i) hquot).of_injective ψ hψ

end Representation
