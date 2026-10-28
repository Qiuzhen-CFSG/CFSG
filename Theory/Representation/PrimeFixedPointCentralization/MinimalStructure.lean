module

public import Theory.Representation.PrimeFixedPointCentralization.Defs
public import Theory.Representation.PrimeFixedPointCentralization.MinimalStructure.GroupConsequences
public import Theory.Representation.PrimeFixedPointCentralization.MinimalStructure.CyclicCenter
public import Theory.Representation.TwoDimensionalOddOrder

/-!
# The structure of a minimal prime action with a faithful irreducible module

If the kernel in a minimal prime-order action is nonabelian, its centre is a
proper invariant subgroup.  Minimality therefore makes the actor centralize
that centre.  The image of the centre in the semidirect product is then a
subgroup of the ambient centre, and Schur's lemma (in the finite form already
proved for faithful irreducible representations) makes it cyclic.

The imported group consequences prove the abelian branch and, in the
nonabelian branch, the elementary central quotient and fixed-centre equality.
Exercise 8.10 (printed p.116) gives a special group from the group-action
hypotheses; its extraspecial clause additionally requires a faithful
irreducible representation. The cyclic centre supplied here is therefore
essential to the extraspecial and order conclusions in Aschbacher 36.2.
The final theorem supplies it to the cyclic-center structural helper and
therefore retains only the original action and representation hypotheses.
-/

open scoped IsMulCommutative
open Representation

namespace Representation.PrimeFixedPointCentralization

universe u

/-- Every actor centralizes the centre of the kernel once that centre is
proper.  The centre is invariant under every automorphism, so this is a
direct application of `IsMinimalAction`. -/
public theorem actor_fixes_center_of_minimal_action
    {P A : Type*} [Group P] [Group A]
    (φ : A →* MulAut P) (hmin : IsMinimalAction φ)
    (hproper : Subgroup.center P ≠ ⊤) :
    ∀ a : A, ∀ z : P, z ∈ Subgroup.center P → φ a z = z := by
  have hinv : ∀ a : A, ∀ z : P, z ∈ Subgroup.center P → φ a z ∈ Subgroup.center P := by
    intro a z hz
    exact Subgroup.mem_center_iff.mpr (fun y => by
      have hh := congrArg (φ a) (Subgroup.mem_center_iff.mp hz ((φ a)⁻¹ y))
      have hleft : (φ a) ((φ a)⁻¹ y) = y := by
        rw [MulAut.coe_inv]
        exact MulEquiv.apply_symm_apply (φ a) y
      simpa only [map_mul, hleft] using hh)
  intro a z hz
  exact hmin (Subgroup.center P) hinv hproper a z hz

/-- In the nonabelian branch the centre is cyclic.  The proof embeds the
centre into the centre of the semidirect product and invokes the finite Schur
lemma for the given faithful irreducible representation. -/
public theorem center_cyclic_of_minimal_action
    {P A W : Type u} [Group P] [Finite P] [Group A] [Finite A]
    (φ : A →* MulAut P) (hmin : IsMinimalAction φ)
    (hproper : Subgroup.center P ≠ ⊤)
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) (SemidirectProduct P A φ) W)
    [ρ.IsIrreducible] (hfaith : Function.Injective ρ) :
    IsCyclic (Subgroup.center P) := by
  let G := SemidirectProduct P A φ
  let _ : Group G := inferInstance
  let _ : Finite G := Finite.of_equiv (P × A) SemidirectProduct.equivProd.symm
  have hcentfix := actor_fixes_center_of_minimal_action φ hmin hproper
  let f : Subgroup.center P →* Subgroup.center G :=
    { toFun := fun z => ⟨SemidirectProduct.inl z.1, by
        rw [Subgroup.mem_center_iff]
        intro g
        rw [SemidirectProduct.mul_def, SemidirectProduct.mul_def]
        ext <;> simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl,
          one_mul, mul_one]
        · rw [hcentfix g.right z.1 z.2]
          simpa using (Subgroup.mem_center_iff.mp z.2 g.left)
      ⟩
      map_one' := by rfl
      map_mul' := by
        intro x y
        apply Subtype.ext
        change (⟨x.1 * y.1, 1⟩ : P ⋊[φ] A) =
          (⟨x.1, 1⟩ : P ⋊[φ] A) * (⟨y.1, 1⟩ : P ⋊[φ] A)
        rw [SemidirectProduct.mul_def]
        simp }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply (SemidirectProduct.inl_injective (φ := φ))
    exact congrArg Subtype.val hxy
  let _ : IsCyclic (Subgroup.center G) :=
    Representation.center_cyclic_of_representation_faithful_irreducible ρ hfaith
  exact isCyclic_of_injective f hf

/-- The structural alternative in Aschbacher 36.2 for a faithful minimal action
of a distinct odd prime-order group, with its given faithful irreducible binary
representation. The cyclic center in the nonabelian branch is derived from
that representation, so no additional structural hypothesis is required. -/
public theorem hasMinimalActionStructure_of_faithful_irreducible
    {q r : ℕ} [Fact q.Prime] [Fact r.Prime] (hqodd : Odd q) (_hrodd : Odd r)
    {P A W : Type u} [Group P] [Finite P] [Group A] [Finite A]
    (hP : IsPGroup q P) (hA : Nat.card A = r) (hqr : q ≠ r)
    (φ : A →* MulAut P) (hφ : Function.Injective φ) (hmin : IsMinimalAction φ)
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) (SemidirectProduct P A φ) W)
    [ρ.IsIrreducible] (hfaith : Function.Injective ρ) :
    HasMinimalActionStructure q φ := by
  by_cases hproper : Subgroup.center P = ⊤
  · let : IsMulCommutative P := Subgroup.center_eq_top_iff.mp hproper
    exact hasMinimalActionStructure_of_commutative hP hA hqr φ hφ hmin
  · let : IsCyclic (Subgroup.center P) :=
      center_cyclic_of_minimal_action φ hmin hproper ρ hfaith
    exact hasMinimalActionStructure_of_cyclic_center hqodd hP hA hqr φ hφ hmin

end Representation.PrimeFixedPointCentralization
