module

public import Theory.Character.ModularBlock.Cartan

/-!
# Recovering Cartan invariants from ordinary character kernels

The sum over ordinary principal-block characters of `χ(g) * χ(h)`, for
odd-order `g` and `h`, expands in products of irreducible Brauer characters.
Its coefficients are exactly the Cartan entries. Linear independence in each
variable makes this expansion unique, so an identity between ordinary kernels
suffices to compare Cartan matrices.

This is the linear-algebra step in the central two-quotient comparison
(cf. Feit, *The Representation Theory of Finite Groups*, III.2.13).
It uses the genuine decomposition data of `Cartan`; it asserts neither
existence of decomposition coefficients nor a quotient kernel identity.
-/

public section

open scoped BigOperators

noncomputable section

namespace ModularBlock.Cartan

private theorem bilinear_coefficients_unique {X : Type*} {n : ℕ}
    (f : Fin n → X → ℂ) (hf : LinearIndependent ℂ f)
    (A B : Fin n → Fin n → ℂ)
    (h : ∀ x y, ∑ j, ∑ k, A j k * f j x * f k y =
      ∑ j, ∑ k, B j k * f j x * f k y) : A = B := by
  have hf' := Fintype.linearIndependent_iffₛ.mp hf
  have hrow (y : X) : (fun j => ∑ k, A j k * f k y) =
      (fun j => ∑ k, B j k * f k y) := by
    apply funext (hf' _ _ ?_)
    funext x
    have hx := h x y
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
      mul_right_comm] using hx
  funext j
  apply funext (hf' _ _ ?_)
  funext y
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun (hrow y) j

open PrincipalBlockConstruction BrauerCoefficientExtension
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Expand the ordinary principal-block kernel in products of Brauer values. -/
theorem PrincipalDecompositionData.ordinaryKernel_eq {d : PrincipalCongruenceBlockData G} {n : ℕ}
    (a : PrincipalDecompositionData d n) (g h : G)
    (hg : Odd (orderOf g)) (hh : Odd (orderOf h)) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk g) * d.chi i (ConjClasses.mk h) =
      ∑ j, ∑ k, (a.cartan j k : ℂ) * BrauerCharacter.value d (a.family.rep j) g *
        BrauerCharacter.value d (a.family.rep k) h := by
  calc
    _ = ∑ i ∈ d.block, ∑ j, ∑ k,
        ((a.decomposition i j : ℂ) * (a.decomposition i k : ℂ)) *
          BrauerCharacter.value d (a.family.rep j) g *
          BrauerCharacter.value d (a.family.rep k) h := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [a.restriction i hi g hg, a.restriction i hi h hh, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      simp only [PrincipalDecompositionData.cartan, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul]

/-- Independence in both variables recovers every Cartan entry from the ordinary kernel. -/
theorem PrincipalDecompositionData.cartan_eq_of_ordinaryKernel {d : PrincipalCongruenceBlockData G} {n : ℕ}
    (a : PrincipalDecompositionData d n) (C : Fin n → Fin n → ℕ)
    (hC : ∀ g h : G, Odd (orderOf g) → Odd (orderOf h) →
      ∑ i ∈ d.block, d.chi i (ConjClasses.mk g) * d.chi i (ConjClasses.mk h) =
        ∑ j, ∑ k, (C j k : ℂ) * BrauerCharacter.value d (a.family.rep j) g *
          BrauerCharacter.value d (a.family.rep k) h) :
    a.cartan = C := by
  have heq : (fun j k => (a.cartan j k : ℂ)) = (fun j k => (C j k : ℂ)) := by
    apply bilinear_coefficients_unique _ a.family.independent
    intro x y
    obtain ⟨g, hg, hx⟩ := x.property
    obtain ⟨h, hh, hy⟩ := y.property
    have hx' : x = BrauerCharacter.twoRegularClass g hg := Subtype.ext hx.symm
    have hy' : y = BrauerCharacter.twoRegularClass h hh := Subtype.ext hy.symm
    rw [hx', hy']
    simpa only [BrauerCharacter.character_apply] using
      (a.ordinaryKernel_eq g h hg hh).symm.trans (hC g h hg hh)
  funext j k
  exact_mod_cast congrFun (congrFun heq j) k

end ModularBlock.Cartan
