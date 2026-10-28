module
public import Theory.Representation.FiniteSimpleGenerators
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Independent simple images distinguished by their action kernels

An equivalence of representations preserves its group-action kernel.
Schur's lemma therefore makes every intertwiner between irreducibles with
different kernels zero. In a completely reducible target, extend the inverse
of each injected simple image to an equivariant retraction. These retractions
annihilate all other images, so the map from their finite direct product is
injective and their dimensions add to at most the target dimension.

This is the constituent-separation step used in the Wedderburn argument of
Fong--Seitz I (6C), printed p.41. It works over any field and retains each
actual action, without requiring an algebraically closed scalar field.
-/

public noncomputable section
namespace Representation
open scoped MonoidAlgebra
variable {k H V W : Type*} [Field k] [Group H]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

private theorem ker_eq_of_equiv {ρ : Representation k H V} {σ : Representation k H W}
    (e : ρ.Equiv σ) : ρ.ker = σ.ker := by
  ext h
  constructor
  · intro hh
    change σ h = 1
    ext w
    obtain ⟨v,rfl⟩ := e.toLinearEquiv.surjective w
    change σ h (e v) = e v
    have he : e (ρ h v) = σ h (e v) := e.toIntertwiningMap.isIntertwining _ _ h v
    rw [show ρ h = 1 from hh] at he
    exact he.symm
  · intro hh
    change ρ h = 1
    ext v
    apply e.toLinearEquiv.injective
    change e (ρ h v) = e v
    have he : e (ρ h v) = σ h (e v) := e.toIntertwiningMap.isIntertwining _ _ h v
    rw [show σ h = 1 from hh] at he
    exact he

/-- Distinct action kernels distinguish irreducible representations over
any field, so every intertwiner between them vanishes. -/
theorem intertwiner_eq_zero_of_distinct_kernels
    {ρ : Representation k H V} {σ : Representation k H W}
    [ρ.IsIrreducible] [σ.IsIrreducible] (hne : ρ.ker ≠ σ.ker)
    (f : ρ.IntertwiningMap σ) : f = 0 := by
  rcases IsIrreducible.bijective_or_eq_zero f with hf | hf
  · exact (hne (ker_eq_of_equiv (f.ofBijective hf))).elim
  · exact hf

/-- In a completely reducible target, injective images of irreducibles
with distinct action kernels are independent. -/
theorem finrank_sum_le_of_distinct_kernels [FiniteDimensional k W]
    {ι : Type*} [Fintype ι] (V : ι → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, FiniteDimensional k (V i)]
    (ρ : ∀ i, Representation k H (V i)) (σ : Representation k H W)
    (hir : ∀ i, (ρ i).IsIrreducible) (hcr : σ.IsCompletelyReducible)
    (hker : Pairwise fun i j => (ρ i).ker ≠ (ρ j).ker)
    (f : ∀ i, (ρ i).IntertwiningMap σ) (hf : ∀ i, Function.Injective (f i)) :
    (∑ i, Module.finrank k (V i)) ≤ Module.finrank k W := by
  classical
  let : IsSemisimpleModule k[H] σ.asModule := hcr
  have retract (i : ι) : ∃ p : σ.IntertwiningMap (ρ i), ∀ x, p (f i x) = x := by
    let fm := IntertwiningMap.equivLinearMapAsModule _ _ (f i)
    obtain ⟨pm,hpm⟩ := IsSemisimpleModule.extension_property fm
      (show Function.Injective fm from hf i) (LinearMap.id : (ρ i).asModule →ₗ[k[H]] (ρ i).asModule)
    let p := (IntertwiningMap.equivLinearMapAsModule σ (ρ i)).symm pm
    exact ⟨p,fun x => LinearMap.congr_fun hpm x⟩
  choose p hp using retract
  have hzero (i j : ι) (hij : i ≠ j) (x : V j) : p i (f j x) = 0 := by
    let := hir i
    let := hir j
    have he := intertwiner_eq_zero_of_distinct_kernels (hker hij.symm) ((p i).comp (f j))
    exact congrArg (fun g => g x) he
  let a : (∀ i, V i) →ₗ[k] W := {
    toFun x := ∑ i, f i (x i)
    map_add' x y := by simp only [Pi.add_apply,map_add,Finset.sum_add_distrib]
    map_smul' c x := by simp only [Pi.smul_apply,map_smul,Finset.smul_sum]; rfl }
  have hi : Function.Injective a := by
    intro x y hxy
    funext i
    have hcalc (z : ∀ i, V i) : p i (a z) = z i := by
      change p i (∑ j, f j (z j)) = _
      rw [map_sum,Finset.sum_eq_single i]
      · exact hp i (z i)
      · intro j _ hji; exact hzero i j hji.symm (z j)
      · simp
    exact (hcalc x).symm.trans ((congrArg (p i) hxy).trans (hcalc y))
  have hh := LinearMap.finrank_le_finrank_of_injective hi
  rwa [Module.finrank_pi_fintype] at hh
end Representation
