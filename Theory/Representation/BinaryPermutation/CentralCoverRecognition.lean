module

public import Theory.Representation.BinaryPermutationSixCover.Universal
public import Theory.Representation.BinaryPermutationEightCover.Universal
public import Theory.Representation.FirstCohomologyDuality.Indecomposable

/-!
# Recognition of perfect central covers of small alternating natural modules

Odd-degree natural modules have vanishing dual first cohomology, so a
perfect central cover has zero kernel. In degrees six and eight the
augmentation core is universal. A cover with nonzero kernel has dimension
strictly greater than the natural module, hence the same dimension as the
core; the universal surjection is consequently an isomorphism. The
isomorphism preserves the given projection, not just the representation type.

Source: Aschbacher–Smith, I.1.5–6, p.408; used in 12.2.16, p.800.
-/

public noncomputable section
open Representation Representation.OneCohomology
namespace BinaryPermutation

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

/-- A perfect central cover of an odd-degree natural module has trivial kernel. -/
theorem alternating_odd_cover_injective {n : ℕ} (hn : 3 ≤ n) (ho : Odd n)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin n)) U)
    (p : σ.IntertwiningMap (alternatingNaturalRepresentation (Fin n)))
    (hp : IsCover p) : Function.Injective p := by
  have : NeZero n := ⟨by omega⟩
  let E := H1Congr (alternatingNaturalRepresentation (Fin n))
    (alternatingNaturalRepresentation (Fin n)).dual
    (MulEquiv.refl _) (naturalDualEquiv (Fin n))
    (fun g v => naturalDualEquiv_equivariant (Fin n) g.val v)
  have hd : Module.finrank (ZMod 2)
      (H1 (alternatingNaturalRepresentation (Fin n)).dual) = 0 := by
    rw [← E.finrank_eq]
    exact alternatingNatural_finrank_H1_eq_zero_of_odd (Fin n)
      (by simpa using hn) (by simpa using ho)
  have hk := finrank_ker_le_H1_of_cover p hp
  rw [hd] at hk
  exact LinearMap.ker_eq_bot.mp
    ((Submodule.finrank_eq_zero).mp (Nat.eq_zero_of_le_zero hk))

/-- Nontrivial perfect central covers in degrees six and eight are the core,
with the original natural projection and actor marking retained. -/
theorem alternating_even_cover_equiv_core {n : ℕ} (hn : n = 6 ∨ n = 8)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin n)) U)
    (p : σ.IntertwiningMap (alternatingNaturalRepresentation (Fin n)))
    (hp : IsCover p) (hk : p.toLinearMap.ker ≠ ⊥) :
    ∃ E : U ≃ₗ[ZMod 2] core (Fin n),
      (∀ g u, E (σ g u) = alternatingCoreRepresentation (Fin n) g (E u)) ∧
      ∀ u, coreToNatural (Fin n) (E u) = p u := by
  have : NeZero n := ⟨by rcases hn with rfl | rfl <;> omega⟩
  have hf : ∃ f : core (Fin n) →ₗ[ZMod 2] U, Function.Surjective f ∧
      (∀ g v, f (alternatingCoreRepresentation (Fin n) g v) = σ g (f v)) ∧
      ∀ v, p (f v) = coreToNatural (Fin n) v := by
    rcases hn with rfl | rfl
    · exact SixCover.core_quotient_of_alternating_cover σ p hp
    · exact EightCover.core_quotient_of_alternating_cover σ p hp
  obtain ⟨f, hsur, he, hpf⟩ := hf
  have hpos : 0 < Module.finrank (ZMod 2) p.toLinearMap.ker :=
    Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hk)
  have hsum := p.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hp.1, finrank_top] at hsum
  have heven : Even (Fintype.card (Fin n)) := by
    rcases hn with rfl | rfl <;> decide
  rw [finrank_natural_even (Fin n) heven] at hsum
  have hupper := LinearMap.finrank_le_finrank_of_surjective hsur
  have hdim : Module.finrank (ZMod 2) (core (Fin n)) = Module.finrank (ZMod 2) U := by
    rw [finrank_core] at hupper ⊢
    simp only [Fintype.card_fin] at hupper hsum ⊢
    rcases hn with rfl | rfl <;> omega
  let F : core (Fin n) ≃ₗ[ZMod 2] U := LinearEquiv.ofBijective f
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsur, hsur⟩
  refine ⟨F.symm, ?_, ?_⟩
  · intro g u
    apply F.injective
    rw [F.apply_symm_apply]
    exact (he g (F.symm u)).trans (congrArg (σ g) (F.apply_symm_apply u)) |>.symm
  · intro u
    exact (hpf (F.symm u)).symm.trans (congrArg p (F.apply_symm_apply u))

end BinaryPermutation
