module

public import Theory.Representation.BinaryPermutation
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic


/-!
# Splitting a natural five-letter quotient

The sum of the twenty three-cycle operators is the identity on the binary
augmentation core. It is zero on every A₅-fixed kernel, and is equivariant
under S₅ because the three-cycles form a conjugacy class. Factoring this
operator through the given quotient constructs an actual equivariant section.
Its image is exactly the alternating commutator, including when the original
module has an additional fixed part.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the natural
S₅ branch of C.1.24 and E.2.3, printed pp.130–131 and 216–217.
-/

@[expose] public section

open Equiv
namespace BinaryPermutation.FiveCentralExtension
abbrev Sym := Perm (Fin 5)
def cubes : Finset Sym := Finset.univ.filter (fun g => g ^ 3 = 1 ∧ g ≠ 1)
theorem cubes_card : cubes.card = 20 := by decide +kernel
theorem cubes_even : ∀ g ∈ cubes, g ∈ alternatingGroup (Fin 5) := by
  intro g hg
  rw [Perm.mem_alternatingGroup]
  have h : ∀ g : Sym, g ^ 3 = 1 → g.sign = 1 := by decide +kernel
  exact h g (Finset.mem_filter.mp hg).2.1
private theorem cubes_conj (g a : Sym) : a ∈ cubes ↔ (MulAut.conj g) a ∈ cubes := by
  simp only [cubes, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← map_pow, map_eq_one_iff _ (MulAut.conj g).injective,
    map_ne_one_iff _ (MulAut.conj g).injective]

theorem core_sum (v : core (Fin 5)) : ∑ g ∈ cubes, coreRepresentation (Fin 5) g v = v := by
  have hc : ∀ v : Full (Fin 5), (∑ i, v i) = 0 →
      ∀ i, (∑ g ∈ cubes, representation (Fin 5) g v i) = v i := by decide +kernel
  apply Subtype.ext
  ext i
  simpa only [Submodule.coe_sum, Finset.sum_apply, coreRepresentation_apply] using hc v.val v.property i

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
def projector (ρ : Representation (ZMod 2) Sym V) : V →ₗ[ZMod 2] V := ∑ g ∈ cubes, ρ g

theorem projector_equivariant (ρ : Representation (ZMod 2) Sym V) (g : Sym) (v : V) :
    projector ρ (ρ g v) = ρ g (projector ρ v) := by
  simp only [projector, LinearMap.sum_apply, map_sum]
  symm
  apply Finset.sum_equiv (MulAut.conj g).toEquiv (cubes_conj g)
  intro a _
  change ρ g (ρ a v) = ρ (g * a * g⁻¹) (ρ g v)
  simp only [← Module.End.mul_apply, ← map_mul]
  simp [mul_assoc]

/-- The natural quotient is unchanged by the class-sum projection. -/
theorem quotient_projector (ρ : Representation (ZMod 2) Sym V)
    (p : V →ₗ[ZMod 2] core (Fin 5))
    (he : ∀ g v, p (ρ g v) = coreRepresentation (Fin 5) g (p v)) (v : V) :
    p (projector ρ v) = p v := by
  simp only [projector, LinearMap.sum_apply, map_sum, he]
  exact core_sum (p v)

private theorem projector_kernel (ρ : Representation (ZMod 2) Sym V)
    (p : V →ₗ[ZMod 2] core (Fin 5))
    (hk : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5), ρ g v = v)
    {v : V} (hv : p v = 0) : projector ρ v = 0 := by
  simp only [projector, LinearMap.sum_apply]
  calc
    _ = ∑ _g ∈ cubes, v := Finset.sum_congr rfl (fun g hg => hk v hv g (cubes_even g hg))
    _ = 0 := by
      rw [Finset.sum_const, cubes_card, ← Nat.cast_smul_eq_nsmul (R := ZMod 2)]
      change (20 : ZMod 2) • v = 0
      rw [show (20 : ZMod 2) = 0 from rfl, zero_smul]

/-- A natural five-letter core quotient with A₅-fixed kernel has an actual
S₅-equivariant section; the quotient map is retained literally. -/
theorem exists_section (ρ : Representation (ZMod 2) Sym V)
    (p : V →ₗ[ZMod 2] core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g v, p (ρ g v) = coreRepresentation (Fin 5) g (p v))
    (hk : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5), ρ g v = v) :
    ∃ s : core (Fin 5) →ₗ[ZMod 2] V,
      (∀ v, p (s v) = v) ∧
      (∀ g v, s (coreRepresentation (Fin 5) g v) = ρ g (s v)) ∧
      (∀ v, s (p v) = projector ρ v) := by
  let f := projector ρ
  have hker : p.ker ≤ f.ker := fun v hv => projector_kernel ρ p hk hv
  let s := (p.ker.liftQ f hker).comp (p.quotKerEquivOfSurjective hp).symm.toLinearMap
  have hs (v : V) : s (p v) = projector ρ v := by
    simp [s, LinearMap.quotKerEquivOfSurjective_symm_apply, f]
  refine ⟨s, ?_, ?_, hs⟩
  · intro v
    obtain ⟨w, rfl⟩ := hp v
    rw [hs, quotient_projector ρ p he]
  · intro g v
    obtain ⟨w, rfl⟩ := hp v
    rw [← he, hs, hs]
    exact projector_equivariant ρ g w

open Representation.BinaryOffender

/-- The class-sum projector has exactly the actual alternating moved space as range. -/
theorem projector_range (ρ : Representation (ZMod 2) Sym V)
    (p : V →ₗ[ZMod 2] core (Fin 5))
    (he : ∀ g v, p (ρ g v) = coreRepresentation (Fin 5) g (p v))
    (hk : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5), ρ g v = v) :
    (projector ρ).range = subspaceCommutator ρ ⊤ (alternatingGroup (Fin 5)) := by
  have hzero (v : V) : 20 • v = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (R := ZMod 2)]
    change (20 : ZMod 2) • v = 0
    rw [show (20 : ZMod 2) = 0 from rfl, zero_smul]
  apply le_antisymm
  · rintro v ⟨w, rfl⟩
    have hsum : projector ρ w = ∑ g ∈ cubes, (ρ g w - w) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, cubes_card, hzero, sub_zero,
        projector, LinearMap.sum_apply]
    rw [hsum]
    exact Submodule.sum_mem _ fun g hg => Submodule.subset_span
      ⟨g, cubes_even g hg, w, Submodule.mem_top, rfl⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨g, hg, w, _, rfl⟩
    have hker : p (projector ρ w - w) = 0 := by
      rw [map_sub, quotient_projector ρ p he, sub_self]
    have hc := hk _ hker g hg
    rw [map_sub] at hc
    refine ⟨ρ g w - w, ?_⟩
    rw [map_sub, projector_equivariant]
    exact sub_eq_sub_iff_sub_eq_sub.mpr hc

/-- The original quotient identifies its actual moved support with the natural core. -/
theorem exists_moved_section (ρ : Representation (ZMod 2) Sym V)
    (p : V →ₗ[ZMod 2] core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g v, p (ρ g v) = coreRepresentation (Fin 5) g (p v))
    (hk : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5), ρ g v = v) :
    ∃ s : core (Fin 5) →ₗ[ZMod 2] V,
      (∀ v, p (s v) = v) ∧
      (∀ g v, s (coreRepresentation (Fin 5) g v) = ρ g (s v)) ∧
      s.range = subspaceCommutator ρ ⊤ (alternatingGroup (Fin 5)) := by
  obtain ⟨s, hs, heq, hsp⟩ := exists_section ρ p hp he hk
  refine ⟨s, hs, heq, ?_⟩
  rw [← projector_range ρ p he hk]
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨u, rfl⟩ := hp w
    exact ⟨u, (hsp u).symm⟩
  · rintro ⟨w, rfl⟩
    exact ⟨p w, hsp w⟩

end BinaryPermutation.FiveCentralExtension
