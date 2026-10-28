module

public import Theory.Representation.BinaryPermutation.FiveCentralExtension
public import Theory.Representation.BinaryPermutation.FiveTensorNormalizer
import Mathlib.Tactic

/-!
# Extending the original natural A₅ quotient to S₅

The sum of twenty three-cycle operators descends through the given quotient map
using only alternating equivariance and an alternating-fixed kernel. Its
centrality supplies the induced action of every symmetric permutation.
Comparing an induced actor with the prescribed coordinate permutation gives
an invertible map commuting with A₅. The existing scalar-commutant theorem
forces this map to be the identity over F₂. Thus the original quotient map
is already S₅-equivariant, without assuming an action on the outside coset
or a decomposition of the full module.

Source: Aschbacher–Smith, the natural S₅ branch of C.1.24 and E.2.3,
printed pp.130–131 and 216–217; the permutation-core commutant is the
point-stabilizer calculation used in the binary A₅ tensor normalizer.
-/

public section

open Representation Representation.BinaryOffender
namespace BinaryPermutation.FiveCentralExtension

/-- An injective endomorphism commuting with the actual A₅ core action is the identity. -/
theorem core_commuting_eq_id (f : core (Fin 5) →ₗ[ZMod 2] core (Fin 5))
    (hf : ∀ g ∈ alternatingGroup (Fin 5), ∀ v,
      f (coreRepresentation (Fin 5) g v) = coreRepresentation (Fin 5) g (f v))
    (hi : Function.Injective f) : ∀ v, f v = v := by
  obtain ⟨c, hc⟩ := FiveTensorNormalizer.core_commuting_scalar f (fun g v => hf g.val g.property v)
  have hbinary : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hbinary c with hz | ho
  · have hn : Nontrivial (core (Fin 5)) := Module.nontrivial_of_finrank_pos
      (by rw [finrank_core]; decide)
    obtain ⟨v, hv⟩ := exists_ne (0 : core (Fin 5))
    have hzero : f v = f 0 := by simp [hc, hz]
    exact (hv (hi hzero)).elim
  · simpa [ho] using hc

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem even_quotient_projector (ρ : Representation (ZMod 2) Sym V)
    (p : V →ₗ[ZMod 2] core (Fin 5))
    (he : ∀ g ∈ alternatingGroup (Fin 5), ∀ v,
      p (ρ g v) = coreRepresentation (Fin 5) g (p v)) (v : V) :
    p (projector ρ v) = p v := by
  simp only [projector, LinearMap.sum_apply, map_sum]
  rw [Finset.sum_congr rfl (fun g hg => he g (cubes_even g hg) v)]
  exact core_sum (p v)

private theorem even_section (ρ : Representation (ZMod 2) Sym V)
    (p : V →ₗ[ZMod 2] core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g ∈ alternatingGroup (Fin 5), ∀ v,
      p (ρ g v) = coreRepresentation (Fin 5) g (p v))
    (hk : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5), ρ g v = v) :
    ∃ s : core (Fin 5) →ₗ[ZMod 2] V,
      (∀ w, p (s w) = w) ∧ ∀ v, s (p v) = projector ρ v := by
  have hker : p.ker ≤ (projector ρ).ker := by
    intro v hv
    change projector ρ v = 0
    simp only [projector, LinearMap.sum_apply]
    calc
      _ = ∑ _g ∈ cubes, v := Finset.sum_congr rfl (fun g hg => hk v hv g (cubes_even g hg))
      _ = 0 := by
        rw [Finset.sum_const, cubes_card, ← Nat.cast_smul_eq_nsmul (R := ZMod 2)]
        change (20 : ZMod 2) • v = 0
        rw [show (20 : ZMod 2) = 0 from rfl, zero_smul]
  let s := (p.ker.liftQ (projector ρ) hker).comp (p.quotKerEquivOfSurjective hp).symm.toLinearMap
  have hs (v : V) : s (p v) = projector ρ v := by
    simp [s, LinearMap.quotKerEquivOfSurjective_symm_apply]
  refine ⟨s, ?_, hs⟩
  intro w
  obtain ⟨v, rfl⟩ := hp w
  rw [hs, even_quotient_projector ρ p he]

/-- Alternating equivariance of the original natural quotient forces full
symmetric equivariance; its kernel is only required to be alternating-fixed. -/
theorem equivariant_of_alternating (ρ : Representation (ZMod 2) Sym V)
    (p : V →ₗ[ZMod 2] core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g ∈ alternatingGroup (Fin 5), ∀ v,
      p (ρ g v) = coreRepresentation (Fin 5) g (p v))
    (hk : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5), ρ g v = v) :
    ∀ g v, p (ρ g v) = coreRepresentation (Fin 5) g (p v) := by
  obtain ⟨s, hs, hsp⟩ := even_section ρ p hp he hk
  let R := coreRepresentation (Fin 5)
  let A (g : Sym) : core (Fin 5) →ₗ[ZMod 2] core (Fin 5) := p.comp ((ρ g).comp s)
  have hA (g : Sym) (v : V) : A g (p v) = p (ρ g v) := by
    change p (ρ g (s (p v))) = _
    rw [hsp, ← projector_equivariant, even_quotient_projector ρ p he]
  have hinv (g : Sym) (w : core (Fin 5)) : A g⁻¹ (A g w) = w := by
    obtain ⟨v, rfl⟩ := hp w
    rw [hA, hA]
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hconj (g a : Sym) (ha : a ∈ alternatingGroup (Fin 5)) (w : core (Fin 5)) :
      A g (R a w) = R (g * a * g⁻¹) (A g w) := by
    obtain ⟨v, rfl⟩ := hp w
    have hea : g * a * g⁻¹ ∈ alternatingGroup (Fin 5) :=
      (inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem a ha g
    change A g (coreRepresentation (Fin 5) a (p v)) = _
    rw [← he a ha, hA, hA, ← he _ hea]
    congr 1
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  have hD (g : Sym) (w : core (Fin 5)) : R g⁻¹ (A g w) = w := by
    let d := (R g⁻¹).comp (A g)
    apply core_commuting_eq_id d
    · intro a ha v
      change R g⁻¹ (A g (R a v)) = R a (R g⁻¹ (A g v))
      rw [hconj g a ha]
      change (R g⁻¹ * R (g * a * g⁻¹)) (A g v) = (R a * R g⁻¹) (A g v)
      rw [← map_mul, ← map_mul]
      congr 2
      group
    · intro u v huv
      have hh := congrArg (R g) huv
      have heq : A g u = A g v := by
        change R g (R g⁻¹ (A g u)) = R g (R g⁻¹ (A g v)) at hh
        simpa only [R.self_inv_apply] using hh
      have hh' := congrArg (A g⁻¹) heq
      simpa only [hinv] using hh'
  intro g v
  have h := congrArg (R g) (hD g (p v))
  simpa only [hA, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
    map_one, Module.End.one_apply] using h

/-- The exact A₅-fixed kernel version used by the original source quotient. -/
theorem equivariant_of_alternating_fixed_kernel (ρ : Representation (ZMod 2) Sym V)
    (p : V →ₗ[ZMod 2] core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g ∈ alternatingGroup (Fin 5), ∀ v,
      p (ρ g v) = coreRepresentation (Fin 5) g (p v))
    (hker : p.ker = fixedSpace ρ (alternatingGroup (Fin 5))) :
    ∀ g v, p (ρ g v) = coreRepresentation (Fin 5) g (p v) := by
  apply equivariant_of_alternating ρ p hp he
  intro v hv g hg
  have hh : v ∈ fixedSpace ρ (alternatingGroup (Fin 5)) := hker ▸ hv
  exact hh ⟨g, hg⟩

/-- The A₅-only natural marking identifies the actual moved support with the
core, with full symmetric equivariance and the original quotient as inverse. -/
theorem exists_moved_section_of_alternating
    (ρ : Representation (ZMod 2) Sym V)
    (p : V →ₗ[ZMod 2] core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g ∈ alternatingGroup (Fin 5), ∀ v,
      p (ρ g v) = coreRepresentation (Fin 5) g (p v))
    (hk : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5), ρ g v = v) :
    ∃ s : core (Fin 5) →ₗ[ZMod 2] V,
      (∀ w, p (s w) = w) ∧
      (∀ g w, s (coreRepresentation (Fin 5) g w) = ρ g (s w)) ∧
      s.range = subspaceCommutator ρ ⊤ (alternatingGroup (Fin 5)) :=
  exists_moved_section ρ p hp (equivariant_of_alternating ρ p hp he hk) hk
end BinaryPermutation.FiveCentralExtension
