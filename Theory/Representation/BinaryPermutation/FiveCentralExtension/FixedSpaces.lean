module

public import Theory.Representation.BinaryPermutation.FiveCentralExtension
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryPermutation.OddOffenderTransport
import Mathlib.Tactic


/-!
# Fixed codimensions in natural S₅ extensions

The class-sum section gives an equivariant product decomposition into the
actual quotient and its kernel. Fixed codimensions therefore add, with the
kernel retaining its possibly nontrivial S₅-action.

Source: Aschbacher–Smith, C.1.24 and E.2.3, printed pp.130–131 and 216–217.
-/

@[expose] public section

namespace BinaryPermutation.FiveCentralExtension
open Representation.BinaryOffender
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) Sym V)
    (p : V →ₗ[ZMod 2] core (Fin 5))
    (he : ∀ g v, p (ρ g v) = coreRepresentation (Fin 5) g (p v))

def kernelRepresentation : Representation (ZMod 2) Sym p.ker where
  toFun g := (ρ g).restrict (by intro v hv; change p (ρ g v) = 0; rw [he, hv, map_zero])
  map_one' := by ext v; simp
  map_mul' := by intros; ext; simp [map_mul, Module.End.mul_apply]

private def splitEquiv (s : core (Fin 5) →ₗ[ZMod 2] V) (hs : ∀ v, p (s v) = v) :
    V ≃ₗ[ZMod 2] (core (Fin 5)) × p.ker where
  toFun v := (p v, ⟨v - s (p v), by change p (v - s (p v)) = 0; rw [map_sub, hs, sub_self]⟩)
  invFun v := s v.1 + v.2.val
  left_inv v := by simp
  right_inv v := by
    rcases v with ⟨v, w⟩
    apply Prod.ext
    · simp [hs]
    · apply Subtype.ext
      simp [hs]
  map_add' v w := by apply Prod.ext; exact map_add _ _ _; apply Subtype.ext; simp [map_add]; abel
  map_smul' r v := by apply Prod.ext; exact map_smul _ _ _; apply Subtype.ext; simp [map_smul, smul_sub]

private theorem splitEquiv_equivariant
    (s : core (Fin 5) →ₗ[ZMod 2] V) (hs : ∀ v, p (s v) = v)
    (hse : ∀ g v, s (coreRepresentation (Fin 5) g v) = ρ g (s v))
    (g : Sym) (v : V) :
    splitEquiv p s hs (ρ g v) =
      ((coreRepresentation (Fin 5)).prod (kernelRepresentation ρ p he)) g
        (splitEquiv p s hs v) := by
  apply Prod.ext
  · exact he g v
  · apply Subtype.ext
    change ρ g v - s (p (ρ g v)) = ρ g (v - s (p v))
    rw [he, hse, map_sub]

theorem fixedCodim_split [FiniteDimensional (ZMod 2) V]
    (hp : Function.Surjective p)
    (hk : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5), ρ g v = v)
    (A : Subgroup Sym) :
    fixedCodim ρ A = fixedCodim (coreRepresentation (Fin 5)) A +
      fixedCodim (kernelRepresentation ρ p he) A := by
  obtain ⟨s, hs, hse, _⟩ := exists_section ρ p hp he hk
  rw [OddTransport.fixedCodim_eq_of_equivariant ρ _
    (splitEquiv p s hs) (splitEquiv_equivariant ρ p he s hs hse), fixedCodim_prod]
end BinaryPermutation.FiveCentralExtension
