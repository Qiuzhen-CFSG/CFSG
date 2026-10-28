module
public import Theory.Representation.BinaryPermutation.FiveCentralExtension.OuterCompatibility
public import Theory.Alternating.Aut

/-!
# Normalizers of the five-letter core action

An automorphism of the symmetric group restricts to its characteristic A₅.
Aut(A₅)=S₅ gives the required actual permutation. Correcting by that permutation
leaves a linear map commuting with A₅, which is the identity over F₂.
The paired S₅ Baumann application uses this after fixing the two factors.

Source: Aschbacher–Smith C.1.24 and E.2.3(3), pp.130–131 and216–217.
-/

public section
namespace BinaryPermutation.FiveCoreNormalizer
open FiveCentralExtension

/-- Every normalizer of the marked five-letter natural action is the actual
permutation action. The inducing automorphism is allowed to be arbitrary. -/
theorem normalizer
    (f : core (Fin 5) ≃ₗ[ZMod 2] core (Fin 5)) (φ : MulAut Sym)
    (hf : ∀ g v, f (coreRepresentation (Fin 5) g v) =
      coreRepresentation (Fin 5) (φ g) (f v)) :
    ∃ s : Sym, ∀ v, f v = coreRepresentation (Fin 5) s v := by
  let φA : MulAut (alternatingGroup (Fin 5)) := MulAut.characteristic _ φ
  obtain ⟨s,hs⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
    (by decide) (by decide)).surjective φA
  have hφ (g : alternatingGroup (Fin 5)) : φ (g : Sym) = s * (g : Sym) * s⁻¹ := by
    have hh := congrArg (fun ψ : MulAut (alternatingGroup (Fin 5)) => ((ψ g : alternatingGroup (Fin 5)) : Sym)) hs
    exact hh.symm
  let F : core (Fin 5) →ₗ[ZMod 2] core (Fin 5) :=
    (coreRepresentation (Fin 5) s⁻¹).comp f.toLinearMap
  have hF : ∀ v, F v = v := by
    apply core_commuting_eq_id F
    · intro g hg v
      change coreRepresentation (Fin 5) s⁻¹ (f (coreRepresentation (Fin 5) g v)) =
        coreRepresentation (Fin 5) g (coreRepresentation (Fin 5) s⁻¹ (f v))
      rw [hf,hφ ⟨g,hg⟩]
      simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel_left]
    · exact ((coreRepresentation (Fin 5)).apply_bijective s⁻¹).1.comp f.injective
  refine ⟨s,fun v => ?_⟩
  have hh := congrArg (coreRepresentation (Fin 5) s) (hF v)
  change coreRepresentation (Fin 5) s (coreRepresentation (Fin 5) s⁻¹ (f v)) = _ at hh
  simpa only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply] using hh

end BinaryPermutation.FiveCoreNormalizer
