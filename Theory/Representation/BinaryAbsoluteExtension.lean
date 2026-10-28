module

public import Theory.Representation.AbsolutelyIrreducible
public import Theory.Representation.RepEquiv
public import Theory.Representation.Quotient
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases

/-!
# Rigidity of extensions of absolutely irreducible binary actions

Conjugating an intertwiner by an ambient element differs from the original
intertwiner by an endomorphism of the normal restricted representation.
Absolute irreducibility makes this a scalar, and the only invertible scalar
in F₂ is one. Consequently the same marked linear map intertwines the whole
action. The M₂₂ code and cocode source recognition applies this to F*(G).

Source application: Aschbacher–Smith H.13.2 and K.4, printed pp.395 and 457.
-/

public section
namespace Representation
variable {G H V W : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

omit [FiniteDimensional (ZMod 2) W] in
/-- Absolute irreducibility is preserved by a surjective change of actor. -/
theorem binary_absolute_comp_surjective (σ : Representation (ZMod 2) H W)
    (f : G →* H) (hf : Function.Surjective f) (ha : σ.IsAbsolutelyIrreducible) :
    IsAbsolutelyIrreducible (σ.comp f) := by
  constructor
  let := ha.irreducible_of_closure
  exact (irreducible_comp_surjective_iff f hf
    (extendScalars (AlgebraicClosure (ZMod 2)) σ)).mpr inferInstance

/-- A fixed equivalence on a normal absolutely irreducible binary restriction
intertwines the entire ambient action. There is no nontrivial binary scalar twist. -/
theorem binary_extension_intertwining (ρ : Representation (ZMod 2) G V)
    (σ : Representation (ZMod 2) G W) (N : Subgroup G) [N.Normal]
    (ha : IsAbsolutelyIrreducible (σ.comp N.subtype))
    (E : Equiv (ρ.comp N.subtype) (σ.comp N.subtype)) :
    ∀ g v, E (ρ g v) = σ g (E v) := by
  let : IsAbsolutelyIrreducible (σ.comp N.subtype) := ha
  let : IsIrreducible (σ.comp N.subtype) :=
    IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible _
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial (σ.comp N.subtype)
  have hE (n : N) (v : V) : E (ρ n v) = σ n (E v) :=
    LinearMap.congr_fun (E.isIntertwining' n) v
  intro g
  let f : End (σ.comp N.subtype) := {
    toLinearMap := (σ g⁻¹).comp (E.toLinearMap.comp ((ρ g).comp E.symm.toLinearMap))
    isIntertwining' := by
      intro n
      let n' : N := ⟨g * n * g⁻¹, (inferInstance : N.Normal).conj_mem n n.property g⟩
      have he (w : W) : E.symm (σ n w) = ρ n (E.symm w) :=
        LinearMap.congr_fun (E.symm.isIntertwining' n) w
      have hgn : g * (n : G) = (n' : G) * g := by simp [n', mul_assoc]
      have hng : g⁻¹ * (n' : G) = (n : G) * g⁻¹ := by simp [n', mul_assoc]
      apply LinearMap.ext
      intro w
      change σ g⁻¹ (E (ρ g (E.symm (σ n w)))) =
        σ n (σ g⁻¹ (E (ρ g (E.symm w))))
      rw [he]
      have h1 : ρ g (ρ n (E.symm w)) = ρ n' (ρ g (E.symm w)) := by
        change (ρ g * ρ n) _ = (ρ n' * ρ g) _
        rw [← map_mul, ← map_mul, hgn]
      rw [h1, hE]
      change (σ g⁻¹ * σ n') _ = (σ n * σ g⁻¹) _
      rw [← map_mul, ← map_mul, hng] }
  obtain ⟨c, hc⟩ := (isAbsolutelyIrreducible_iff_surjective (σ.comp N.subtype)).mp ha f
  have hscalar (w : W) : σ g⁻¹ (E (ρ g (E.symm w))) = c • w :=
    (congrArg (fun q : End (σ.comp N.subtype) => q w) hc).symm
  have hc0 : c ≠ 0 := by
    intro hz
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    have hzero := hscalar w
    rw [hz, zero_smul] at hzero
    have hinj : Function.Injective (fun w => σ g⁻¹ (E (ρ g (E.symm w)))) :=
      (LinearMap.GeneralLinearGroup.toLinearEquiv (σ.asGroupHom g⁻¹)).injective.comp
        (E.injective.comp ((LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)).injective.comp E.symm.injective))
    apply hw
    apply hinj
    simpa using hzero
  have hc1 : c = 1 := by
    fin_cases c
    · exact (hc0 rfl).elim
    · rfl
  intro v
  have hv := hscalar (E v)
  simp only [Equiv.symm_apply_apply, hc1, one_smul] at hv
  have hh := congrArg (σ g) hv
  change (σ g * σ g⁻¹) (E (ρ g v)) = _ at hh
  simpa only [← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] using hh
end Representation
