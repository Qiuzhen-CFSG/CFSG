module

public import CFSG.Quasithin.ChapterJ.Defs
public import Theory.Representation.SL2FourNaturalOrbits.SelfDual
public import Mathlib.RepresentationTheory.Intertwining
public import Theory.Representation.BinaryInvolutoryExtension

/-!
# Self-duality of the original marked S₅ action

The trace-determinant pairing is fixed by the alternating subgroup. On the
space of maps to the dual, add this pairing to its translate by a transposition.
The sum is invariant under S₅; if it vanishes, the original pairing is already
invariant in characteristic two. A nonzero invariant map has zero kernel
because the marked SL₂(4) is transitive on nonzero vectors. Equal dimensions
then give a linear equivalence with the contragredient of the given action.

The action and the SL₂(4) marking in `ChapterJ.L2FourAction` are preserved.
Source application: Aschbacher–Smith, 14.7.71(1), printed p.1075, identifying
the commutator-dual chief factor with the original natural module; the duality
itself comes from 14.5.21(1), printed pp.1019–1020.
-/

public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ.L2FourAction
variable (r : L2FourAction)

private theorem pairing_fixed (g : S5) (hg : g ∈ alternatingGroup (Fin 5)) :
    Representation.linHom r.action r.action.dual g SL2FourNatural.binaryPairing =
      SL2FourNatural.binaryPairing := by
  obtain ⟨a, ha⟩ := r.marking.surjective ⟨g⁻¹, (alternatingGroup (Fin 5)).inv_mem hg⟩
  have he : (r.marking a : S5) = g⁻¹ := congrArg Subtype.val ha
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  change SL2FourNatural.binaryPairing (r.action g⁻¹ v) (r.action g⁻¹ w) =
    SL2FourNatural.binaryPairing v w
  rw [← he, r.restriction, r.restriction]
  exact SL2FourNatural.binaryPairing_invariant a v w

private theorem exists_selfDual_map :
    ∃ f : FourSpace →ₗ[ZMod 2] Module.Dual (ZMod 2) FourSpace,
      f ≠ 0 ∧ ∀ g v, f (r.action g v) = r.action.dual g (f v) := by
  let t : S5 := Equiv.swap 0 1
  have ht : t * t = 1 := Equiv.swap_mul_self 0 1
  have hcoset (g : S5) :
      g ∈ alternatingGroup (Fin 5) ∨ g * t ∈ alternatingGroup (Fin 5) := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hg | hg
    · exact Or.inl (Equiv.Perm.mem_alternatingGroup.mpr hg)
    · right
      simp only [Equiv.Perm.mem_alternatingGroup, map_mul, hg, t,
        Equiv.Perm.sign_swap (by decide : (0 : Fin 5) ≠ 1), neg_mul_neg, one_mul]
  obtain ⟨f, hf, hfix⟩ := Representation.exists_fixed_ne_zero_of_involutory_extension
    (Representation.linHom r.action r.action.dual) (alternatingGroup (Fin 5)) t ht hcoset
    SL2FourNatural.binaryPairing
    (LinearMap.ne_zero_of_injective SL2FourNatural.binaryPairing_injective) (pairing_fixed r)
  refine ⟨f, hf, fun g v => ?_⟩
  have he := LinearMap.congr_fun (hfix g) (r.action g v)
  simpa only [Representation.linHom_apply, LinearMap.comp_apply,
    ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply] using he.symm

private theorem selfDual_map_injective
    (f : FourSpace →ₗ[ZMod 2] Module.Dual (ZMod 2) FourSpace) (hf : f ≠ 0)
    (he : ∀ g v, f (r.action g v) = r.action.dual g (f v)) : Function.Injective f := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  by_contra hv0
  apply hf
  apply LinearMap.ext
  intro w
  by_cases hw : w = 0
  · subst w
    exact f.map_zero
  obtain ⟨g, hg⟩ := SL2FourNatural.transitive_nonzero v w hv0 hw
  have he' := he (r.marking g) v
  rw [r.restriction, hg, hv, map_zero] at he'
  exact he'

/-- An equivariant self-duality for the given full S₅ action. -/
def selfDual : r.action.Equiv r.action.dual := by
  let f := Classical.choose (exists_selfDual_map r)
  have hf := (Classical.choose_spec (exists_selfDual_map r)).1
  have he := (Classical.choose_spec (exists_selfDual_map r)).2
  let j : IntertwiningMap r.action r.action.dual :=
    f.intertwiningMap_of_isIntertwiningMap _ _ he
  have hinj := selfDual_map_injective r f hf he
  exact j.ofBijective ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ZMod 2) (V := FourSpace)).symm).mp hinj⟩

/-- Equivariance holds for every S₅ actor, including odd permutations. -/
theorem selfDual_equivariant (g : S5) (v : FourSpace) :
    (selfDual r).toLinearEquiv (r.action g v) =
      r.action.dual g ((selfDual r).toLinearEquiv v) :=
  LinearMap.congr_fun ((selfDual r).isIntertwining' g) v

end CFSG.Quasithin.ChapterJ.L2FourAction
