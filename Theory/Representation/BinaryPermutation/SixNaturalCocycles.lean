module
public import Theory.Representation.BinaryAlternatingNaturalCohomology.Even
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Natural A₆ cocycles as the deleted six-letter module

Every cocycle on the natural binary A₆ module is a displacement of a full
permutation vector. The existing point-stabilizer normalization supplies the
surjectivity; the displacement kernel is precisely the constant line.
Thus the cocycle space is the actual five-dimensional deleted module.

Source: Aschbacher–Smith I.1.6(1), applied in 14.3.19(10).
-/

namespace BinaryPermutation.SixNaturalCocycles
open Representation.OneCohomology
local notation "ρ" => alternatingNaturalRepresentation (Fin 6)

public theorem displacement_surjective : Function.Surjective (naturalDisplacement (Fin 6)) := by
  intro f
  obtain ⟨v,hv⟩ := alternatingNatural_normalize_pointStabilizer 6 (Or.inl rfl) 0 f
  obtain ⟨a,ha⟩ := alternatingNatural_normalized_eq_coordinate 6 (Or.inl rfl) 0
    (f - principal ρ v) (by
      intro g hg
      change f.val g - (ρ g v-v)=0
      rw [hv g hg,sub_self])
  obtain ⟨w,hw,hwv⟩ := v.property
  let u : core (Fin 6) := ⟨w,hw⟩
  have hu : coreToNatural (Fin 6) u=v := Subtype.ext hwv
  refine ⟨a • Pi.single 0 1 + u.val,?_⟩
  rw [map_add,map_smul,naturalDisplacement_core,hu]
  change a • naturalCoordinateCocycle (Fin 6) 0 + principal ρ v = f
  rw [← ha]
  exact sub_add_cancel f (principal ρ v)

public theorem displacement_ker : (naturalDisplacement (Fin 6)).ker=constants (Fin 6) := by
  ext w
  exact naturalDisplacement_eq_zero_iff (Fin 6) (by simp) w

public noncomputable def deletedEquiv : Deleted (Fin 6) ≃ₗ[ZMod 2] cocycles ρ :=
  (Submodule.quotEquivOfEq (constants (Fin 6)) (naturalDisplacement (Fin 6)).ker
    displacement_ker.symm).trans
      ((naturalDisplacement (Fin 6)).quotKerEquivOfSurjective displacement_surjective)

public theorem deletedEquiv_mk (w : Full (Fin 6)) :
    deletedEquiv ((constants (Fin 6)).mkQ w) = naturalDisplacement (Fin 6) w := by
  simp [deletedEquiv]

public theorem cocycles_card : Nat.card (cocycles ρ)=32 := by
  rw [← Nat.card_congr deletedEquiv.toEquiv]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,finrank_deleted]
  decide
public theorem deletedEquiv_action (s : Equiv.Perm (Fin 6)) (d : Deleted (Fin 6))
    (g : alternatingGroup (Fin 6)) :
    (deletedEquiv (deletedRepresentation (Fin 6) s d)).val (MulAut.conjNormal s g) =
      naturalRepresentation (Fin 6) s ((deletedEquiv d).val g) := by
  obtain ⟨w,rfl⟩ := (constants (Fin 6)).mkQ_surjective d
  rw [deletedRepresentation_mk,deletedEquiv_mk,deletedEquiv_mk]
  apply Subtype.ext
  change (constants (Fin 6)).mkQ
    (representation (Fin 6) (s*g.val*s⁻¹) (representation (Fin 6) s w) - representation (Fin 6) s w) =
      deletedRepresentation (Fin 6) s ((constants (Fin 6)).mkQ (representation (Fin 6) g.val w-w))
  have he : representation (Fin 6) (s*g.val*s⁻¹) (representation (Fin 6) s w) =
      representation (Fin 6) s (representation (Fin 6) g.val w) := by
    rw [← Module.End.mul_apply,← map_mul,← Module.End.mul_apply,← map_mul]
    congr 2
    group
  rw [deletedRepresentation_mk,(representation (Fin 6) s).map_sub,he]
end BinaryPermutation.SixNaturalCocycles
