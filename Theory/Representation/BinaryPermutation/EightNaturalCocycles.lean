module
public import Theory.Representation.BinaryAlternatingNaturalCohomology.Even
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Natural A₈ cocycles as the deleted eight-letter module

Every cocycle on the natural binary A₈ module is a displacement of a full
permutation vector. The existing point-stabilizer normalization supplies the
surjectivity; the displacement kernel is precisely the constant line.
Thus the cocycle space is the actual seven-dimensional deleted module.

Source: Aschbacher–Smith I.1.6(1), applied in 12.6.2, printed p.828.
-/

namespace BinaryPermutation.EightNaturalCocycles
open Representation.OneCohomology
local notation "ρ" => alternatingNaturalRepresentation (Fin 8)

public theorem displacement_surjective : Function.Surjective (naturalDisplacement (Fin 8)) := by
  intro f
  obtain ⟨v,hv⟩ := alternatingNatural_normalize_pointStabilizer 8 (Or.inr rfl) 0 f
  obtain ⟨a,ha⟩ := alternatingNatural_normalized_eq_coordinate 8 (Or.inr rfl) 0
    (f - principal ρ v) (by
      intro g hg
      change f.val g - (ρ g v-v)=0
      rw [hv g hg,sub_self])
  obtain ⟨w,hw,hwv⟩ := v.property
  let u : core (Fin 8) := ⟨w,hw⟩
  have hu : coreToNatural (Fin 8) u=v := Subtype.ext hwv
  refine ⟨a • Pi.single 0 1 + u.val,?_⟩
  rw [map_add,map_smul,naturalDisplacement_core,hu]
  change a • naturalCoordinateCocycle (Fin 8) 0 + principal ρ v = f
  rw [← ha]
  exact sub_add_cancel f (principal ρ v)

public theorem displacement_ker : (naturalDisplacement (Fin 8)).ker=constants (Fin 8) := by
  ext w
  exact naturalDisplacement_eq_zero_iff (Fin 8) (by simp) w

public noncomputable def deletedEquiv : Deleted (Fin 8) ≃ₗ[ZMod 2] cocycles ρ :=
  (Submodule.quotEquivOfEq (constants (Fin 8)) (naturalDisplacement (Fin 8)).ker
    displacement_ker.symm).trans
      ((naturalDisplacement (Fin 8)).quotKerEquivOfSurjective displacement_surjective)

public theorem deletedEquiv_mk (w : Full (Fin 8)) :
    deletedEquiv ((constants (Fin 8)).mkQ w) = naturalDisplacement (Fin 8) w := by
  simp [deletedEquiv]

public theorem cocycles_card : Nat.card (cocycles ρ)=128 := by
  rw [← Nat.card_congr deletedEquiv.toEquiv]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,finrank_deleted]
  decide
end BinaryPermutation.EightNaturalCocycles
