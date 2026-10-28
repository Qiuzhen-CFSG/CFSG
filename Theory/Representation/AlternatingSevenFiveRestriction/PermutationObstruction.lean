module
public import Theory.SpecificGroups.Alternating.SevenFivePlacement.ThreeCycles
public import Theory.Representation.BinaryAlternatingSevenFixedPoints
public import Theory.Representation.AlternatingFiveLinearTwoObstruction

/-!
# The five-point permutation core does not occur in an A₇ four-space

Every cubic in the actual normalized A₅ is a three-cycle of A₇. Such a
three-cycle acts without fixed vectors on a faithful binary four-space, whereas
a cubic in the five-point core fixes a nonzero vector. The contradiction keeps
the original subgroup, its full Sylow normalizer, and the specified intertwiner.
Source: Aschbacher–Smith, C.5.13, printed p.163.
-/
public section
namespace Representation.AlternatingSevenFiveRestriction
open Subgroup
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
local notation "A7" => alternatingGroup (Fin 7)

theorem no_permutation_core_injection
    (ρ : Representation (ZMod 2) A7 V) (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) V = 4)
    (B : Subgroup A7) (e : B ≃* alternatingGroup (Fin 5))
    (S : Sylow 2 A7) (hSN : (S : Subgroup A7) ≤ normalizer (B : Set A7))
    (j : BinaryPermutation.core (Fin 5) →+ V) (hj : Function.Injective j)
    (heq : ∀ (b : B) v, ρ b (j v) =
      j (BinaryPermutation.coreRepresentation (Fin 5) (e b).val v)) : False := by
  obtain ⟨a, ha, v, hv, hfix⟩ :=
    BinaryPermutation.AlternatingFiveLinearTwo.exists_cubic_fixed_ne_zero
  let b := e.symm a
  have hb : orderOf b = 3 := (orderOf_injective e.toMonoidHom e.injective b).symm.trans
    (by simpa only [b, MulEquiv.coe_toMonoidHom, e.apply_symm_apply] using ha)
  have hcycle := Theory.SpecificGroups.Alternating.SevenFivePlacement.isThreeCycle_of_order_three
    B e S hSN b hb
  have hfixed : ρ b (j v) = j v := by
    rw [heq, show e b = a from e.apply_symm_apply a, hfix]
  have hz := binaryAlternatingSeven_threeCycle_fixedPointFree ρ hρ hdim b.val hcycle (j v) hfixed
  exact hv (hj (hz.trans j.map_zero.symm))
end Representation.AlternatingSevenFiveRestriction
