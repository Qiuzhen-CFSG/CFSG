module

public import Theory.SpecificGroups.Janko3.Model.ThreeCoverLocalConfiguration.Relations
public import Theory.GroupTheory.CentralThreeInvertedPlane

/-!
# The marked elementary plane in the J₃ affine local

The commuting cubic words give a homomorphism from two copies of Z/3. Its
nine coordinate products have distinct images of letter zero, proving
injectivity in the actual degree-6156 model. Both generators normalize the
same nontrivial elementary two-subgroup. The first factor centralizes the
whole right support, by its two generator commutation certificates.

Source: GLS, Number 3, Table 5.3h, printed p.269; Aschbacher--Smith A.2.19,
printed p.41. Perfectness and cyclic Sylow three-subgroups of the supports
are separate inputs to the final configuration construction.
-/

namespace Sporadic.Janko3.ThreeCoverConfig
open Subgroup
set_option maxRecDepth 40000

/-- The actual pair of commuting cubic model elements, in the configuration's
literal product convention. -/
@[expose] public def plane :
    (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) →* Model :=
  (MonoidHom.cubicPairHom x y x_cube y_cube xy).comp
    (MulEquiv.prodMultiplicative (ZMod 3) (ZMod 3)).symm.toMonoidHom

public theorem plane_apply (a : Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) :
    plane a = x ^ a.1.toAdd.val * y ^ a.2.toAdd.val := rfl

public theorem plane_left (a : Multiplicative (ZMod 3)) :
    plane (a, 1) = x ^ a.toAdd.val := by
  simp only [plane_apply]
  change x ^ a.toAdd.val * y ^ 0 = x ^ a.toAdd.val
  rw [pow_zero, mul_one]

public theorem plane_right (b : Multiplicative (ZMod 3)) :
    plane (1, b) = y ^ b.toAdd.val := by
  simp only [plane_apply]
  change x ^ 0 * y ^ b.toAdd.val = y ^ b.toAdd.val
  rw [pow_zero, one_mul]

/-- A single-letter action detects the kernel of the nine-element plane. -/
public theorem plane_injective : Function.Injective plane := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro a ha
  have h : ∀ b : Multiplicative (ZMod 3) × Multiplicative (ZMod 3),
      (xPerm ^ b.1.toAdd.val * yPerm ^ b.2.toAdd.val) 0 = 0 → b = 1 := by
    decide +kernel
  apply h a
  have hv := congrArg (fun g : Model => (g : Equiv.Perm (Fin 6156)) 0) ha
  change ((x : Equiv.Perm (Fin 6156)) ^ a.1.toAdd.val *
    (y : Equiv.Perm (Fin 6156)) ^ a.2.toAdd.val) 0 = 0 at hv
  rwa [xPerm_eq, yPerm_eq]

public theorem plane_normalizes (a : Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) :
    plane a ∈ normalizer (twoSubgroup : Set Model) := by
  rw [plane_apply]
  exact (normalizer _).mul_mem ((normalizer _).pow_mem x_normalizes _)
    ((normalizer _).pow_mem y_normalizes _)

public theorem plane_left_centralizes (a : Multiplicative (ZMod 3)) :
    plane (a, 1) ∈ centralizer (rightSupport : Set Model) := by
  rw [plane_left]
  exact (centralizer _).pow_mem x_centralizes_right _

/-- Membership of the marked scalar suffices for the whole first factor. -/
public theorem plane_left_mem (hx : x ∈ leftSupport) (a : Multiplicative (ZMod 3)) :
    plane (a, 1) ∈ leftSupport := by
  rw [plane_left]
  exact leftSupport.pow_mem hx _

/-- Membership of the marked right element suffices for the whole second factor. -/
public theorem plane_right_mem (hy : y ∈ rightSupport) (b : Multiplicative (ZMod 3)) :
    plane (1, b) ∈ rightSupport := by
  rw [plane_right]
  exact rightSupport.pow_mem hy _

end Sporadic.Janko3.ThreeCoverConfig
