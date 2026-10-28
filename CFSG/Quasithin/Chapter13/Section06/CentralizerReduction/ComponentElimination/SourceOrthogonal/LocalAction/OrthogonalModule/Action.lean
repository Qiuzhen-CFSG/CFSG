module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.Representation.BinaryPermutation
public import Theory.Representation.SubspaceQuotient

/-!
# The binary plus action on the original seed span

The underlying module here is the additive form of the literal W_K. The
projection contract describes W_K/C_{W_K}(K) as the natural eight-point
module, with one chosen ambient actor marking and an equivariant map. It
retains the fixed kernel; it asserts no splitting and contains no seed
stabilizer or centralizer conclusion. Constructing it from the full B.5.1
alternatives and the middle-node parabolic remains the recognition step.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the paragraph following 13.6.23, printed p.933 (PDF p.950).
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule
open ComponentSelection
variable {G : Type*} [Group G] (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]

/-- The faithful plus action, linearized on its original elementary abelian group. -/
noncomputable def representation : Representation (ZMod 2)
    (Gplus K L T z v hL hz) (Additive (WK K L T z v)) where
  toFun g := (plusAction K L T z v hL hz g).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro x
    change Additive.ofMul (plusAction K L T z v hL hz 1 x.toMul) = x
    rw [map_one]
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro x
    change Additive.ofMul (plusAction K L T z v hL hz (a * b) x.toMul) = _
    rw [map_mul]
    rfl

/-- This is precisely the published plus action, not a separate module action. -/
theorem representation_apply (g : Gplus K L T z v hL hz) (w : WK K L T z v) :
    representation K L T z v hL hz g (Additive.ofMul w) =
      Additive.ofMul (plusAction K L T z v hL hz g w) := rfl

/-- The linear action is faithful because the literal plus action is faithful. -/
theorem representation_injective : Function.Injective (representation K L T z v hL hz) := by
  intro a b hab
  apply plusAction_injective K L T z v hL hz
  apply MulEquiv.ext
  intro w
  exact congrArg Additive.toMul (DFunLike.congr_fun hab (Additive.ofMul w))

/-- The source moved section U_K/C_{U_K}(K), with its full ambient action.
The upper space is the literal commutator subgroup; neither K nor an arbitrary
six-dimensional space can be substituted for it. -/
structure NaturalMovedSection where
  actor : Gplus K L T z v hL hz ≃* Equiv.Perm (Fin 8)
  component_image : (plusImage K L T z v hL hz K).map actor.toMonoidHom =
    alternatingGroup (Fin 8)
  upper : Subrepresentation (representation K L T z v hL hz)
  upper_mem : ∀ w : Additive (WK K L T z v), w ∈ upper.toSubmodule ↔
    (w.toMul : G) ∈ ⁅WK K L T z v, K⁆
  central : Subrepresentation upper.toRepresentation
  central_mem : ∀ w : upper.toSubmodule, w ∈ central.toSubmodule ↔
    (w.val.toMul : G) ∈ centralizer (K : Set G)
  coordinates : (upper.toSubmodule ⧸ central.toSubmodule) ≃ₗ[ZMod 2]
    BinaryPermutation.natural (Fin 8)
  equivariant : ∀ g w, coordinates (central.quotientRepresentation g w) =
    BinaryPermutation.naturalRepresentation (Fin 8) (actor g) (coordinates w)

/-- A chosen natural quotient, with the component and its entire fixed kernel
specified. This is recognition data to construct, not an earlier source theorem. -/
structure NaturalSeedSection where
  actor : Gplus K L T z v hL hz ≃* Equiv.Perm (Fin 8)
  component_image : (plusImage K L T z v hL hz K).map actor.toMonoidHom =
    alternatingGroup (Fin 8)
  projection : Additive (WK K L T z v) →ₗ[ZMod 2] BinaryPermutation.natural (Fin 8)
  surjective : Function.Surjective projection
  equivariant : ∀ g w, projection (representation K L T z v hL hz g w) =
    BinaryPermutation.naturalRepresentation (Fin 8) (actor g) (projection w)
  kernel : ∀ w, projection w = 0 ↔
    ∀ k : plusImage K L T z v hL hz K, representation K L T z v hL hz k w = w

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule
