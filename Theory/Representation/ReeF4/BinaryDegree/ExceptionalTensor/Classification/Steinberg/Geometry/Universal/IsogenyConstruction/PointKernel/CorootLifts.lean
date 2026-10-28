module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.TorusLift
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.Coroots
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Basic
public import Theory.AlgebraicGroup.Morphism.RegularLift
public import Theory.AlgebraicGroup.Morphism.Power
public import Theory.AlgebraicGroup.RootSubgroups.BinaryCorootWord

/-!
# Constructing torus lifts from regular root words

A regular normalized lift of a powered cocharacter is automatically a group
morphism: its multiplicative defect is a connected finite image. Its image
is connected and lies in the torus preimage, hence lies in its identity
component. Thus regular lifts of two opposite root curves, with their target
coroot-word identity, give an actual cocharacter in the connected torus lift.

The geometric inputs remain explicit: regular characteristic-power lifts of
root curves and the target coroot-word identity. They are not asserted here
from the isogeny hypotheses. No source root model, kernel containment, or
regular inverse to an inseparable isogeny is used. The final four-coroot
assembly is conditional until those two geometric inputs are constructed.

Source: GLS3, Theorem 1.12.1(c)--(d) and the criterion in Theorem 1.12.5(b),
`refs/KGroup/GLS3/Chapter1.tex`.
-/

public section
universe u
namespace Theory.AlgebraicGroup
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A regular normalized lift of a powered cocharacter factors as an actual
cocharacter of the connected torus preimage. -/
theorem exists_isogenyTorusLift_cocharacter_of_regular_lift
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (φ : Morphism H G) (hfinite : Finite φ.kernel) (T : ClosedSubgroup G)
    (c : Morphism (KMult k) T.carrierVariety) (n : ℕ)
    (f : Variety.Morphism (KMult k) H) (hf : f.toFun 1 = 1)
    (hcomp : ∀ t, φ.onPoints (f.toFun t) = T.inclusion.onPoints (c.onPoints (t ^ n))) :
    ∃ μ : Morphism (KMult k) (isogenyTorusLift φ T).carrierVariety,
      ∀ t, (isogenyTorusLiftMap φ T).onPoints (μ.onPoints t) = c.onPoints (t ^ n) := by
  let p := commutativeNpowMorphism (KMult k) (dVariety_isMulCommutative 1) n
  let g := T.inclusion.comp (c.comp p)
  have hfg : ∀ t, φ.onPoints (f.toFun t) = g.onPoints t := by
    intro t
    change φ.onPoints (f.toFun t) = T.inclusion.onPoints (c.onPoints ((npowMorphism _ n).toFun t))
    rw [npowMorphism_apply]
    exact hcomp t
  have hc : Variety.IsConnected (KMult k) := (dVariety_isTorus 1).isConnected
  let l := φ.regularLift hfinite hc f hf g hfg
  let P := φ.closedSubgroupPreimage T
  let S := isogenyTorusLift φ T
  have hle : l.imageClosedSubgroup ≤ P := by
    rintro _ ⟨t, rfl⟩
    change φ.onPoints (l.onPoints t) ∈ T
    rw [Morphism.regularLift_apply, hcomp]
    exact (T.pointEquiv (c.onPoints (t ^ n))).property
  have hleS : l.imageClosedSubgroup ≤ S :=
    connected_closedSubgroup_le_identityComponentAmbient
      l.imageClosedSubgroup P (l.imageClosedSubgroup_isConnected hc) hle
  let μ := l.codRestrictClosedSubgroup S (fun t => hleS ⟨t, rfl⟩)
  refine ⟨μ, fun t => T.inclusion_injective ?_⟩
  rw [isogenyTorusLiftMap_apply]
  rw [show S.inclusion.onPoints (μ.onPoints t) = l.onPoints t from
    Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ t]
  rw [Morphism.regularLift_apply]
  exact hcomp t

/-- Opposite regular curve lifts produce a cocharacter lift once the target
curves satisfy the actual coroot-word identity. -/
theorem exists_isogenyTorusLift_cocharacter_of_binary_root_words
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (φ : Morphism H G) (hfinite : Finite φ.kernel) (T : ClosedSubgroup G)
    (c : Morphism (KMult k) T.carrierVariety)
    (x y : Variety.Morphism (KPlus k) G)
    (hword : ∀ t, (binaryCorootWord x y).toFun t = T.inclusion.onPoints (c.onPoints t))
    (xH yH : Variety.Morphism (KPlus k) H) (n : ℕ)
    (hx : ∀ s, φ.onPoints (xH.toFun (kPlusPoint s)) = x.toFun (kPlusPoint (s ^ n)))
    (hy : ∀ s, φ.onPoints (yH.toFun (kPlusPoint s)) = y.toFun (kPlusPoint (s ^ n))) :
    ∃ μ : Morphism (KMult k) (isogenyTorusLift φ T).carrierVariety,
      ∀ t, (isogenyTorusLiftMap φ T).onPoints (μ.onPoints t) = c.onPoints (t ^ n) := by
  apply exists_isogenyTorusLift_cocharacter_of_regular_lift φ hfinite T c n
    (binaryCorootWord xH yH) (binaryCorootWord_one xH yH)
  intro t
  rw [binaryCorootWord_map_of_parameter_power φ x y xH yH n hx hy, hword]

namespace RootSystemModel
open StandardRootSystem

/-- Four independent characteristic-power root-word lifts give the four
actual standard-base coroot lifts. The two geometric inputs are explicit. -/
theorem f4_coroot_power_lifts_of_root_curve_lifts
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (M : RootSystemModel typeF4RootPairingULift G)
    (φ : Morphism H G) (hφ : IsIsogeny φ)
    (x y : Fin 4 → Variety.Morphism (KPlus k) G)
    (hword : ∀ i t, (binaryCorootWord (x i) (y i)).toFun t =
      M.torus.inclusion.onPoints ((M.rootData.rootCocharacter (M.f4SimpleRoot i)).onPoints t))
    (hx : ∀ i, ∃ a : ℕ, ∃ xH : Variety.Morphism (KPlus k) H,
      ∀ s, φ.onPoints (xH.toFun (kPlusPoint s)) =
        (x i).toFun (kPlusPoint (s ^ (2 ^ a))))
    (hy : ∀ i, ∃ b : ℕ, ∃ yH : Variety.Morphism (KPlus k) H,
      ∀ s, φ.onPoints (yH.toFun (kPlusPoint s)) =
        (y i).toFun (kPlusPoint (s ^ (2 ^ b)))) :
    ∃ a : Fin 4 → ℕ,
      ∃ μ : Fin 4 → Morphism (KMult k) (isogenyTorusLift φ M.torus).carrierVariety,
      ∀ i t, (isogenyTorusLiftMap φ M.torus).onPoints ((μ i).onPoints t) =
        (M.rootData.rootCocharacter (M.f4SimpleRoot i)).onPoints (t ^ (2 ^ a i)) := by
  choose a xH yH hxH hyH using fun i =>
    exists_common_binary_parameter_lifts φ (x i) (y i) (hx i) (hy i)
  choose μ hμ using fun i =>
    exists_isogenyTorusLift_cocharacter_of_binary_root_words φ hφ.2 M.torus
      (M.rootData.rootCocharacter (M.f4SimpleRoot i)) (x i) (y i) (hword i)
      (xH i) (yH i) (2 ^ a i) (hxH i) (hyH i)
  exact ⟨a, μ, hμ⟩

end RootSystemModel
end Theory.AlgebraicGroup
