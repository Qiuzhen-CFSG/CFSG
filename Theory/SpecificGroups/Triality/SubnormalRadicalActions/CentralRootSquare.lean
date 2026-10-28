module

public import Theory.GroupAction.CommutatorLinearLayer
public import Theory.GroupTheory.PResidual.Defs
public import Mathlib.GroupTheory.IsSubnormal
public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.CentralRootSquare.ElementaryImage
public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.CentralRootSquare.ParabolicAction
public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.CentralRootSquare.SquareWitness

/-!
# Central triality square rigidity

The genuine first two cubic root coordinates provide a uniform route,
including q = 2. The commutator image is closed under cubic-field scalars
when this coordinate map is additive and parabolic conjugation is linear.
The commutator is normal in the radical. An elementary-normal-subgroup
calculation then makes its image zero, so the actor fixes the first layer.
The faithful full-parabolic action places that actor in the radical.

The four concrete premises of the retained conditional assembly theorem are
discharged by `ElementaryImage` and `ParabolicAction`. Consequently every
subgroup X of the full central parabolic with [R,X] of exponent at most two
lies in R. The requested subnormal, two-perfect specialization follows without
additional root-action assumptions. In fact neither subnormality nor
two-perfectness is needed for this root rigidity statement.

The genuine pinned u(1)v(1) has order three and sends the first-layer vector
(1,0) to (1,1). The square condition would force this actor to fix the layer,
giving an explicit exclusion of the PSL₂(2) C₃ case as well. Multiplying the
actor by an arbitrary radical element does not change this obstruction.

The imported square witness separately excludes Levi-containing actors for
q > 2. No full-Levi torus coordinate or arbitrary radical factor is removed.

Sources: GLS3 §§2.4 and 2.6 (`refs/KGroup/GLS3/chapter2.tex`), and the
central parabolic of Aschbacher–Smith F.1.12(I)(4), printed pp.263–264
(`refs/quasithin.pdf`).
-/

public section
noncomputable section
open Subgroup
namespace Triality.Standard.Parabolics.CentralRootSquare

/-- Assembly from the two independent first-layer root calculations. -/
theorem le_radical_of_firstLayer_calculations
    (P : Parameters) (hp : P.prime = 2)
    (hadd : ∀ r s, firstLayer P hp (r * s) = firstLayer P hp r + firstLayer P hp s)
    (hvanish : ∀ N : Subgroup (radical P .central), N.Normal →
      (∀ n ∈ N, (n : radical P .central) ^ 2 = 1) →
      (∀ c : ExtensionField P, ∀ r ∈ N, ∃ s ∈ N,
        firstLayer P hp s = c • firstLayer P hp r) →
      ∀ r ∈ N, firstLayer P hp r = 0)
    (hlinear : ∀ g : parabolic P .central,
      ∃ A : (ExtensionField P × ExtensionField P) →ₗ[ExtensionField P]
          (ExtensionField P × ExtensionField P),
        ∀ r, firstLayer P hp (conjugation P g r) = A (firstLayer P hp r))
    (hkernel : ∀ g : parabolic P .central,
      (∀ r, firstLayer P hp (conjugation P g r) = firstLayer P hp r) →
      g.val ∈ radical P .central)
    (X : Subgroup (parabolic P .central))
    (hsq : ∀ z ∈ ⁅(radical P .central).subgroupOf (parabolic P .central), X⁆,
      (z : parabolic P .central) ^ 2 = 1) :
    X ≤ (radical P .central).subgroupOf (parabolic P .central) := by
  let H := parabolic P .central
  let R := radical P .central
  let Y := X.map H.subtype
  have hY : Y ≤ H := by
    rintro y ⟨x, hx, rfl⟩
    exact x.property
  have he : (⁅R.subgroupOf H, X⁆).map H.subtype = ⁅R, Y⁆ := by
    rw [map_commutator, map_subgroupOf_eq_of_le (radical_le_parabolic P .central)]
  have hsqY : ∀ z ∈ ⁅R, Y⁆, (z : Carrier P) ^ 2 = 1 := by
    intro z hz
    rw [← he] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact congrArg Subtype.val (hsq w hw)
  let ρ : Y → MulAut R := fun x => conjugation P ⟨x.val, hY x.property⟩
  let A : Y → (ExtensionField P × ExtensionField P) →ₗ[ExtensionField P]
      (ExtensionField P × ExtensionField P) :=
    fun x => Classical.choose (hlinear ⟨x.val, hY x.property⟩)
  have hA (x : Y) (r : R) : firstLayer P hp (ρ x r) = A x (firstLayer P hp r) :=
    Classical.choose_spec (hlinear ⟨x.val, hY x.property⟩) r
  have hfix := action_layer_trivial_of_commutator_squares R Y (firstLayer P hp)
    hadd (firstLayer_surjective P hp) ρ
    (fun x r => conjugation_val P ⟨x.val, hY x.property⟩ r) A hA hvanish hsqY
  intro x hx
  exact hkernel x (fun r => hfix ⟨x.val, mem_map_of_mem H.subtype hx⟩ r)

/-- Uniform central root rigidity: an exponent-two radical commutator forces
the actor into the genuine radical of the full parabolic. This includes q = 2. -/
theorem le_radical_of_commutator_squares
    (P : Parameters) (hp : P.prime = 2)
    (X : Subgroup (parabolic P .central))
    (hsq : ∀ z ∈ ⁅(radical P .central).subgroupOf (parabolic P .central), X⁆,
      (z : parabolic P .central) ^ 2 = 1) :
    X ≤ (radical P .central).subgroupOf (parabolic P .central) :=
  le_radical_of_firstLayer_calculations P hp (firstLayer_mul P hp)
    (firstLayer_eq_zero_of_normal_elementary P hp)
    (firstLayer_linear P hp (firstLayer_mul P hp))
    (firstLayer_kernel P hp (firstLayer_mul P hp)) X hsq

/-- The subnormal two-perfect interface for the central radical-action
application, with every concrete root-calculation premise discharged. -/
theorem le_radical_of_subnormal_of_isPPerfect
    (P : Parameters) (hp : P.prime = 2)
    (X : Subgroup (parabolic P .central))
    (_hsub : X.IsSubnormal) (_hperfect : IsPPerfect 2 X)
    (hsq : ∀ z ∈ ⁅(radical P .central).subgroupOf (parabolic P .central), X⁆,
      (z : parabolic P .central) ^ 2 = 1) :
    X ≤ (radical P .central).subgroupOf (parabolic P .central) :=
  le_radical_of_commutator_squares P hp X hsq

/-- Explicit exclusion of the genuine central C₃ actor, including in PSL₂(2):
the checked root formula moves (1,0) to (1,1), whereas every radical actor
fixes this layer. No perfectness assertion for PSL₂(2) is used. -/
theorem orderThreeActor_not_mem_of_commutator_squares
    (P : Parameters) (hp : P.prime = 2)
    (X : Subgroup (parabolic P .central))
    (hsq : ∀ z ∈ ⁅(radical P .central).subgroupOf (parabolic P .central), X⁆,
      (z : parabolic P .central) ^ 2 = 1) :
    orderThreeActor P hp ∉ X := by
  intro hx
  have hR := le_radical_of_commutator_squares P hp X hsq hx
  obtain ⟨r, _, _, hmove⟩ := orderThreeActor_moves P hp
  exact hmove (firstLayer_conjugation_radical P hp (firstLayer_mul P hp)
    ⟨(orderThreeActor P hp).val, hR⟩ r)

/-- The same explicit C₃ obstruction retains an arbitrary radical factor. -/
theorem radical_mul_orderThreeActor_not_mem_of_commutator_squares
    (P : Parameters) (hp : P.prime = 2)
    (X : Subgroup (parabolic P .central))
    (hsq : ∀ z ∈ ⁅(radical P .central).subgroupOf (parabolic P .central), X⁆,
      (z : parabolic P .central) ^ 2 = 1)
    (x : radical P .central) :
    (⟨x.val, radical_le_parabolic P .central x.property⟩ : parabolic P .central) *
      orderThreeActor P hp ∉ X := by
  intro hx
  have hR := le_radical_of_commutator_squares P hp X hsq hx
  change x.val * (orderThreeActor P hp).val ∈ radical P .central at hR
  have hactor : (orderThreeActor P hp).val ∈ radical P .central := by
    simpa only [inv_mul_cancel_left] using
      (radical P .central).mul_mem ((radical P .central).inv_mem x.property) hR
  obtain ⟨r, _, _, hmove⟩ := orderThreeActor_moves P hp
  exact hmove (firstLayer_conjugation_radical P hp (firstLayer_mul P hp)
    ⟨(orderThreeActor P hp).val, hactor⟩ r)

end Triality.Standard.Parabolics.CentralRootSquare

end
