module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Marked.PairingData
public import Theory.Representation.BinaryOffender.ActionImage
public import Mathlib.LinearAlgebra.Projection

/-!
# Paired coordinates on the marked line section

Given `PairedGeometry`, descend the literal section action to `G/Q` and restrict
its actual centralizer factor to the first fixed-space image `W`. Projection to
this factor in the marked product gives a representation of `G/Q` on `W`.

The complementary images and marked conjugation identify `U/E` with `W × W`:
the inverse coordinate map sends `(w₁,w₂)` to `w₁ + y⁻¹ w₂`. Commutation on the
quotient makes the centralizer action diagonal in these coordinates. Composing
with `U → U/E` constructs `PairedSection` with kernel exactly `E`.

An element of `C` fixing `W` consequently fixes the entire section. Equality of
the actual action kernels identifies the two centralizer action images and
supplies a faithful action of that image on `W`. The representation of the whole
`G/Q` need not be faithful: its marked first factor acts trivially.

All constructions also apply when `W = 0`. This is the conditional coordinate
step; constructing `PairedGeometry` from the source hypotheses remains with the
marked geometry and source assembly owners.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of 15.3.67,
printed pp.1153–1154, PDF pp.1170–1171.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.PairedGeometry
variable {G D : Type*} [Group G] [Group D]
  {U E A C Q : Subgroup G} [U.Normal] [IsElementaryAbelian 2 U] [E.Normal] [Q.Normal]
  {f : G →* D} {hf : Function.Surjective f}
  {hker : f.ker = centralizer (U : Set G)} {τ y : G}
  (d : PairedGeometry U E A C Q f hf hker τ y)

local notation "N" => Representation.NormalElementaryQuotient.subspace U (E.subgroupOf U)
local notation "X" => Additive U ⧸ N
local notation "W" => MarkedSection.fixedImage U E τ
local notation "W₂" => MarkedSection.fixedImage U E (y⁻¹ * τ * y)
local notation "ρ" => MarkedSection.action U E f hf hker

/-- The actual action of `C` on the first fixed-space image in `U/E`. -/
noncomputable def centralizerAction : Representation (ZMod 2) C W :=
  Representation.subrepresentation ((ρ).comp C.subtype) W (fun c => d.first_invariant c c.property)

/-- Restriction agrees with the literal section action. -/
@[simp] theorem centralizerAction_apply (c : C) (w : W) :
    (d.centralizerAction c w : X) = ρ c w := rfl

/-- The section action descends because the actual core acts trivially. -/
noncomputable def quotientAction : Representation (ZMod 2) (G ⧸ Q) X :=
  QuotientGroup.lift Q ρ d.core_kills

/-- Descent preserves the action of each original group element. -/
@[simp] theorem quotientAction_mk (g : G) :
    d.quotientAction (QuotientGroup.mk' Q g) = ρ g := rfl

private theorem factor_invariant (c : C.map (QuotientGroup.mk' Q)) :
    W ≤ (W).comap (d.quotientAction c) := by
  obtain ⟨g, hg, hgc⟩ := c.property
  intro w hw
  change d.quotientAction c w ∈ W
  rw [← hgc, quotientAction_mk]
  exact d.first_invariant g hg w hw

/-- The actual centralizer image in `G/Q` acts on the first summand. -/
noncomputable def factorAction :
    Representation (ZMod 2) (C.map (QuotientGroup.mk' Q)) W :=
  Representation.subrepresentation
    (d.quotientAction.comp (C.map (QuotientGroup.mk' Q)).subtype) W
    (by exact factor_invariant d)

/-- Extend the centralizer-factor action through the marked product projection. -/
noncomputable def representation : Representation (ZMod 2) (G ⧸ Q) W :=
  d.factorAction.comp ((MonoidHom.snd _ _).comp d.factors.equiv.toMonoidHom)

/-- The extension retains the action of every actual centralizer element. -/
@[simp] theorem representation_mk (c : C) :
    d.representation (QuotientGroup.mk' Q c) = d.centralizerAction c := by
  ext w
  change d.quotientAction (d.factors.equiv (QuotientGroup.mk' Q c)).2 w = ρ c w
  rw [d.factors.centralizer_factor]
  rfl

/-- The factor action is the restriction of the descended section action. -/
@[simp] theorem factorAction_apply (c : C.map (QuotientGroup.mk' Q)) (w : W) :
    (d.factorAction c w : X) = d.quotientAction c w := rfl

/-- In marked product coordinates only the centralizer factor acts. -/
@[simp] theorem representation_factors (s : Equiv.Perm (Fin 3))
    (c : C.map (QuotientGroup.mk' Q)) :
    d.representation (d.factors.equiv.symm (s, c)) = d.factorAction c := by
  change d.factorAction (d.factors.equiv (d.factors.equiv.symm (s, c))).2 = _
  rw [d.factors.equiv.apply_symm_apply]

/-- The second summand is identified with the first by the action of `y⁻¹`. -/
noncomputable def conjugateEquiv : W ≃ₗ[ZMod 2] W₂ :=
  let e : X ≃ₗ[ZMod 2] X := LinearEquiv.ofLinearMap (ρ y⁻¹) (ρ y)
    (by change ρ y⁻¹ * ρ y = 1; rw [← map_mul]; simp)
    (by change ρ y * ρ y⁻¹ = 1; rw [← map_mul]; simp)
  e.ofSubmodules W W₂ d.conjugate.symm

/-- The summand identification is the specified marked conjugation. -/
@[simp] theorem conjugateEquiv_apply (w : W) :
    (d.conjugateEquiv w : X) = ρ y⁻¹ w := rfl

/-- Coordinates in the two complementary images, with both copies identified with `W`. -/
noncomputable def coordinates : X ≃ₗ[ZMod 2] W × W :=
  (Submodule.prodEquivOfIsCompl W W₂ d.complementary).symm.trans
    ((LinearEquiv.refl (ZMod 2) W).prodCongr d.conjugateEquiv.symm)

/-- Reconstruct a section vector by adding its two marked summands. -/
@[simp] theorem coordinates_symm_apply (w : W × W) :
    d.coordinates.symm w = (w.1 : X) + ρ y⁻¹ w.2 := rfl

/-- The coordinates of the displayed marked decomposition. -/
theorem coordinates_sum (w₁ w₂ : W) :
    d.coordinates ((w₁ : X) + ρ y⁻¹ w₂) = (w₁, w₂) :=
  d.coordinates.apply_symm_apply (w₁, w₂)

/-- A first-summand vector has zero second coordinate. -/
@[simp] theorem coordinates_first (w : W) : d.coordinates (w : X) = (w, 0) := by
  simpa using d.coordinates_sum w 0

/-- A conjugated first-summand vector has zero first coordinate. -/
@[simp] theorem coordinates_second (w : W) : d.coordinates (ρ y⁻¹ w) = (0, w) := by
  simpa using d.coordinates_sum 0 w

/-- Every section vector is the sum of its marked coordinate vectors. -/
theorem coordinates_reconstruct (v : X) :
    ((d.coordinates v).1 : X) + ρ y⁻¹ (d.coordinates v).2 = v :=
  d.coordinates.symm_apply_apply v

/-- Quotient commutation makes the actual centralizer action diagonal. -/
theorem coordinates_equivariant (c : C) (v : X) :
    d.coordinates (ρ c v) =
      (d.centralizerAction c (d.coordinates v).1,
        d.centralizerAction c (d.coordinates v).2) := by
  apply d.coordinates.symm.injective
  rw [LinearEquiv.symm_apply_apply, coordinates_symm_apply]
  conv_lhs => rw [← d.coordinates_reconstruct v]
  rw [map_add]
  congr 1
  exact LinearMap.congr_fun (d.commutes c c.property).eq _

/-- The paired projection first passes to the literal quotient by `E`. -/
noncomputable def projection : Additive U →ₗ[ZMod 2] W × W :=
  d.coordinates.toLinearMap.comp (N).mkQ

/-- The paired projection takes coordinates of the quotient class. -/
@[simp] theorem projection_apply (v : Additive U) :
    d.projection v = d.coordinates ((N).mkQ v) := rfl

/-- The coordinates reconstruct exactly the quotient class of the original vector. -/
theorem projection_reconstruct (v : Additive U) :
    ((d.projection v).1 : X) + ρ y⁻¹ (d.projection v).2 = (N).mkQ v :=
  d.coordinates_reconstruct ((N).mkQ v)

/-- An actual vector fixed by `τ` projects entirely into the first copy. -/
theorem projection_fixed (v : Additive U)
    (hv : (v.toMul : G) ∈ centralizer ({τ} : Set G)) :
    d.projection v =
      (⟨(N).mkQ v, (MarkedSection.mem_fixedImage_iff U E τ _).mpr ⟨v, hv, rfl⟩⟩, 0) :=
  d.coordinates_first ⟨(N).mkQ v,
    (MarkedSection.mem_fixedImage_iff U E τ _).mpr ⟨v, hv, rfl⟩⟩

/-- Conjugating an actual `τ`-fixed vector projects into the second copy. -/
theorem projection_conjugate_fixed (v : Additive U)
    (hv : (v.toMul : G) ∈ centralizer ({τ} : Set G)) :
    d.projection (Representation.NormalElementaryQuotient.representation U f hf hker (f y⁻¹) v) =
      (0, ⟨(N).mkQ v, (MarkedSection.mem_fixedImage_iff U E τ _).mpr ⟨v, hv, rfl⟩⟩) :=
  d.coordinates_second ⟨(N).mkQ v,
    (MarkedSection.mem_fixedImage_iff U E τ _).mpr ⟨v, hv, rfl⟩⟩

/-- Every pair occurs, since both the quotient map and the coordinates are onto. -/
theorem projection_surjective : Function.Surjective d.projection :=
  d.coordinates.surjective.comp (N).mkQ_surjective

/-- The kernel is precisely the binary subspace of the actual denominator `E`. -/
theorem projection_ker : d.projection.ker = N := by
  ext v
  change d.coordinates ((N).mkQ v) = 0 ↔ v ∈ N
  rw [← d.coordinates.map_zero, d.coordinates.injective.eq_iff]
  exact Submodule.Quotient.mk_eq_zero N

/-- The projection intertwines actual conjugation by `C` with the two equal actions. -/
theorem projection_equivariant (c : C) (v : Additive U) :
    d.projection (Representation.NormalElementaryQuotient.representation U f hf hker (f c) v) =
      (d.representation (QuotientGroup.mk' Q c) (d.projection v).1,
        d.representation (QuotientGroup.mk' Q c) (d.projection v).2) := by
  rw [representation_mk, projection_apply, ← MarkedSection.action_mk]
  exact d.coordinates_equivariant c ((N).mkQ v)

/-- The constructed marked paired section, with all projection obligations discharged. -/
noncomputable def pairedSection : PairedSection U E C Q f hf hker d.representation where
  line_le := d.line_le
  projection := d.projection
  surjective := d.projection_surjective
  kernel_eq := d.projection_ker
  equivariant c hc v := d.projection_equivariant ⟨c, hc⟩ v

/-- Fixing the first summand forces fixation of its conjugate and hence the section. -/
theorem centralizerAction_eq_one_iff (c : C) :
    d.centralizerAction c = 1 ↔ ρ c = 1 := by
  constructor
  · intro hc
    apply LinearMap.ext
    intro v
    apply d.coordinates.injective
    rw [coordinates_equivariant, hc]
    rfl
  · intro hc
    ext w
    change ρ c w = w
    rw [hc]
    rfl

/-- The first-summand kernel is exactly the restriction of the entire section kernel. -/
theorem centralizerAction_ker : d.centralizerAction.ker = (ρ).ker.subgroupOf C := by
  ext c
  exact d.centralizerAction_eq_one_iff c

/-- The first-summand kernel retains the original commutator criterion modulo `E`. -/
theorem centralizerAction_eq_one_iff_commutator (c : C) :
    d.centralizerAction c = 1 ↔ ∀ u ∈ U, ⁅u, (c : G)⁆ ∈ E := by
  rw [centralizerAction_eq_one_iff, MarkedSection.action_eq_one_iff]

/-- Identify the kernel with the relative quotient centralizer inside `C`. -/
theorem centralizerAction_ker_eq_centralizerModulo :
    d.centralizerAction.ker = (centralizerModulo ⊤ U E).subgroupOf C := by
  rw [centralizerAction_ker, MarkedSection.action_ker]

open Representation.BinaryOffender

private theorem imageKernel_eq :
    ((actionHom ρ).comp C.subtype).ker = (actionHom d.centralizerAction).ker := by
  ext c
  change actionHom ρ c = 1 ↔ actionHom d.centralizerAction c = 1
  rw [actionHom_eq_one_iff, actionHom_eq_one_iff]
  change (∀ v, ρ c v = (1 : Module.End (ZMod 2) X) v) ↔
    (∀ w, d.centralizerAction c w = (1 : Module.End (ZMod 2) W) w)
  rw [← LinearMap.ext_iff, ← LinearMap.ext_iff, centralizerAction_eq_one_iff]

/-- The actual `C`-action image on the entire section is isomorphic to its image on `W`. -/
noncomputable def actionImageEquiv :
    actionSubgroup ρ C ≃* actionImage d.centralizerAction :=
  (actionQuotientEquiv ρ C).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (by exact imageKernel_eq d)).trans
      (QuotientGroup.quotientKerEquivOfSurjective (actionHom d.centralizerAction)
        d.centralizerAction.asGroupHom.rangeRestrict_surjective))

/-- The image isomorphism sends the action of `c` to the action of the same `c`. -/
@[simp] theorem actionImageEquiv_apply (c : C) :
    d.actionImageEquiv ⟨actionHom ρ c, mem_map_of_mem _ c.property⟩ =
      actionHom d.centralizerAction c := by
  have he : actionQuotientEquiv ρ C (QuotientGroup.mk c) =
      ⟨actionHom ρ c, mem_map_of_mem _ c.property⟩ := rfl
  rw [← he]
  simp only [actionImageEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- The actual centralizer action image on the section acts faithfully on `W`. -/
noncomputable def faithfulRepresentation :
    Representation (ZMod 2) (actionSubgroup ρ C) W :=
  (imageRepresentation d.centralizerAction).comp d.actionImageEquiv.toMonoidHom

/-- Faithfulness holds after passage to the actual action image. -/
theorem faithfulRepresentation_injective : Function.Injective d.faithfulRepresentation :=
  (imageRepresentation_injective d.centralizerAction).comp d.actionImageEquiv.injective

/-- The faithful image action still agrees with the original centralizer action. -/
@[simp] theorem faithfulRepresentation_apply (c : C) :
    d.faithfulRepresentation ⟨actionHom ρ c, mem_map_of_mem _ c.property⟩ =
      d.centralizerAction c := by
  change imageRepresentation d.centralizerAction (d.actionImageEquiv _) = _
  rw [actionImageEquiv_apply, imageRepresentation_actionHom]

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.PairedGeometry
