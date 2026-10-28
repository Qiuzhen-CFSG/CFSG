module

public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.ModelOrbits
public import Theory.Representation.BinaryNaturalDual.GeneratedCore
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers

/-!
# The source setup and constructed coordinates for H.9

The input consists only of the actual automorphism-group identification,
the natural action of the layer, two complementary marked summands, and
an outer element carrying the first summand onto the second. In particular
it contains no orbit, stabilizer, elementary-actor or adapted-pair conclusion.
The whole-module comparison is constructed by the marked comparison theorem.

`SourceSetup.model` preserves the original layer marking and both summands.
Its evaluation form is the unique invariant nondegenerate quadratic form.
The source point stabilizer and two-residual below are literal subgroups of
M; the moving module is the span of their actual displacements.

Source: Aschbacher–Smith H.9, printed pp.389–392; the nonsingular Sylow
marking uses the separately proved correction of 6 October 2026.
-/

@[expose] public section
open BinaryNaturalDual BinaryNaturalDual.ModelOrbits BinaryLinear.OuterCyclic
open Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterH.NaturalDual

/-- The standing source hypotheses of H.9, before choosing a Sylow subgroup. -/
structure SourceSetup (n : ℕ) (M V : Type*) [Group M] [AddCommGroup V]
    [Module (ZMod 2) V] where
  degree : n = 4 ∨ n = 5
  projective : M ≃* MulAut PSL(n, ZMod 2)
  layer : componentLayer M ≃* LinearGroup n
  representation : Representation (ZMod 2) M V
  natural : Submodule (ZMod 2) V
  dual : Submodule (ZMod 2) V
  complement : IsCompl natural dual
  naturalCoordinates : natural ≃ₗ[ZMod 2] BinaryLinear.OuterCyclic.Space n
  natural_action : ∀ (l : componentLayer M) (x : BinaryLinear.OuterCyclic.Space n),
    representation l (naturalCoordinates.symm x : V) =
      (naturalCoordinates.symm (layer l x) : V)
  outer : ∃ t : M, t ∉ componentLayer M ∧ natural.map (representation t) = dual

namespace SourceSetup
variable {n : ℕ} {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]
  (S : SourceSetup n M V)

/-- A marked equivariant comparison, which the source hypotheses construct. -/
structure Model where
  group : M ≃* MulAut (LinearGroup n)
  dualCoordinates : S.dual ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)
  coordinates : V ≃ₗ[ZMod 2] CoordinateSpace n
  on_layer : ∀ l : componentLayer M, group l = MulAut.conj (S.layer l)
  inner_iff : ∀ m : M, group m ∈ MulAut.innerSubgroup (LinearGroup n) ↔ m ∈ componentLayer M
  natural_marking : ∀ u : S.natural, coordinates u = (S.naturalCoordinates u, 0)
  dual_marking : ∀ w : S.dual, coordinates w = (0, dualCoordinates w)
  equivariant : ∀ m v, coordinates (S.representation m v) =
    (AutomorphismModel.coordinateAction S.degree).representation (group m) (coordinates v)

/-- Neither the whole-module equivalence nor an action extension is assumed. -/
theorem nonempty_model : Nonempty S.Model := by
  obtain ⟨e,e₂,eV,he,hL,h₁,h₂,ha⟩ := exists_source_model S.degree S.projective S.layer
    S.representation S.complement S.naturalCoordinates S.natural_action S.outer
  exact ⟨⟨e,e₂,eV,he,hL,h₁,h₂,ha⟩⟩

/-- A fixed choice of the constructed source comparison. -/
noncomputable def model : S.Model := Classical.choice S.nonempty_model

include S in
/-- Finiteness follows from the actual group identification. -/
theorem finite_group : Finite M := by
  let : Finite (LinearGroup n) := Finite.of_injective
    (fun g : LinearGroup n => (g : BinaryLinear.OuterCyclic.Space n →
      BinaryLinear.OuterCyclic.Space n)) DFunLike.coe_injective
  exact Finite.of_equiv (MulAut (LinearGroup n)) S.model.group.toEquiv.symm

/-- The source form, obtained by pulling back the coordinate evaluation form. -/
noncomputable def quadratic : QuadraticForm (ZMod 2) V :=
  MarkedGeometry.form S.model.coordinates

@[simp] theorem quadratic_apply (v : V) :
    S.quadratic v = BinaryNaturalDual.quadratic (S.model.coordinates v) :=
  MarkedGeometry.form_apply S.model.coordinates v

/-- The source form is nondegenerate, invariant, and totally singular on V₁. -/
theorem quadratic_invariant :
    MarkedGeometry.IsInvariantForm S.representation S.natural S.quadratic :=
  MarkedGeometry.form_invariant (AutomorphismModel.coordinateAction S.degree)
    S.representation S.model.group S.model.coordinates S.model.equivariant
    (MarkedGeometry.mem_natural_iff_of_marking S.model.coordinates S.naturalCoordinates
      S.model.natural_marking) S.degree

/-- Uniqueness holds among all source-invariant nondegenerate forms. -/
theorem quadratic_unique (q : QuadraticForm (ZMod 2) V)
    (hq : MarkedGeometry.IsInvariantForm S.representation S.natural q) : q = S.quadratic :=
  MarkedGeometry.form_unique (AutomorphismModel.coordinateAction S.degree)
    S.representation S.model.group S.model.coordinates S.model.equivariant
    (MarkedGeometry.mem_natural_iff_of_marking S.model.coordinates S.naturalCoordinates
      S.model.natural_marking) q hq

/-- The literal vector centralizer C_M(v). -/
def stabilizer (v : V) : Subgroup M :=
  VectorStabilizers.representationStabilizer S.representation v

/-- The layer centralizer C_L(v), embedded in M. -/
def innerStabilizer (v : V) : Subgroup M := componentLayer M ⊓ S.stabilizer v

/-- The embedded TWO-RESIDUAL O²(C_L(v)); this is not the two-core. -/
noncomputable def residual (v : V) : Subgroup M :=
  (pResidual 2 (S.innerStabilizer v)).map (S.innerStabilizer v).subtype

/-- The actual moving module [V,L_v]. -/
noncomputable def moving (v : V) : Submodule (ZMod 2) V :=
  Representation.Coinvariants.ker (S.representation.comp (S.residual v).subtype)

/-- The actual centralizer subspace of an actor in the original module. -/
noncomputable def fixed (A : Subgroup M) : Submodule (ZMod 2) V :=
  Representation.BinaryOffender.fixedSpace S.representation A

end SourceSetup
end CFSG.Quasithin.ChapterH.NaturalDual
