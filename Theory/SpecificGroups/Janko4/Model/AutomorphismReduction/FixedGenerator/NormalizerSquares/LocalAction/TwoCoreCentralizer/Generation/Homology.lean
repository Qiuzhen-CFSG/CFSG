module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Max2Bridge
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RepresentationTheory.Basic

/-!
# The canonical linear quotient for the literal involution centralizer

On the natural binary column module V, the displacement a - 1 has square
zero. Every element of C = `involutionCentralizer` commutes with this map,
so C acts on ker(a - 1) / im(a - 1). This construction uses the entire
literal centralizer, independently of generation by the two max2 words.
The distinguished involution acts trivially even on ker(a - 1).

The kernel-image order formula reduces an upper bound for |C| to two
independent bounds. A separate restriction to `localSubgroup` gives the
corresponding lower-bound formula. The proposed numerical bounds are explicit
premises; neither the dimension of the quotient nor either bound is asserted.
In particular, this is a quotient of the natural linear module, not the
Frattini quotient of the local two-core.

Source motivation: GLS3, Table 5.3i, printed p.270, gives the expected
2A centralizer structure 2^(1+12).(3M22.2). The matrix word provenance is
recorded in `TwoCoreCentralizer/source/README.md`. All actions here use
column vectors with left multiplication; row-action certificates require
an explicit duality or new column coordinates before use.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
namespace Generation

/-- The natural column module of the literal 112-dimensional representation. -/
abbrev NaturalModule := Fin 112 → ZMod 2

/-- Matrix multiplication by actors in the whole literal centralizer. -/
def naturalAction : Representation (ZMod 2) involutionCentralizer NaturalModule :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp
    ((Units.coeHom BinaryMatrix).comp involutionCentralizer.subtype)

set_option maxRecDepth 2048 in
theorem naturalAction_apply (c : involutionCentralizer) (v : NaturalModule) :
    naturalAction c v = Matrix.mulVec ((c : BinaryMatrixˣ) : BinaryMatrix) v := rfl

/-- The nilpotent displacement of the distinguished involution. -/
def displacement : Module.End (ZMod 2) NaturalModule :=
  naturalAction centralInvolution - 1

set_option maxRecDepth 2048 in
theorem displacement_apply (v : NaturalModule) :
    displacement v = Matrix.mulVec matrixA v - v := rfl

theorem displacement_sq : displacement * displacement = 0 := by
  have ha : naturalAction centralInvolution * naturalAction centralInvolution = 1 := by
    rw [← map_mul, ← pow_two, centralInvolution_pow_two, map_one]
  have hn : -(1 : Module.End (ZMod 2) NaturalModule) = 1 := by
    ext v i
    exact CharTwo.neg_eq _
  have hs (f : Module.End (ZMod 2) NaturalModule) : f + f = 0 := by
    ext v i
    exact CharTwo.add_self_eq_zero _
  rw [displacement, sub_eq_add_neg, hn, add_mul, mul_add, mul_add,
    mul_one, one_mul, one_mul, ha]
  rw [add_assoc, ← add_assoc (naturalAction centralInvolution), hs,
    zero_add, hs]

theorem displacement_commute (c : involutionCentralizer) :
    displacement * naturalAction c = naturalAction c * displacement := by
  have hc : c * centralInvolution = centralInvolution * c :=
    Subgroup.mem_center_iff.mp centralInvolution_mem_center c
  dsimp only [displacement]
  rw [sub_mul, mul_sub, one_mul, mul_one, ← map_mul, ← map_mul, hc]

/-- Vectors fixed by the distinguished involution. -/
def fixedVectors : Submodule (ZMod 2) NaturalModule := LinearMap.ker displacement

/-- The image of a - 1, a subspace of the fixed vectors. -/
def displacementVectors : Submodule (ZMod 2) NaturalModule := LinearMap.range displacement

theorem displacementVectors_le_fixedVectors : displacementVectors ≤ fixedVectors := by
  rintro _ ⟨v, rfl⟩
  change (displacement * displacement) v = 0
  rw [displacement_sq, LinearMap.zero_apply]

theorem fixedVectors_invariant (c : involutionCentralizer) :
    fixedVectors ≤ fixedVectors.comap (naturalAction c) := by
  intro v hv
  change displacement (naturalAction c v) = 0
  have he := LinearMap.congr_fun (displacement_commute c) v
  change displacement (naturalAction c v) = naturalAction c (displacement v) at he
  rw [he, show displacement v = 0 from hv, map_zero]

theorem displacementVectors_invariant (c : involutionCentralizer) :
    displacementVectors ≤ displacementVectors.comap (naturalAction c) := by
  rintro _ ⟨v, rfl⟩
  refine ⟨naturalAction c v, ?_⟩
  exact LinearMap.congr_fun (displacement_commute c) v

/-- Restriction of the natural representation to the fixed vectors. -/
def fixedAction : Representation (ZMod 2) involutionCentralizer fixedVectors :=
  naturalAction.subrepresentation fixedVectors fixedVectors_invariant

theorem fixedAction_centralInvolution : fixedAction centralInvolution = 1 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact sub_eq_zero.mp (show naturalAction centralInvolution (v : NaturalModule) - v = 0
    from v.property)

/-- The displacement subspace, regarded as a subspace of the fixed vectors. -/
def displacementInFixed : Submodule (ZMod 2) fixedVectors :=
  displacementVectors.comap fixedVectors.subtype

theorem displacementInFixed_invariant (c : involutionCentralizer) :
    displacementInFixed ≤ displacementInFixed.comap (fixedAction c) := by
  intro v hv
  exact displacementVectors_invariant c hv

/-- The canonical quotient ker(a - 1) / im(a - 1). -/
abbrev NaturalHomology := fixedVectors ⧸ displacementInFixed

/-- The quotient representation on the canonical linear quotient. -/
def homologyRepresentation :
    Representation (ZMod 2) involutionCentralizer NaturalHomology :=
  fixedAction.quotient displacementInFixed displacementInFixed_invariant

/-- The induced action of the entire literal centralizer on the canonical quotient. -/
def homologyAction : involutionCentralizer →* (Module.End (ZMod 2) NaturalHomology)ˣ :=
  homologyRepresentation.asGroupHom

/-- Restriction to the subgroup whose generation remains to be proved. -/
def localHomologyAction : localSubgroup →* (Module.End (ZMod 2) NaturalHomology)ˣ :=
  homologyAction.comp localSubgroup.subtype

theorem homologyAction_mk (c : involutionCentralizer) (v : fixedVectors) :
    (homologyAction c : Module.End (ZMod 2) NaturalHomology)
      (Submodule.Quotient.mk v) = Submodule.Quotient.mk (fixedAction c v) := rfl

theorem homologyAction_centralInvolution : homologyAction centralInvolution = 1 := by
  apply Units.ext
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    rw [homologyAction_mk, fixedAction_centralInvolution]
    rfl

theorem centralInvolution_mem_homologyAction_ker :
    centralInvolution ∈ homologyAction.ker := homologyAction_centralInvolution

attribute [local irreducible] naturalAction displacement fixedVectors displacementVectors

theorem mem_homologyAction_ker_iff (c : involutionCentralizer) :
    c ∈ homologyAction.ker ↔
      ∀ v : fixedVectors, naturalAction c (v : NaturalModule) - v ∈ displacementVectors := by
  constructor
  · intro hc v
    have he := congrArg (fun u : (Module.End (ZMod 2) NaturalHomology)ˣ =>
      (u : Module.End (ZMod 2) NaturalHomology) (Submodule.Quotient.mk v)) hc
    change (Submodule.Quotient.mk (fixedAction c v) : NaturalHomology) =
      Submodule.Quotient.mk v at he
    exact (Submodule.Quotient.eq displacementInFixed).mp he
  · intro hc
    apply Units.ext
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | H v =>
      change (Submodule.Quotient.mk (fixedAction c v) : NaturalHomology) =
        Submodule.Quotient.mk v
      exact (Submodule.Quotient.eq displacementInFixed).mpr (hc v)

theorem card_centralizer_eq_kernel_mul_image :
    Nat.card involutionCentralizer =
      Nat.card homologyAction.ker * Nat.card homologyAction.range := by
  rw [← homologyAction.ker.card_mul_index, Subgroup.index_ker]

theorem card_localSubgroup_eq_kernel_mul_image :
    Nat.card localSubgroup =
      Nat.card localHomologyAction.ker * Nat.card localHomologyAction.range := by
  rw [← localHomologyAction.ker.card_mul_index, Subgroup.index_ker]

theorem localSubgroup_card_ge_of_homology_bounds
    (hk : 8192 ≤ Nat.card localHomologyAction.ker)
    (hi : 2661120 ≤ Nat.card localHomologyAction.range) :
    21799895040 ≤ Nat.card localSubgroup := by
  rw [card_localSubgroup_eq_kernel_mul_image]
  exact Nat.mul_le_mul hk hi

theorem centralizer_card_le_of_homology_bounds
    (hk : Nat.card homologyAction.ker ≤ 8192)
    (hi : Nat.card homologyAction.range ≤ 2661120) :
    Nat.card involutionCentralizer ≤ 21799895040 := by
  rw [card_centralizer_eq_kernel_mul_image]
  exact Nat.mul_le_mul hk hi

end Generation
end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
