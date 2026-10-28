module

public import Theory.Representation.PSL3Two.IrreducibleCatalogue.FanoDecomposition.Basic

/-!
# The concrete Fano flag map

A flag (x,λ) maps to (1, eₓ + Ω, e_λ + Ω, xλ). The last component is the
literal rank-one endomorphism v ↦ λ(v)x, with trace zero by incidence.
Each of the four components commutes with every actual SL₃(2) element.
No irreducibility or decomposition theorem enters this construction.

Source: the four summands of Aschbacher–Smith H.6.2(1), combined manuscript
of 1 March 2004, printed p.387.
-/

@[expose] public section
open Matrix Representation
namespace BinaryLinearThree.FanoDecomposition

/-- The complement of one coordinate lies in the odd-degree binary core. -/
def coreSpike (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (hΩ : (Fintype.card Ω : ZMod 2) = 1) (p : Ω) : BinaryPermutation.core Ω :=
  ⟨Pi.single p (1 : ZMod 2) + BinaryPermutation.allOne Ω, by
    change BinaryPermutation.augmentation Ω _ = 0
    rw [map_add, BinaryPermutation.augmentation_allOne, hΩ]
    simp [BinaryPermutation.augmentation]
    decide⟩

theorem coreSpike_action (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (hΩ : (Fintype.card Ω : ZMod 2) = 1) (g : Equiv.Perm Ω) (p : Ω) :
    coreSpike Ω hΩ (g p) = BinaryPermutation.coreRepresentation Ω g (coreSpike Ω hΩ p) := by
  apply Subtype.ext
  funext q
  change (Pi.single (g p) 1 : Ω → ZMod 2) q + 1 = (Pi.single p 1 : Ω → ZMod 2) (g.symm q) + 1
  simp only [Pi.single_apply, Equiv.symm_apply_eq]

def pointSpike (p : Point) : Core :=
  coreSpike Point (by rw [Matrix.PSL3Two.Fano.card_point]; decide) p

def lineSpike (l : Line) : LineCore :=
  coreSpike Line (by rw [Matrix.PSL3Two.Fano.card_line]; decide) l

@[simp] theorem pointSpike_apply (p q : Point) :
    (pointSpike p).val q = (Pi.single p 1 : Point → ZMod 2) q + 1 := rfl
@[simp] theorem lineSpike_apply (l m : Line) :
    (lineSpike l).val m = (Pi.single l 1 : Line → ZMod 2) m + 1 := rfl

theorem pointSpike_action (g : Group) (p : Point) :
    pointSpike (pointPerm g p) = U₂ g (pointSpike p) := coreSpike_action _ _ _ _

theorem lineSpike_action (g : Group) (l : Line) :
    lineSpike (linePerm g l) = lineCoreRepresentation g (lineSpike l) :=
  coreSpike_action _ _ _ _

/-- The rank-one trace-zero endomorphism of an incident flag. -/
noncomputable def flagRankOne (f : Flag) : Steinberg :=
  ⟨(lineFunctional f.val.2).smulRight f.val.1.val, by
    change LinearMap.trace (ZMod 2) Vector _ = 0
    rw [LinearMap.trace_smulRight]
    exact (incident_iff _ _).mp f.property⟩

@[simp] theorem flagRankOne_apply (f : Flag) (v : Vector) :
    (flagRankOne f).val v = lineFunctional f.val.2 v • f.val.1.val := rfl

theorem flagRankOne_action (g : Group) (f : Flag) :
    flagRankOne (flagPerm g f) = S g (flagRankOne f) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  change lineFunctional (linePerm g f.val.2) v • W g f.val.1.val =
    W g (lineFunctional f.val.2 (W g⁻¹ v) • f.val.1.val)
  rw [lineFunctional_action, map_smul]
  rfl

/-- Explicit parenthesization of the four proposed summands. -/
abbrev Target := ZMod 2 × (Core × (LineCore × Steinberg))

/-- The actual trivial, point-core, line-core and adjoint actions. -/
noncomputable def targetRepresentation : Representation (ZMod 2) Group Target :=
  (Representation.trivial (ZMod 2) Group (ZMod 2)).prod
    (U₂.prod (lineCoreRepresentation.prod S))

/-- The specified value of the flag map on a permutation basis vector. -/
noncomputable def flagValue (f : Flag) : Target :=
  (1, (pointSpike f.val.1, (lineSpike f.val.2, flagRankOne f)))

theorem flagValue_action (g : Group) (f : Flag) :
    flagValue (flagPerm g f) = targetRepresentation g (flagValue f) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact pointSpike_action g f.val.1
    · exact Prod.ext (lineSpike_action g f.val.2) (flagRankOne_action g f)

/-- Linear extension of the literal flag formula. -/
noncomputable def flagLinearMap : BinaryPermutation.Full Flag →ₗ[ZMod 2] Target where
  toFun a := ∑ f : Flag, a f • flagValue f
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [smul_smul, Finset.smul_sum]

@[simp] theorem flagLinearMap_apply (a : BinaryPermutation.Full Flag) :
    flagLinearMap a = ∑ f : Flag, a f • flagValue f := rfl

@[simp] theorem flagRepresentation_apply (g : Group) (a : BinaryPermutation.Full Flag) (f : Flag) :
    flagRepresentation g a f = a ((flagPerm g).symm f) := rfl

/-- The concrete flag map, equivariant for all actual group elements. -/
noncomputable def flagMap : Representation.IntertwiningMap flagRepresentation targetRepresentation where
  toLinearMap := flagLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro a
    change flagLinearMap (flagRepresentation g a) = targetRepresentation g (flagLinearMap a)
    rw [flagLinearMap_apply, flagLinearMap_apply]
    rw [← Equiv.sum_comp (flagPerm g) (fun f : Flag =>
      flagRepresentation g a f • flagValue f)]
    simp only [flagRepresentation_apply, Equiv.symm_apply_apply,
      flagValue_action, map_sum, map_smul]

@[simp] theorem flagMap_apply (a : BinaryPermutation.Full Flag) :
    flagMap a = ∑ f : Flag, a f • flagValue f := rfl

/-- On each actual flag basis vector the map has exactly the required formula. -/
theorem flagMap_basis (f : Flag) : flagMap (Pi.single f 1) =
    (1, (pointSpike f.val.1, (lineSpike f.val.2, flagRankOne f))) := by
  rw [flagMap_apply]
  simp [Pi.single_apply, flagValue]

end BinaryLinearThree.FanoDecomposition
