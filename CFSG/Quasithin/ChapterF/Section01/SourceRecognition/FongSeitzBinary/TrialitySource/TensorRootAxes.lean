module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.TensorRealization
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.TensorApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.LongRootApplication

/-!
# Literal long-root axes in the source cubic tensor

The simple long root embeds in the canonical short radical's abelianization:
its possible kernel lies in the structural derived root, and the canonical
hexagon roots are disjoint. Its short-Weyl conjugate commutes with every
short upper root by 6E(b). The cubic tensor's fixed-line calculation thus
places these two literal long roots on its extreme axes, with one faithful
additive coefficient. Simultaneously normalize both axes at parameter one.

The commutator representative is B(t)⁻¹ A(a)⁻¹ B(t) A(a), in the same
radical, with its actual quotient class. The constructed chart computes
all eight coordinates of this class and the cubic-norm character on the
highest long axis. Elementarity, irreducibility and the chart are all
constructed from the stated same-quotient geometric inputs. No matrix or
root-axis equation is assumed, and q=2 and q=4 are included.

The coefficient is currently an additive embedding of the original fixed
field, not yet identified with the restriction of the tensor embedding.
The middle short-root coordinates, that scalar compatibility, trace
pairings, lifted products and covariance remain necessary for the full
source presentation. These equations modulo the derived root do not
replace its missing highest-root coefficient or full marked comparison.

Source: Fong--Seitz I (6E)(b), printed p.43; II, printed pp.218--219,
including the basis comparison preceding (9.27) and the module calculations
underlying (9.29) and (9.31). All group actions use left conjugation.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.PSL2.SemilinearCoverage
open scoped MatrixGroups MonoidAlgebra TensorProduct
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
open Triality.Standard Triality.Standard.RootPresentationRecognition
open Representation Representation.SL2.BinarySmall
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.TensorRootAxes
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (σ : F ≃+* F) (indices : Fin 2 ≃ Fin 2)
  (hVi : simpleRemainder Q split (indices 0) ≤ localKernel Q (indices 0))
  (hVj : simpleRemainder Q split (indices 1) ≤ localKernel Q (indices 1))
  (μi : localGroup Q split (indices 0) ≃* PSL(2,F))
  (μj : localGroup Q split (indices 1) ≃* PSL(2,ScalarMarking.SourceFixed (σ := σ)))
  (hm : rotationOrder Q = 6)
  (row : StructuralRow Q split (indices 0) (indices 1))
  {n : ℕ} {hn : 0 < n} (e : ScalarMarking (binaryParameters n hn) σ)
local notation "K" => ScalarMarking.SourceFixed (σ := σ)
local notation "i" => indices 0
local notation "j" => indices 1
local notation "si" => UnitarySource.actorReflection Q split i
local notation "q" => GeometricScalars.alignedPair Q split σ indices hVi hVj μi μj hm row e
local notation "w" => GeometricScalars.alignedPlacement Q split σ indices hVi hVj μi μj hm row e
local notation "hs" => GeometricScalars.aligned_short_range Q split σ indices hVi hVj μi μj hm row e
local notation "hl" => GeometricScalars.aligned_long_range Q split σ indices hVi hVj μi μj hm row e
local notation "cc" => StructuralApplication.positiveCommutations Q split (q) (w) (hs) (hl) hm row

def longLift : Multiplicative K →* simpleRemainder Q split i :=
  ((q).longOrbit 0).codRestrict _ (fun a =>
    simpleRoot_le_other_remainder Q split hm j i (indices.injective.ne (by decide))
      ((hl) ▸ (show (q).longOrbit 0 a ∈ ((q).longOrbit 0).range from ⟨a,rfl⟩)))

local notation "b" => longLift Q split σ indices hVi hVj μi μj hm row e

theorem longLift_coe (a : K) : ((b) (.ofAdd a) : X ⧸ Q.D) = (q).l 0 a := rfl

def longVector : K →+ Additive (RadicalQuotient Q split i) :=
  (Abelianization.of.comp (b)).toAdditive

local notation "vB" => longVector Q split σ indices hVi hVj μi μj hm row e

def upperLift (a : K) : simpleRemainder Q split i :=
  radicalAction Q split i hVi (alignedPinning Q split i hVi μi si (weyl F)) ((b) (.ofAdd a))

local notation "vE" => upperLift Q split σ indices hVi hVj μi μj hm row e

theorem upperLift_coe (a : K) : ((vE) a : X ⧸ Q.D) = (q).l 1 a := by
  rw [upperLift,radicalAction_apply]
  rfl

variable [hEA : IsElementaryAbelian 2 (RadicalQuotient Q split (indices 0))]
include hEA
local notation "ρ" => TensorApplication.sourceAction Q split indices hVi μi (hEA := hEA)

theorem weyl_longVector (a : K) :
    (ρ) (weyl F) ((vB) a) = Additive.ofMul (Abelianization.of ((vE) a)) := by
  exact radicalRepresentation_of Q split i hVi _ _

theorem upper_fixed (a : K) (t : F) :
    (ρ) (uni t) ((ρ) (weyl F) ((vB) a)) = (ρ) (weyl F) ((vB) a) := by
  rw [weyl_longVector]
  change radicalRepresentation Q split i hVi (alignedPinning Q split i hVi μi si (uni t))
    (Additive.ofMul (Abelianization.of ((vE) a))) = _
  rw [radicalRepresentation_of]
  apply congrArg Additive.ofMul
  apply congrArg Abelianization.of
  apply Subtype.ext
  rw [radicalAction_apply,upperLift_coe]
  exact ((cc).short0_long1 t a).mul_inv_cancel

omit hEA in
theorem longVector_injective : Function.Injective (vB) := by
  apply (injective_iff_map_eq_zero (vB)).mpr
  intro a ha
  have hker : (b) (.ofAdd a) ∈
      (Abelianization.of : simpleRemainder Q split i →* RadicalQuotient Q split i).ker := by
    exact congrArg Additive.toMul ha
  have hmem : (q).l 0 a ∈ ((q).longOrbit 2).range := by
    rw [ModuleApplication.long_two_rootAt Q split (q) (w) (hl)]
    change (q).l 0 a ∈ rootAt Q split j (Q.simple i * Q.simple j)
    rw [← row.radical_derived,← radicalProjection_kernel]
    exact ⟨(b) (.ofAdd a),hker,rfl⟩
  have hmem' : (q).l 1 a ∈ ((q).longOrbit 2).range := by
    obtain ⟨t,ht⟩ := hmem
    refine ⟨t,?_⟩
    exact ((q).orthogonalLong t.toAdd).symm.trans (congrArg (q).dihedral.A ht)
  have hz : (q).longOrbit 1 (.ofAdd a) = 1 :=
    (Subgroup.disjoint_def.mp (ModuleApplication.long_ranges_disjoint Q split (q) (w) (hl) hm))
      ⟨.ofAdd a,rfl⟩ hmem'
  have hi := (q).longOrbit_injective
    (GeometricLongRoots.aligned_long_injective Q split σ indices hVi hVj μi μj hm row e) 1
  exact Multiplicative.ofAdd.injective (hi (hz.trans ((q).longOrbit 1).map_one.symm))

omit hEA in
def mixedLift (a : F) (t : K) : simpleRemainder Q split i :=
  ((b) (.ofAdd t))⁻¹ *
    radicalAction Q split i hVi (alignedPinning Q split i hVi μi si (uni a)) ((b) (.ofAdd t))

local notation "vM" => mixedLift Q split σ indices hVi hVj μi μj hm row e

omit hEA in
theorem mixedLift_coe (a : F) (t : K) :
    ((vM) a t : X ⧸ Q.D) = rightCommutator ((q).l 0 t) ((q).s 0 a) := by
  have hi : ((q).s 0 a)⁻¹ = (q).s 0 a := by
    change (((q).shortOrbit 0) (.ofAdd a))⁻¹ = _
    rw [← map_inv,← ofAdd_neg,CharTwo.neg_eq]
  change ((b) (.ofAdd t) : X ⧸ Q.D)⁻¹ *
    (radicalAction Q split i hVi (alignedPinning Q split i hVi μi si (uni a))
      ((b) (.ofAdd t)) : X ⧸ Q.D) = _
  rw [radicalAction_apply,longLift_coe]
  change ((q).l 0 t)⁻¹*((q).s 0 a*(q).l 0 t*((q).s 0 a)⁻¹) = _
  simp only [rightCommutator,hi,mul_assoc]

omit hEA in
def mixedVector (a : F) (t : K) : Additive (RadicalQuotient Q split i) :=
  .ofMul (Abelianization.of ((vM) a t))

local notation "dV" => mixedVector Q split σ indices hVi hVj μi μj hm row e

theorem mixedVector_eq (a : F) (t : K) :
    (dV) a t = (ρ) (uni a) ((vB) t) - (vB) t := by
  have ha : (ρ) (uni a) ((vB) t) = Additive.ofMul (Abelianization.of
      (radicalAction Q split i hVi (alignedPinning Q split i hVi μi si (uni a))
        ((b) (.ofAdd t)))) := radicalRepresentation_of Q split i hVi _ _
  rw [ha]
  change Additive.ofMul (Abelianization.of (((b) (.ofAdd t))⁻¹ *
    radicalAction Q split i hVi (alignedPinning Q split i hVi μi si (uni a)) ((b) (.ofAdd t)))) = _
  rw [map_mul,map_inv]
  change -Additive.ofMul (Abelianization.of ((b) (.ofAdd t))) + _ = _
  change -Additive.ofMul (Abelianization.of ((b) (.ofAdd t))) + _ =
    _ - Additive.ofMul (Abelianization.of ((b) (.ofAdd t)))
  abel

section MatrixEquation
variable {C : Type*} [Field C] (κ : F →+* C)
  (J : Additive (RadicalQuotient Q split (indices 0)) →+ TripleSpace C)
  (c : ScalarMarking.SourceFixed (σ := σ) →+ C)

/-- All eight coordinates of the literal mixed commutator modulo the
structural derived root. The source additive coefficient is the same on
both extreme long axes; its identification with the field inclusion is a
further compatibility step. -/
theorem mixed_coordinates
    (hact : ∀ (g : SL(2,F)) v, J ((ρ) g v) = TensorAction.cubicTensor κ σ g (J v))
    (hB : ∀ t, J ((vB) t) = c t • TensorCoordinates.basis ((1,1),1))
    (a : F) (t : K) (r s u : Fin 2) :
    TensorCoordinates.coordinates (J ((dV) a t)) ((r,s),u) =
      c t*(if r = 0 then κ a else 1)*(if s = 0 then κ (σ a) else 1)*
        (if u = 0 then κ (σ (σ a)) else 1) -
          (if ((r,s),u) = ((1,1),1) then c t else 0) := by
  rw [mixedVector_eq,map_sub,hact,hB,map_sub]
  simp only [Pi.sub_apply]
  rw [TensorCoordinates.upper_bottom]
  fin_cases r <;> fin_cases s <;> fin_cases u <;>
    simp [TensorCoordinates.coordinates]

/-- The source Cartan acts on the identified highest long axis by the
cubic norm through the same extension-field embedding. -/
theorem torus_coordinates
    (hact : ∀ (g : SL(2,F)) v, J ((ρ) g v) = TensorAction.cubicTensor κ σ g (J v))
    (hE : ∀ t, J (Additive.ofMul (Abelianization.of ((vE) t))) =
      c t • TensorCoordinates.basis ((0,0),0))
    (a : Fˣ) (t : K) :
    J ((ρ) (tor a) (Additive.ofMul (Abelianization.of ((vE) t)))) =
      κ (e.norm a.val).val • J (Additive.ofMul (Abelianization.of ((vE) t))) := by
  rw [hact,hE,map_smul,TensorCoordinates.tor_top,smul_smul,smul_smul]
  change (c t*κ (a.val*σ a.val*σ (σ a.val))) • _ =
    (κ (a.val*σ a.val*σ (σ a.val))*c t) • _
  rw [mul_comm]
end MatrixEquation

include hVj μj hm row e in
theorem source_axes :
    let := TensorApplication.irreducible Q split σ indices hVi hVj μi μj hm e
    ∃ κ : F →+* AlgebraicClosure (Module.End (ZMod 2)[SL(2,F)] (ρ).asModule),
      ∃ J : Additive (RadicalQuotient Q split i) →+
        TripleSpace (AlgebraicClosure (Module.End (ZMod 2)[SL(2,F)] (ρ).asModule)),
      ∃ c : K →+ AlgebraicClosure (Module.End (ZMod 2)[SL(2,F)] (ρ).asModule),
        Function.Injective J ∧ Function.Injective c ∧ c 1 = 1 ∧
        (∀ (g : SL(2,F)) v, J ((ρ) g v) = TensorAction.cubicTensor κ σ g (J v)) ∧
        (∀ a, J (Additive.ofMul (Abelianization.of ((vE) a))) =
          c a • TensorCoordinates.basis ((0,0),0)) ∧
        (∀ a, J ((vB) a) = c a • TensorCoordinates.basis ((1,1),1)) := by
  let := TensorApplication.irreducible Q split σ indices hVi hVj μi μj hm e
  have hF : Nat.card F = 2^(3*n) := by
    rw [scalarMarking_sourceExtension_card e,←pow_mul]
    congr 1
    omega
  have ht := TensorRealization.exists_normalized_axes (ρ)
    (TensorApplication.nontrivial_action Q split indices hVi hVj μi hm) hn hF
    (TensorApplication.binary_dimension Q split σ indices hVi hVj μi μj hm e)
    σ (TensorApplication.frobenius_power σ e) e.cubic (scalarMarking_exists_nonfixed e)
    (vB) (longVector_injective Q split σ indices hVi hVj μi μj hm row e)
    (upper_fixed Q split σ indices hVi hVj μi μj hm row e)
  simpa only [weyl_longVector] using ht

omit hEA in
/-- The actual quotient supplies elementarity and irreducibility internally.
The chart is constructed with both long axes normalized at parameter one. -/
def constructedCoordinates :
    letI := linear_pair_radicalQuotient_elementary Q split hm (indices 1) (indices 0)
      (indices.injective.ne (by decide)) μj μi
    letI := TensorApplication.irreducible Q split σ indices hVi hVj μi μj hm e
    TensorRealization.NormalizedAxes (TensorApplication.sourceAction Q split indices hVi μi)
      σ (vB) := by
  let hEA := linear_pair_radicalQuotient_elementary Q split hm (indices 1) (indices 0)
    (indices.injective.ne (by decide)) μj μi
  let := TensorApplication.irreducible Q split σ indices hVi hVj μi μj hm e
  have hF : Nat.card F = 2^(3*n) := by
    rw [scalarMarking_sourceExtension_card e,←pow_mul]
    congr 1
    omega
  exact TensorRealization.normalizedAxes (TensorApplication.sourceAction Q split indices hVi μi)
    (TensorApplication.nontrivial_action Q split indices hVi hVj μi hm) hn hF
    (TensorApplication.binary_dimension Q split σ indices hVi hVj μi μj hm e)
    σ (TensorApplication.frobenius_power σ e) e.cubic (scalarMarking_exists_nonfixed e)
    (vB) (longVector_injective Q split σ indices hVi hVj μi μj hm row e)
    (upper_fixed Q split σ indices hVi hVj μi μj hm row e)

omit hEA in
/-- The constructed chart supplies the mixed matrix equation and the norm
character on the literal source quotient, with no chart or matrix premise. -/
theorem constructed_equations :
    letI := linear_pair_radicalQuotient_elementary Q split hm (indices 1) (indices 0)
      (indices.injective.ne (by decide)) μj μi
    letI := TensorApplication.irreducible Q split σ indices hVi hVj μi μj hm e
    let d := constructedCoordinates Q split σ indices hVi hVj μi μj hm row e
    (∀ (a : F) (t : K) (r s u : Fin 2),
      TensorCoordinates.coordinates (d.chart ((dV) a t)) ((r,s),u) =
        d.coefficient t*(if r = 0 then d.embedding a else 1)*
          (if s = 0 then d.embedding (σ a) else 1)*
          (if u = 0 then d.embedding (σ (σ a)) else 1) -
            (if ((r,s),u) = ((1,1),1) then d.coefficient t else 0)) ∧
    (∀ (a : Fˣ) (t : K),
      d.chart (TensorApplication.sourceAction Q split indices hVi μi (tor a)
        (Additive.ofMul (Abelianization.of ((vE) t)))) =
      d.embedding (e.norm a.val).val • d.chart (Additive.ofMul (Abelianization.of ((vE) t)))) := by
  let hEA := linear_pair_radicalQuotient_elementary Q split hm (indices 1) (indices 0)
    (indices.injective.ne (by decide)) μj μi
  let := TensorApplication.irreducible Q split σ indices hVi hVj μi μj hm e
  let d := constructedCoordinates Q split σ indices hVi hVj μi μj hm row e
  constructor
  · exact mixed_coordinates Q split σ indices hVi hVj μi μj hm row e
      d.embedding d.chart d.coefficient d.action d.bottom
  · apply torus_coordinates Q split σ indices hVi hVj μi μj hm row e
      d.embedding d.chart d.coefficient d.action
    intro t
    exact (congrArg d.chart
      (weyl_longVector Q split σ indices hVi hVj μi μj hm row e t)).symm.trans (d.top t)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.TensorRootAxes
