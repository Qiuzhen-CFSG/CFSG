module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.TensorForm
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.CubicRatio
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.GeometricScalars

/-!
# The actual source radical action as a cubic tensor

Use the canonical radical abelianization in the same marked quotient and
conjugation by the entire short rank-one pinning. The existing unequal
linear geometry proves this action irreducible and of binary dimension 8n.
TensorWeights and TensorAction then construct its three-factor Frobenius
tensor comparison, following extension of its actual Schur field. This
proves the representation-selection input from Fong--Seitz (4.7)(b) used
on II printed p.218, including q=2 and q=4.

Restrict the same tensor embedding to the original fixed subfield. The
compatible field equivalence identifies it with scalar endomorphisms;
constructed_comparison constructs the actual dimension-eight action over
this field without changing the quotient or its group action. The conjugation
equation identifies the action of the aligned geometric pinning on literal
source representatives, for both orientations.

The elementary abelian, dimension and irreducibility hypotheses are proved
internally in constructed_comparison. The original ScalarMarking, local
PSL₂ identifications and source quotient hypotheses remain explicit. The
root-coordinate basis comparison, trace pairings, lifted short–short and
full mixed equations, covariance and remaining signed torus equations are
still required for full marked recognition. In particular this module does
not discharge NaturalScalarAction.compare_tensor's coordinate formula.

Source: Fong--Seitz I (6E)(b); II (4.7), (9.22)--(9.29), printed pp.217--219.
The tensor factors use the q-Frobenius of the same cubic source field, and
the fixed-field identification is its restriction, not a separate marking.
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
open Representation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.TensorApplication
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (σ : F ≃+* F) (indices : Fin 2 ≃ Fin 2)
  (hVi : simpleRemainder Q split (indices 0) ≤ localKernel Q (indices 0))
  (hVj : simpleRemainder Q split (indices 1) ≤ localKernel Q (indices 1))
  (μi : localGroup Q split (indices 0) ≃* PSL(2,F))
  (μj : localGroup Q split (indices 1) ≃* PSL(2,ScalarMarking.SourceFixed (σ := σ)))
  (hm : rotationOrder Q = 6)
local notation "K" => ScalarMarking.SourceFixed (σ := σ)
local notation "i" => indices 0
local notation "j" => indices 1
local notation "hij" => indices.injective.ne (by decide : (0 : Fin 2) ≠ 1)
local notation "si" => UnitarySource.actorReflection Q split i
local notation "sj" => UnitarySource.actorReflection Q split j

variable [hEA : IsElementaryAbelian 2 (RadicalQuotient Q split (indices 0))]
include hEA

/-- Conjugation by the original short pinning on the literal radical
abelianization. Its prime-field module structure is constructed from the roots. -/
def sourceAction : Representation (ZMod 2) SL(2,F) (Additive (RadicalQuotient Q split i)) :=
  (radicalRepresentation Q split i hVi).comp (alignedPinning Q split i hVi μi si).toMonoidHom

local notation "ρ" => sourceAction Q split indices hVi μi
variable {n : ℕ} {hn : 0 < n} (e : ScalarMarking (binaryParameters n hn) σ)

omit hEA [Finite F] [CharP F 2] in
include e in
private theorem field_card : Nat.card F = 2^(3*n) := by
  rw [scalarMarking_sourceExtension_card e,←pow_mul]
  congr 1
  omega

include hVj μj hm e in
/-- The same quotient's action is irreducible, including the binary endpoint. -/
theorem irreducible : (ρ).IsIrreducible := by
  let : (radicalRepresentation Q split i hVi).IsIrreducible :=
    unequal_linear_radical_irreducible Q split hm j i (hij).symm hVj hVi μj μi sj si
      hn (by omega : n < 3*n) (scalarMarking_sourceFixed_card e)
      (field_card σ e)
  exact (Representation.irreducible_comp_surjective_iff
    (alignedPinning Q split i hVi μi si).toMonoidHom
    (alignedPinning Q split i hVi μi si).surjective
    (radicalRepresentation Q split i hVi)).mpr inferInstance

include hVi hVj μi μj hm e in
/-- Exact prime-field dimension of this actual source section. -/
theorem binary_dimension : Module.finrank (ZMod 2) (Additive (RadicalQuotient Q split i)) = 8*n := by
  have hh := unequal_linear_radical_finrank Q split hm j i (hij).symm hVj hVi μj μi sj si
    hn (by omega : n < 3*n) (scalarMarking_sourceFixed_card e) (field_card σ e)
  simpa only [show 2*n+2*(3*n) = 8*n by omega] using hh

include hVj hm in
/-- The source rank-one actor acts faithfully, hence nontrivially. -/
theorem nontrivial_action : ∃ g,(ρ) g ≠ 1 := by
  have hf : Function.Injective (ρ) :=
    (linear_radicalRepresentation_injective Q split i hVi μi si hm j (hij).symm hVj).comp
      (alignedPinning Q split i hVi μi si).injective
  refine ⟨uni 1,fun he => ?_⟩
  have hh := hf (he.trans (map_one (ρ)).symm)
  have h01 := congrArg (fun g : SL(2,F) => g.val 0 1) hh
  simp [uni] at h01

include hVj μj hm e in
/-- The actual Schur field has the source fixed field's degree. -/
theorem schur_degree : Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,F)] (ρ).asModule) = n := by
  let := irreducible Q split σ indices hVi hVj μi μj hm e
  exact TensorWeights.schur_degree (ρ) (nontrivial_action Q split indices hVi hVj μi hm)
    hn (field_card σ e) (binary_dimension Q split σ indices hVi hVj μi μj hm e)

omit hEA [Finite F] [CharP F 2] in
include e in
/-- The source automorphism is the same q-Frobenius used by the tensor factors. -/
theorem frobenius_power (a : F) : σ a = a^(2^n) := by
  apply e.extension.injective
  rw [e.frobenius,fieldFrobenius_apply,map_pow]
  rfl

include hVj μj hm e in
/-- Construct the actual tensor equivalence of the original source action
following extension of its Schur field. No tensor-action premise is supplied. -/
theorem tensor_equivalence :
    letI := irreducible Q split σ indices hVi hVj μi μj hm e
    ∃ κ : F →+* AlgebraicClosure (Module.End (ZMod 2)[SL(2,F)] (ρ).asModule),
      Nonempty ((extendScalars
        (AlgebraicClosure (Module.End (ZMod 2)[SL(2,F)] (ρ).asModule)) (ρ).endFieldRep).Equiv
          (TensorAction.cubicTensor κ σ)) := by
  let := irreducible Q split σ indices hVi hVj μi μj hm e
  exact TensorAction.recognition (ρ) (nontrivial_action Q split indices hVi hVj μi hm)
    hn (field_card σ e) (binary_dimension Q split σ indices hVi hVj μi μj hm e)
    σ (frobenius_power σ e)

variable (row : StructuralRow Q split (indices 0) (indices 1))
local notation "q" => GeometricScalars.alignedPair Q split σ indices hVi hVj μi μj hm row e

include row in
/-- The tensor comparison uses the unchanged whole short actor of the
aligned geometric pinning, on the original quotient itself. -/
theorem action_conjugation (g : SL(2,F)) (v v' : simpleRemainder Q split i)
    (hv : (v' : X ⧸ Q.D) = (q).shortMap g * v * ((q).shortMap g)⁻¹) :
    (ρ) g (Additive.ofMul (Abelianization.of v)) = Additive.ofMul (Abelianization.of v') := by
  change radicalRepresentation Q split i hVi (alignedPinning Q split i hVi μi si g)
    (Additive.ofMul (Abelianization.of v)) = _
  rw [radicalRepresentation_of]
  apply congrArg Additive.ofMul
  apply congrArg Abelianization.of
  apply Subtype.ext
  exact (radicalAction_apply Q split i hVi (alignedPinning Q split i hVi μi si g) v).trans hv.symm


omit hEA in
/-- Construct both compatible scalar fields, the dimension-eight fixed-field
form, and the tensor comparison on the literal quotient. The elementary
abelian and irreducible instances are proved internally from the geometry. -/
theorem constructed_comparison :
    letI := linear_pair_radicalQuotient_elementary Q split hm j i (hij).symm μj μi
    letI := irreducible Q split σ indices hVi hVj μi μj hm e
    ∃ κ : F →+* AlgebraicClosure (Module.End (ZMod 2)[SL(2,F)] (ρ).asModule),
      ∃ c : K ≃+* Module.End (ZMod 2)[SL(2,F)] (ρ).asModule,
        (algebraMap _ _).comp c.toRingHom = κ.comp (ScalarMarking.SourceFixed (σ := σ)).subtype ∧
        Nonempty ((extendScalars
          (AlgebraicClosure (Module.End (ZMod 2)[SL(2,F)] (ρ).asModule)) (ρ).endFieldRep).Equiv
            (TensorAction.cubicTensor κ σ)) ∧
        (letI := TensorForm.fixedModule (ρ) (ScalarMarking.SourceFixed (σ := σ)) c
         Module.finrank K (ρ).asModule = 8 ∧
         ∀ (g : SL(2,F)) (v : (ρ).asModule),
           (ρ).asModuleEquiv (TensorForm.fixedAction (ρ) (ScalarMarking.SourceFixed (σ := σ)) c g v) =
             (ρ) g ((ρ).asModuleEquiv v)) := by
  let := linear_pair_radicalQuotient_elementary Q split hm j i (hij).symm μj μi
  let := irreducible Q split σ indices hVi hVj μi μj hm e
  obtain ⟨κ,c,hc,hκ⟩ := TensorForm.compatible_comparison (ρ)
    (ScalarMarking.SourceFixed (σ := σ)) (nontrivial_action Q split indices hVi hVj μi hm)
    hn (field_card σ e) (binary_dimension Q split σ indices hVi hVj μi μj hm e)
    (scalarMarking_sourceFixed_card e) σ (frobenius_power σ e)
  refine ⟨κ,c,hc,hκ,?_,?_⟩
  · exact TensorForm.fixed_dimension (ρ) (ScalarMarking.SourceFixed (σ := σ)) c
      (nontrivial_action Q split indices hVi hVj μi hm) hn (field_card σ e)
      (binary_dimension Q split σ indices hVi hVj μi μj hm e)
  · exact TensorForm.fixedAction_apply (ρ) (ScalarMarking.SourceFixed (σ := σ)) c

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.TensorApplication
