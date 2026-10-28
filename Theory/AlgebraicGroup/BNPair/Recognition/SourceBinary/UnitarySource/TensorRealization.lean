module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.TensorTorus
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.FourTensor
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Transporting a genuine Hermitian intertwiner into source root coordinates

Relabel the entire reflection-aligned SL₂ actor by the field equivalence
returned by binary Hermitian recognition. Its upper root still maps onto
the same original simple root, and its Weyl matrix still maps to the
specified original reflection. The actual additive intertwiner, inverted
and written multiplicatively, then identifies the Hermitian tensor with
the literal complementary subgroup and intertwines conjugation exactly.

The input here is a genuine representation equivalence. It is proved
from the original quadratic profile in TensorApplication, using
TensorRecognition; it is not an extra premise of that source application.
The other endpoint's coordinates and the full scalar-torus compatibility
are separate remaining obligations.

Source: Fong--Seitz II (8B), pp.201--202; I (4C), pp.20--21.
-/

@[expose] public noncomputable section
open Subgroup Representation Matrix
open scoped MatrixGroups IsMulCommutative
open Theory.PSL2.SemilinearCoverage
open Representation.OrthogonalFourMinus
open Representation.OrthogonalFourMinus.FiniteModel
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
open RootCoordinates HexagonStructure QuadrangleStructure GTwoSource

variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (i : Fin 2) (hV : simpleRemainder Q split i ≤ localKernel Q i)
  (μ : localGroup Q split i ≃* PSL(2,F)) (s : RootReflection Q split i)
  (n : ℕ) [NeZero n]
local instance : Module (ZMod 2) (Space n) := Representation.SL2.BinarySmall.spaceBinaryModule n

/-- Relabel the entire same actor, retaining its source image. -/
def fieldRelabelledActor (f : F ≃+* Field n) : SL(2,Field n) →* X ⧸ Q.D :=
  (alignedPinningHom Q split i hV μ s).comp
    (SpecialLinearGroup.map f.symm.toRingHom)

omit [NeZero n] in
/-- Field transport preserves the actual simple-root parameter. -/
theorem fieldRelabelledActor_upper (f : F ≃+* Field n) (a : Field n) :
    fieldRelabelledActor Q split i hV μ s n f (uni a) =
      alignedSimpleParameter Q split i hV μ s (.ofAdd (f.symm a)) := by
  rw [alignedSimpleParameter_apply]
  apply congrArg (alignedPinningHom Q split i hV μ s)
  ext j k
  change f.symm ((uni a).val j k) = (uni (f.symm a)).val j k
  fin_cases j <;> fin_cases k <;> simp [uni_val]

omit [NeZero n] in
/-- The upper root is the entire original simple root. -/
theorem fieldRelabelledActor_root_range (f : F ≃+* Field n) :
    ((fieldRelabelledActor Q split i hV μ s n f).comp
      (SpecialLinearGroup.upperUnipotentHom (Field n))).range = simpleRoot Q split i := by
  rw [←alignedSimpleParameter_range Q split i hV μ s]
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨.ofAdd (f.symm a.toAdd),(fieldRelabelledActor_upper Q split i hV μ s n f a.toAdd).symm⟩
  · rintro ⟨a,rfl⟩
    refine ⟨.ofAdd (f a.toAdd),?_⟩
    change fieldRelabelledActor Q split i hV μ s n f (uni (f a.toAdd)) = _
    rw [fieldRelabelledActor_upper,RingEquiv.symm_apply_apply]
    rfl

omit [NeZero n] in
/-- The specified reflection is unchanged by field relabeling. -/
theorem fieldRelabelledActor_weyl (f : F ≃+* Field n) :
    fieldRelabelledActor Q split i hV μ s n f (weyl (Field n)) = (s.val : X ⧸ Q.D) := by
  rw [←alignedPinningHom_weyl Q split i hV μ s]
  apply congrArg (alignedPinningHom Q split i hV μ s)
  ext j k
  change f.symm ((weyl (Field n)).val j k) = (weyl F).val j k
  fin_cases j <;> fin_cases k <;> simp [weyl]

variable [IsElementaryAbelian 2 (simpleRemainder Q split i)]

/-- The actual binary intertwiner gives exact source tensor conjugation. -/
theorem tensorRealization_of_hermitian
    (hh : Representation.SL2.BinarySmall.IsHermitian
      (alignedRemainderRepresentation Q split i hV μ s) n) :
    ∃ (f : F ≃+* Field n)
      (e : Multiplicative (FourTensor.Core (Field n) (conjugation n) (conjugation_involutive n)) ≃*
        simpleRemainder Q split i),
      ∀ (g : SL(2,Field n)) (p : FourTensor.Core (Field n) (conjugation n) (conjugation_involutive n)),
        fieldRelabelledActor Q split i hV μ s n f g * (e (.ofAdd p) : X ⧸ Q.D) *
          (fieldRelabelledActor Q split i hV μ s n f g)⁻¹ =
        e (.ofAdd (hermitianAction (FourTensor.conjugation (Field n) (conjugation n))
          (conjugation_involutive n) g p)) := by
  obtain ⟨f,⟨u⟩⟩ := hh
  let e : Multiplicative (FourTensor.Core (Field n) (conjugation n) (conjugation_involutive n)) ≃*
      simpleRemainder Q split i := {
    toFun p := (u.symm p.toAdd).toMul
    invFun v := .ofAdd (u (.ofMul v))
    left_inv p := congrArg Multiplicative.ofAdd (u.apply_symm_apply p.toAdd)
    right_inv v := congrArg Additive.toMul (u.symm_apply_apply (.ofMul v))
    map_mul' p q := congrArg Additive.toMul (map_add u.symm p.toAdd q.toAdd) }
  refine ⟨f,e,fun g p => ?_⟩
  let g' := SpecialLinearGroup.map f.symm.toRingHom g
  have hg : SpecialLinearGroup.map f.toRingHom g' = g :=
    (Atlas.fieldEquivSL 2 f).apply_symm_apply g
  have hu : alignedRemainderRepresentation Q split i hV μ s g' (u.symm p) =
      u.symm (Representation.SL2.BinarySmall.hermitian n g p) := by
    apply u.injective
    change u (alignedRemainderRepresentation Q split i hV μ s g' (u.symm p)) =
      u (u.symm (Representation.SL2.BinarySmall.hermitian n g p))
    rw [Representation.Equiv.apply_symm_apply]
    have he := LinearMap.congr_fun (u.isIntertwining' g') (u.symm p)
    change u (alignedRemainderRepresentation Q split i hV μ s g' (u.symm p)) =
      Representation.SL2.BinarySmall.hermitian n (SpecialLinearGroup.map f.toRingHom g')
        (u (u.symm p)) at he
    rw [hg] at he
    exact he.trans (congrArg (fun x => Representation.SL2.BinarySmall.hermitian n g x)
      (u.apply_symm_apply p))
  have he := congrArg (fun z : Additive (simpleRemainder Q split i) => (z.toMul : X ⧸ Q.D)) hu
  simp only [alignedRemainderRepresentation,MonoidHom.comp_apply,elementaryRepresentation_apply,
    toMul_ofMul,remainderRankOneAction_apply,MulEquiv.coe_toMonoidHom,alignedPinning_coe] at he
  convert he using 1 <;> rfl

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
