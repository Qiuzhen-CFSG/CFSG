module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.DerivedOrbit
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.RankOneRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitaryLinearActions
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.TensorRealization

/-!
# Hermitian realization of the actual U₅ linear derived layer

The completed quadrangle structure gives an irreducible binary action of
SL₂(q²) on the radical-derived subgroup, of order q⁴. The small binary
classifier leaves the natural and Hermitian modules; the exceptional
SL₂(8) case has the wrong field degree. The actual opposite-root derived
layer has order at most q and is stable under the full linear torus.
The natural torus orbit bound therefore rules out the natural module.

The surviving Hermitian equivalence constructs coordinates on the entire
derived subgroup. Its action retains the original SL₂ marking exactly;
a second version aligns the complete actor with the specified source
reflection. Both include q = 2 and q = 4. No Hermitian-action equivalence
is an input. Identification of the individual root-center lines and
synchronization with the SU₃ coordinates remain later source steps.
Source: Fong--Seitz I (4C), (6A)(c); II (8C), p.206, (8.21)--(8.23).
Consumer: DerivedApplication supplies the original quotient and Q.q formulas.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative MonoidAlgebra
open BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource

variable {X K E : Type*} [Group X]
  [Field K] [Finite K] [CharP K 2] [Field E] [Finite E] [CharP E 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (J : HermitianForm 3 E) (n : ℕ) [NeZero n]
  (hK : Nat.card K = (2^n)^2) (hE : Nat.card E = (2^n)^2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (s : RootReflection Q split i) (μ : rankOne Q split i ≃* SL(2,K))
  (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)

include hK hE hfixed hJ hm hij hVi hVj s ν

/-- The source action selects the Hermitian branch of the actual small-module classifier. -/
theorem linear_derived_hermitian :
    ∃ he : IsElementaryAbelian 2
      (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)),
      letI := he
      SL2.BinarySmall.IsHermitian (linearDerivedRepresentation Q split i hVi μ) n := by
  obtain ⟨_,he,hcard,hi⟩ := unitary_linear_derived_irreducible Q split J (NeZero.pos n)
    hK hE hfixed hJ hm i j hij hVi hVj s μ ν
  let := he
  let ρ := elementaryRepresentation (p := 2) (remainderDerivedAction Q split i hVi)
  let σ := linearDerivedRepresentation Q split i hVi μ
  let : ρ.IsIrreducible := hi
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff μ.symm.toMonoidHom μ.symm.surjective ρ).mpr hi
  have hd : Module.finrank (ZMod 2)
      (Additive (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D))) = 4*n := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := Additive (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)))
    rw [Nat.card_zmod] at hc
    have hh : 2 ^ Module.finrank (ZMod 2)
        (Additive (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D))) =
        2^(4*n) := by
      rw [←hc]
      change Nat.card (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) = _
      rw [hcard,←pow_mul,Nat.mul_comm n 4]
    exact Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hh
  obtain ⟨_,hsmall,hne⟩ := simpleRoot_unitary_derived J (NeZero.pos n) hE hfixed hJ Q split j hVj ν
  have hnt : ∃ g, σ g ≠ 1 := by
    obtain ⟨r,hr⟩ := remainderDerivedAction_nontrivial Q split hm i j hij hVi s hne
    refine ⟨μ r,fun hz => hr ?_⟩
    apply DFunLike.ext
    intro v
    have hv := LinearMap.congr_fun hz (Additive.ofMul v)
    change Additive.ofMul (remainderDerivedAction Q split i hVi (μ.symm (μ r)) v) =
      Additive.ofMul v at hv
    change remainderDerivedAction Q split i hVi r v = v
    simpa only [MulEquiv.symm_apply_apply] using Additive.ofMul.injective hv
  have hK' : Nat.card K = 2^(2*n) := by rw [hK,←pow_mul,Nat.mul_comm n 2]
  refine ⟨he,?_⟩
  rcases ChapterG.Section09.DefiningCharacteristic.binary_small_module_alternatives
    σ hnt (2*n) (by have := NeZero.pos n; omega) hK' (by omega) with hnat | hherm | htriple
  · have hb := natural_derived_torus_bound Q split i hVi μ s j hij hne hnat.2.2
    rw [hK] at hb
    have hq : 2 ≤ 2^n := Nat.one_lt_pow (NeZero.ne n) (by decide)
    have hs0 : 1 ≤ (2^n)^2 := le_trans (by decide : 1 ≤ 2^2) (Nat.pow_le_pow_left hq 2)
    have hsq : 2^n < (2^n)^2-1 := by nlinarith [Nat.sub_add_cancel hs0]
    omega
  · obtain ⟨heq,_,hs,hh⟩ := hherm
    have heqn : Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] σ.asModule) = n := by omega
    simpa only [heqn] using hh
  · omega

open Representation.OrthogonalFourMinus.FiniteModel

local instance : Module (ZMod 2) (Space n) := SL2.BinarySmall.spaceBinaryModule n

/-- The complete derived subgroup has actual Hermitian coordinates,
equivariant for the original, unmodified linear actor. -/
theorem linear_derived_realization :
    ∃ (f : K ≃+* Field n)
      (c : Multiplicative (Space n) ≃*
        (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D))),
      ∀ (r : rankOne Q split i) (p : Space n),
        (r : X ⧸ Q.D) * (c (.ofAdd p) : X ⧸ Q.D) * (r : X ⧸ Q.D)⁻¹ =
          c (.ofAdd (action n (Matrix.SpecialLinearGroup.map f.toRingHom (μ r)) p)) := by
  obtain ⟨he,f,⟨u⟩⟩ := linear_derived_hermitian Q split J n hK hE hfixed hJ hm i j hij hVi hVj s μ ν
  let := he
  let c : Multiplicative (Space n) ≃*
      (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) := {
    toFun p := (u.symm p.toAdd).toMul
    invFun v := .ofAdd (u (.ofMul v))
    left_inv p := congrArg Multiplicative.ofAdd (u.apply_symm_apply p.toAdd)
    right_inv v := congrArg Additive.toMul (u.symm_apply_apply (.ofMul v))
    map_mul' p q := congrArg Additive.toMul (map_add u.symm p.toAdd q.toAdd) }
  refine ⟨f,c,fun r p => ?_⟩
  have hu : linearDerivedRepresentation Q split i hVi μ (μ r) (u.symm p) =
      u.symm (SL2.BinarySmall.hermitian n (Matrix.SpecialLinearGroup.map f.toRingHom (μ r)) p) := by
    apply u.injective
    change u (linearDerivedRepresentation Q split i hVi μ (μ r) (u.symm p)) =
      u (u.symm (SL2.BinarySmall.hermitian n (Matrix.SpecialLinearGroup.map f.toRingHom (μ r)) p))
    rw [Representation.Equiv.apply_symm_apply]
    have hi := LinearMap.congr_fun (u.isIntertwining' (μ r)) (u.symm p)
    exact hi.trans (congrArg
      (SL2.BinarySmall.hermitian n (Matrix.SpecialLinearGroup.map f.toRingHom (μ r)))
        (u.apply_symm_apply p))
  have hh := congrArg (fun z : Additive
    (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) =>
      (z.toMul : X ⧸ Q.D)) hu
  simp only [linearDerivedRepresentation,MonoidHom.comp_apply,elementaryRepresentation_apply,
    toMul_ofMul,remainderDerivedAction_apply,MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply]
      at hh
  convert hh using 1 <;> rfl

/-- The same realization can be pinned to a specified source reflection.
The entire actor is relabelled by the constructed field equivalence. -/
theorem aligned_derived_realization (μ₀ : localGroup Q split i ≃* PSL(2,K)) :
    ∃ (f : K ≃+* Field n)
      (c : Multiplicative (Space n) ≃*
        (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D))),
      ∀ (g : SL(2,Field n)) (p : Space n),
        UnitarySource.fieldRelabelledActor Q split i hVi μ₀ s n f g *
            (c (.ofAdd p) : X ⧸ Q.D) *
            (UnitarySource.fieldRelabelledActor Q split i hVi μ₀ s n f g)⁻¹ =
          c (.ofAdd (action n g p)) := by
  let pin := GTwoSource.alignedPinning Q split i hVi μ₀ s
  obtain ⟨f,c,hc⟩ := linear_derived_realization Q split J n hK hE hfixed hJ hm i j hij
    hVi hVj s pin.symm ν
  refine ⟨f,c,fun g p => ?_⟩
  let g' := Matrix.SpecialLinearGroup.map f.symm.toRingHom g
  have hg : Matrix.SpecialLinearGroup.map f.toRingHom g' = g :=
    (Atlas.fieldEquivSL 2 f).apply_symm_apply g
  have he := hc (pin g') p
  rw [MulEquiv.symm_apply_apply,hg] at he
  exact he

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
