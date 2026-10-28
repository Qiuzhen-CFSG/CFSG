module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.TensorAction
public import Theory.Representation.SL2.BinaryNaturalTripleRecognition.FieldIdentification

/-!
# The original fixed field as scalar endomorphisms of the cubic module

The tensor comparison embeds the original cubic field in the algebraic
closure of the actual Schur field. Restrict this same embedding to the
source fixed subfield. Its order equals the Schur field's order, so the
finite-field roots-of-X^q-X argument gives a compatible field equivalence.
Transporting the actual scalar endomorphisms along it gives a module of
dimension eight over the source fixed field, with the original group action.

This supplies the scalar form of the literal radical action in Fong--Seitz
II, printed p.218. The companion TensorApplication constructs it on that
quotient. No unrelated field marking, matrix action or basis is assumed.
The particular root-coordinate basis and trace equations on p.219 remain
necessary for the positive and signed source relations.
-/

@[expose] public noncomputable section
open scoped MatrixGroups MonoidAlgebra TensorProduct
open Representation
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.TensorForm
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) SL(2,F) V) [ρ.IsIrreducible]
local notation "E" => Module.End (ZMod 2)[SL(2,F)] ρ.asModule
local notation "C" => AlgebraicClosure (Module.End (ZMod 2)[SL(2,F)] ρ.asModule)

/-- A single embedding identifies the actual fixed subfield with the scalar
endomorphisms of the original module, compatibly with the tensor action. -/
theorem compatible_comparison (K : Subfield F)
    (hnt : ∃ g,ρ g ≠ 1) {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2^(3*n)) (hV : Module.finrank (ZMod 2) V = 8*n)
    (hK : Nat.card K = 2^n) (σ : F ≃+* F) (hσ : ∀ x,σ x = x^(2^n)) :
    ∃ κ : F →+* C, ∃ c : K ≃+* E,
      (algebraMap E C).comp c.toRingHom = κ.comp K.subtype ∧
      Nonempty ((extendScalars C ρ.endFieldRep).Equiv (TensorAction.cubicTensor κ σ)) := by
  obtain ⟨κ,hκ⟩ := TensorAction.recognition ρ hnt hn hF hV σ hσ
  have hc : Nat.card K = Nat.card E := by
    let : Module.Finite (ZMod 2) E := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E),Nat.card_zmod,
      TensorWeights.schur_degree ρ hnt hn hF hV,hK]
  obtain ⟨c,hc⟩ := Representation.SL2.BinarySmall.exists_fieldEquiv_comp_eq_of_card_eq
    (κ.comp K.subtype) (algebraMap E C) hc
  exact ⟨κ,c,hc,hκ⟩


variable (K : Subfield F)
variable (c : K ≃+* Module.End (ZMod 2)[SL(2,F)] ρ.asModule)

/-- The scalar action of the actual fixed field, through its compatible
embedding in the endomorphisms of the original source module. -/
@[instance_reducible] def fixedModule : Module K ρ.asModule :=
  Module.compHom ρ.asModule (c.toRingHom : K →+* Module.End (ZMod 2)[SL(2,F)] ρ.asModule)

/-- The original group action, now linear over that same fixed field. -/
def fixedAction : letI := fixedModule ρ K c; Representation K SL(2,F) ρ.asModule := by
  letI := fixedModule ρ K c
  exact {
    toFun g := {
      toFun := ρ.endFieldRep g
      map_add' := map_add (ρ.endFieldRep g)
      map_smul' a v := (ρ.endFieldRep g).map_smul (c a) v }
    map_one' := by ext v; exact LinearMap.congr_fun ρ.endFieldRep.map_one v
    map_mul' g h := by ext v; exact LinearMap.congr_fun (ρ.endFieldRep.map_mul g h) v }

omit [Finite F] [CharP F 2] [FiniteDimensional (ZMod 2) V] [ρ.IsIrreducible] in
/-- The fixed-field action still acts on the literal underlying source vector. -/
theorem fixedAction_apply (g : SL(2,F)) (v : ρ.asModule) :
    letI := fixedModule ρ K c
    ρ.asModuleEquiv (fixedAction ρ K c g v) = ρ g (ρ.asModuleEquiv v) :=
  ρ.asModuleEquiv.apply_symm_apply _

/-- The source field identifies with all scalar endomorphisms, so the source
module has dimension exactly eight over it. -/
theorem fixed_dimension (hnt : ∃ g,ρ g ≠ 1) {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2^(3*n)) (hV : Module.finrank (ZMod 2) V = 8*n) :
    letI := fixedModule ρ K c
    Module.finrank K ρ.asModule = 8 := by
  let := fixedModule ρ K c
  let : Algebra K E := c.toRingHom.toAlgebra
  let : IsScalarTower K E ρ.asModule := {
    smul_assoc a b v := by change (c a*b) • v = c a • (b • v); exact mul_smul _ _ _ }
  let : Finite ρ.asModule := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) ρ.asModule)
  let : Module.Finite E ρ.asModule := Module.Finite.of_finite
  have he : Module.finrank K E = 1 := Module.finrank_of_bijective_algebraMap c.bijective
  have hs := TensorWeights.schur_degree ρ hnt hn hF hV
  have ht := Module.finrank_mul_finrank (ZMod 2) E ρ.asModule
  rw [hs,ρ.asModuleEquiv.finrank_eq,hV] at ht
  have hd : Module.finrank E ρ.asModule = 8 := by nlinarith
  rw [←Module.finrank_mul_finrank K E ρ.asModule,he,hd,one_mul]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.TensorForm
