module

public import Theory.Representation.EndFieldRep
public import Theory.Representation.FirstCohomologyLinearTransport
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Transport of the actual binary Schur-field action

A field isomorphism from the commuting endomorphism field supplies scalar
multiplication on the original carrier V. The transported representation has
exactly the original binary action. Compatible embeddings of the two scalar
fields identify their scalar extensions by an actual intertwining equivalence.

This is the transport step in finite-field descent (GLS III, Remark 2.8.8).
The concrete SL₃ models and their classification are separate inputs.
-/

@[expose] public section

open scoped MonoidAlgebra TensorProduct
open Representation

namespace Representation.BinaryFieldDescent
variable {G V S : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ] [Field S]

/-- The actual commuting endomorphism ring of the binary action. -/
abbrev EndField := Module.End (ZMod 2)[G] ρ.asModule

/-- Transfer the Schur-field scalars to the original additive group V. -/
@[instance_reducible] noncomputable def scalarModule (e : EndField ρ ≃+* S) : Module S V := by
  letI : Module S ρ.asModule := Module.compHom _ e.symm.toRingHom
  exact ρ.asModuleEquiv.symm.toAddEquiv.module S

/-- The original group action, linear over the transported scalar field. -/
noncomputable def scalarRep (e : EndField ρ ≃+* S) :
    letI := scalarModule ρ e
    Representation S G V := by
  letI := scalarModule ρ e
  exact
    { toFun g :=
        { (ρ g).toAddHom with
          map_smul' s v := by
            change ρ.asModuleEquiv (ρ.endFieldRep g
              ((e.symm s) • ρ.asModuleEquiv.symm v)) =
              ρ.asModuleEquiv ((e.symm s) • ρ.endFieldRep g (ρ.asModuleEquiv.symm v))
            rw [map_smul] }
      map_one' := by ext v; exact LinearMap.congr_fun ρ.map_one v
      map_mul' g h := by ext v; exact LinearMap.congr_fun (ρ.map_mul g h) v }

omit [FiniteDimensional (ZMod 2) V] [IsIrreducible ρ] in
@[simp] theorem scalarRep_apply (e : EndField ρ ≃+* S) (g : G) (v : V) :
    scalarRep ρ e g v = ρ g v := rfl

omit [FiniteDimensional (ZMod 2) V] [IsIrreducible ρ] in
/-- Binary restriction is the original representation, as an equality. -/
theorem restrict_scalarRep [Algebra (ZMod 2) S] (e : EndField ρ ≃+* S) :
    letI := scalarModule ρ e
    restrictScalars (k := ZMod 2) (scalarRep ρ e) = ρ := by
  ext g v
  rfl

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- The original Schur carrier and V are semilinearly equivalent over the
specified field isomorphism. -/
noncomputable def scalarEquiv (e : EndField ρ ≃+* S) :
    letI := scalarModule ρ e
    LinearEquiv (e : EndField ρ →+* S) (σ' := (e.symm : S →+* EndField ρ)) ρ.asModule V := by
  letI := scalarModule ρ e
  exact
    { ρ.asModuleEquiv.toAddEquiv with
      map_smul' a v := by
        change ρ.asModuleEquiv (a • v) = ρ.asModuleEquiv (e.symm (e a) • v)
        rw [e.symm_apply_apply] }

variable {K : Type*} [Field K] [Algebra (EndField ρ) K] [Algebra S K]

/-- Compatible field embeddings identify the two extended actions. -/
noncomputable def scalarExtensionEquiv (e : EndField ρ ≃+* S)
    (he : ∀ a, algebraMap S K (e a) = algebraMap (EndField ρ) K a) :
    letI := scalarModule ρ e
    (extendScalars K ρ.endFieldRep).Equiv (extendScalars K (scalarRep ρ e)) := by
  letI := scalarModule ρ e
  let eK : LinearEquiv (e : EndField ρ →+* S) (σ' := (e.symm : S →+* EndField ρ)) K K :=
    { _root_.Equiv.refl K with
      map_add' _ _ := rfl
      map_smul' a x := by
        change a • x = e a • x
        simp only [Algebra.smul_def, he] }
  let eT := TensorProduct.congr eK (scalarEquiv ρ e)
  let eL : (K ⊗[EndField ρ] ρ.asModule) ≃ₗ[K] (K ⊗[S] V) :=
    { eT.toAddEquiv with
      map_smul' c t := by
        change eT (c • t) = c • eT t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul a v =>
          simp only [TensorProduct.smul_tmul']
          rfl
        | add x y hx hy => simp only [smul_add, map_add, hx, hy] }
  refine .mk eL ?_
  intro g
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    change eT ((extendScalars K ρ.endFieldRep) g (a ⊗ₜ[EndField ρ] v)) =
      (extendScalars K (scalarRep ρ e)) g (eT (a ⊗ₜ[EndField ρ] v))
    simp only [extendScalars_apply, LinearMap.baseChange_tmul]
    rfl
  | add x y hx hy => simp_all only [map_add, LinearMap.comp_apply]

end Representation.BinaryFieldDescent
