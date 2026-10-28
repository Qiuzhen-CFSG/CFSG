module
public import Theory.SpecificGroups.LieType.F4RootCentralizer.Subsystem
public import Theory.SpecificGroups.LieType.F4RootCentralizer.CentralKernel

/-!
# Assembly maps for the F4 symplectic residual centralizer

This module constructs the actual maps from a faithful Sp6 action on the
F4 elementary lattice to the literal O^{p′} centralizer of the proved
fundamental SL2. The map to F4 is the given matrix homomorphism followed by
the defining central projection. Agreement of the scalar involution with
the long-root involution proves that projection preserves faithfulness.

The statements are conditional assembly lemmas, not a proof of the source
identification: the symplectic lattice homomorphism, its root-subgroup
range, commutation with SL2, and the residual upper containment must still
be constructed. No assumed abstract group isomorphism or order comparison
is used. The source-facing consumer is
`ChapterA.Section02.OddLie.ExceptionalStructure.F4Centralizer.Subsystem`.

Source: Aschbacher–Smith A.2.17, printed p.39 of `refs/quasithin.pdf`, and
its cited fundamental-subgroup centralizer theorem, Asc80, p.402.
-/

@[expose] public noncomputable section
namespace ExceptionalSplit.F4RootCentralizer
open F4RootSL2
open Theory.AlgebraicGroup.StandardRootSystem
open scoped MatrixGroups
attribute [local instance] Classical.decEq
local instance : Fintype typeF4Roots := Fintype.ofFinite _
variable {F : Type*} [Field F]

section Assembly
variable (p : ℕ) [CharP F p]
  (f : Matrix.symplecticGroup (Fin 3) F →* Elementary F)
  (hrange : f.range = elementaryComplement F)
  (hcomm : projectedComplement F ≤ Centralizer F)

/-- The proposed symplectic action followed by the actual quotient and residual restriction. -/
def symplecticToResidual : Matrix.symplecticGroup (Fin 3) F →* Residual p F :=
  (complementToResidual p hcomm).comp
    (f.codRestrict (elementaryComplement F) (fun x => hrange ▸ (show f x ∈ f.range from ⟨x, rfl⟩)))

/-- The ambient element is the literal central projection of the lattice action. -/
@[simp] theorem symplecticToResidual_val (x : Matrix.symplecticGroup (Fin 3) F) :
    ((symplecticToResidual p f hrange hcomm x).val : F4 F) =
      projection typeF4RootPairing typeF4RootPairing_base F (f x) := rfl

/-- The exact central-kernel condition implies faithfulness inside the residual. -/
theorem symplecticToResidual_injective
    (hkernel : ∀ x, f x ∈ Subgroup.center (Elementary F) → x = 1) :
    Function.Injective (symplecticToResidual p f hrange hcomm) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro x hx
  apply hkernel x
  apply (projection_eq_one_iff _ _ F _).mp
  exact congrArg (fun y : Residual p F => (y.val : F4 F)) hx

/-- The root-subgroup range and independent residual upper bound imply surjectivity. -/
theorem symplecticToResidual_surjective
    (hcover : (Subgroup.primeToResidual p (Centralizer F)).map
      (Centralizer F).subtype ≤ projectedComplement F) :
    Function.Surjective (symplecticToResidual p f hrange hcomm) := by
  intro x
  obtain ⟨y, rfl⟩ := complementToResidual_surjective p hcomm hcover x
  have hy : y.val ∈ f.range := hrange.symm ▸ y.property
  obtain ⟨z, hz⟩ := hy
  refine ⟨z, ?_⟩
  change complementToResidual p hcomm _ = complementToResidual p hcomm y
  congr 1
  exact Subtype.ext hz

/-- Conditional residual identification from the concrete homomorphism and its exact kernel and range. -/
def residualEquivOfSubsystem
    (hkernel : ∀ x, f x ∈ Subgroup.center (Elementary F) → x = 1)
    (hcover : (Subgroup.primeToResidual p (Centralizer F)).map
      (Centralizer F).subtype ≤ projectedComplement F) :
    Residual p F ≃* Matrix.symplecticGroup (Fin 3) F :=
  (MulEquiv.ofBijective (symplecticToResidual p f hrange hcomm)
    ⟨symplecticToResidual_injective p f hrange hcomm hkernel,
      symplecticToResidual_surjective p f hrange hcomm hcover⟩).symm

/-- The inverse equivalence follows the literal elementary-group projection. -/
@[simp] theorem residualEquivOfSubsystem_symm_val
    (hkernel : ∀ x, f x ∈ Subgroup.center (Elementary F) → x = 1)
    (hcover : (Subgroup.primeToResidual p (Centralizer F)).map
      (Centralizer F).subtype ≤ projectedComplement F)
    (x : Matrix.symplecticGroup (Fin 3) F) :
    (((residualEquivOfSubsystem p f hrange hcomm hkernel hcover).symm x).val : F4 F) =
      projection typeF4RootPairing typeF4RootPairing_base F (f x) := rfl

/-- Faithfulness and agreement of the two central involutions discharge the
central-kernel condition. The lattice construction and residual upper bound
remain explicit independent inputs. -/
def residualEquivOfFaithfulSubsystem
    (hF : (2 : F) ≠ 0) (hinj : Function.Injective f)
    (hneg : f symplecticNegOne = elementaryHom (-1 : SL(2, F)))
    (hcover : (Subgroup.primeToResidual p (Centralizer F)).map
      (Centralizer F).subtype ≤ projectedComplement F) :
    Residual p F ≃* Matrix.symplecticGroup (Fin 3) F :=
  residualEquivOfSubsystem p f hrange hcomm
    (central_kernel_of_faithful_neg_one hF f hinj hneg) hcover

/-- The same conditional equivalence with the centralizer written literally
as the centralizer of the proved fundamental homomorphism's range. -/
def rangeResidualEquivOfFaithfulSubsystem
    (hF : (2 : F) ≠ 0) (hinj : Function.Injective f)
    (hneg : f symplecticNegOne = elementaryHom (-1 : SL(2, F)))
    (hcover : (Subgroup.primeToResidual p (Centralizer F)).map
      (Centralizer F).subtype ≤ projectedComplement F) :
    Subgroup.primeToResidual p
      (Subgroup.centralizer ((hom (F := F)).range : Set (F4 F))) ≃*
        Matrix.symplecticGroup (Fin 3) F :=
  (Subgroup.primeToResidualEquiv p
    (MulEquiv.subgroupCongr (centralizer_eq_range_centralizer (F := F))).symm).trans
      (residualEquivOfFaithfulSubsystem p f hrange hcomm hF hinj hneg hcover)

end Assembly
end ExceptionalSplit.F4RootCentralizer
end
