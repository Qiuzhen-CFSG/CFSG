module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.Classification.Carriers
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.GroupCore

/-!
# Selected components of a perfect FF actor

A C-component equals a quasisimple generalized Fitting subgroup: component
commutation and the self-centralizing property of F* exclude any other one.
In a direct product, the actual projections of a perfect actor are perfect,
and every C-component is an embedded quasisimple residual factor. The
solvable and outer A₆ × C₃ alternatives have nontrivial abelian quotients,
so cannot occur for a perfect actor.

This exhausts all cases of the complete `SourceAlternative`, including the
repeated-natural, indecomposable and hyperplane possibilities. Their group
identifications are extracted from their genuine action data. The selected
C-component is not assumed ordinary or assigned a model in advance.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1 and
B.5.6, printed pp.99–105; component generation in 15.3.49(i) and its use
at the start of (k), printed pp.1143–1144.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.Classification
universe u v w
variable {D : Type u} [Group D]

private theorem classification_of_equiv {E : Type*} [Group E] (e : D ≃* E)
    (h : IsQuasisimple E ∧ ComponentModel E) : IsQuasisimple D ∧ ComponentModel D := by
  let := h.1
  exact ⟨IsQuasisimple.of_mulEquiv e.symm, componentModel_of_equiv e h.2⟩

/-- A C-component of a group with quasisimple F* is that F* itself. -/
private theorem cComponent_eq_generalizedFitting [Finite D]
    (hq : IsQuasisimple (generalizedFitting D)) {C : Subgroup D}
    (hC : C.IsCComponent) : C = generalizedFitting D := by
  have hf : IsComponent D (generalizedFitting D) :=
    ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal, hq⟩
  rcases hf.subnormal_dichotomy C hC.subnormal with hle | hcomm
  · exact (hf.isCComponent.eq_of_le hC hle).symm
  · rw [commutator_comm, commutator_eq_bot_iff_le_centralizer] at hcomm
    exact hC.eq_of_le hf.isCComponent
      (hcomm.trans CFSG.Quasithin.ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le)

/-- The actual projections of a perfect product are perfect. Each selected
C-component is one of the two embedded quasisimple residuals. -/
theorem component_classification_of_product [Group.IsPerfect D]
    {E : Type v} [Group E] [Finite E] {F : Type w} [Group F] [Finite F]
    (e : D ≃* E × F) (hE : FactorModel E) (hF : FactorModel F)
    {C : Subgroup D} (hC : C.IsCComponent) : IsQuasisimple C ∧ ComponentModel C := by
  let : Group.IsPerfect E := Group.IsPerfect.ofSurjective
    (f := (MonoidHom.fst E F).comp e.toMonoidHom) (Prod.fst_surjective.comp e.surjective)
  let : Group.IsPerfect F := Group.IsPerfect.ofSurjective
    (f := (MonoidHom.snd E F).comp e.toMonoidHom) (Prod.snd_surjective.comp e.surjective)
  have he := factor_classification hE
  have hf := factor_classification hF
  let eE : solvableResidual E ≃* E :=
    (MulEquiv.subgroupCongr solvableResidual_eq_top).trans topEquiv
  let eF : solvableResidual F ≃* F :=
    (MulEquiv.subgroupCongr solvableResidual_eq_top).trans topEquiv
  let := he.1
  let := hf.1
  have hrE : IsQuasisimple (solvableResidual E) := IsQuasisimple.of_mulEquiv eE.symm
  have hrF : IsQuasisimple (solvableResidual F) := IsQuasisimple.of_mulEquiv eF.symm
  rcases cComponent_eq_residual_factor (Or.inr hrE) (Or.inr hrF) (hC.map_equiv e) with h | h
  · exact classification_of_equiv
      (((e.subgroupMap C).trans (MulEquiv.subgroupCongr h)).trans
        (residualLeftEquiv.trans eE)) he
  · exact classification_of_equiv
      (((e.subgroupMap C).trans (MulEquiv.subgroupCongr h)).trans
        (residualRightEquiv.trans eF)) hf

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- A perfect actor cannot be the outer A₆ × C₃ alternative. Its cyclic
quotient would be trivial, leaving a nontrivial abelian image C₃. -/
theorem outerSixThree_not_perfect [Group.IsPerfect D] (c : OuterSixThreeCase ρ) : False := by
  let := c.product_normal ρ
  let := c.quotient_isCyclic ρ
  let : CommGroup (D ⧸ (c.first ⊔ c.second)) := IsCyclic.commGroup
  have ht : c.first ⊔ c.second = ⊤ := by
    apply top_unique
    intro x _
    exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
  let e : D ≃* c.first × c.second :=
    topEquiv.symm.trans ((MulEquiv.subgroupCongr ht.symm).trans c.product.symm)
  let f : D →* Multiplicative (ZMod 3) :=
    c.secondEquiv.toMonoidHom.comp ((MonoidHom.snd c.first c.second).comp e.toMonoidHom)
  let : Group.IsPerfect (Multiplicative (ZMod 3)) :=
    Group.IsPerfect.ofSurjective (f := f)
      (c.secondEquiv.surjective.comp (Prod.snd_surjective.comp e.surjective))
  exact Group.IsPerfect.not_isMulCommutative (Multiplicative (ZMod 3)) inferInstance

/-- Exhaust the full representation alternatives on a perfect actor. No
quasisimplicity or carrier identification of the selected component is assumed. -/
theorem component_classification_of_source_alternative [Finite D] [Group.IsPerfect D]
    (h : SourceAlternative ρ) {C : Subgroup D} (hC : C.IsCComponent) :
    IsQuasisimple C ∧ ComponentModel C := by
  cases h with
  | trivial h =>
    let := h
    exact (hC.ne_bot (Subsingleton.elim _ _)).elim
  | quasisimple hq actions =>
    have he := cComponent_eq_generalizedFitting hq hC
    rw [he]
    let := hq
    exact ⟨hq, componentModel_of_quasisimpleModel (actions.fittingModel ρ)⟩
  | symmetricThree c =>
    let : Group.IsPerfect (Equiv.Perm (Fin 3)) :=
      Group.IsPerfect.ofSurjective (f := c.equiv.toMonoidHom) c.equiv.surjective
    let : Group.IsPerfect ℤˣ := Group.IsPerfect.ofSurjective (Equiv.Perm.sign_surjective (Fin 3))
    exact ((by decide : (1 : ℤˣ) ≠ -1) (Subsingleton.elim _ _)).elim
  | twoFactors c =>
    exact component_classification_of_product c.product.equiv.symm
      (c.firstCase.factorModel ρ) (c.secondCase.factorModel ρ) hC
  | outerSixThree c => exact (outerSixThree_not_perfect ρ c).elim
  | hyperplane c =>
    exact component_classification_of_product c.product.equiv.symm
      (.linearThree BinaryField.two (by decide) c.firstEquiv)
      (c.secondCase.factorModel ρ) hC

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.Classification
