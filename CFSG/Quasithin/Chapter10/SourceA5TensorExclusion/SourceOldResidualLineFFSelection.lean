module

public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualLineFFAdequate
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.SourceB5.Complete
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.ProductComponents.FactorModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.RankOneCovers
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SpecialLinearThree
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.AlternatingSmall

/-!
# The adequate FF row selected by a proper local A₅ section

A proper local C-component with two-core quotient A₅ inside an actual
C-component rules out every product row of the adopted B.5.6 classifier.
The residual factors are binary PSL₂, odd-degree PSL₃, or A₅. Proper
full-Sylow overgroups in the rank-one and small alternating models are
solvable; the actual local-section theorem forces field order four in
PSL₃, contradicting odd field degree. The outer A₆–C₃ row is excluded
by the same full-Sylow obstruction in its literal A₆ component.

Thus the selected C-component is precisely the quasisimple generalized
Fitting subgroup, retaining the entire original source action conclusion.
The nonzero-core line argument applies this to the actual old A₅ image
inside the actual offender subgroup. No component-and-Sylow generation
hypothesis or whole-space splitting of the outer row is used.
Source: Aschbacher–Smith, B.5.6, printed p.105, and original 9.3.1.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.SourceOldResidual
open ChapterB.SourceInduction
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings.FiveLocalFF

private theorem local_five_equiv_transport {D E : Type*}
    [Group D] [Finite D] [Group E] [Finite E]
    (a : D ≃* E) (S : Sylow 2 D) (B : Subgroup D)
    (hB : B ∈ localCComponents S) (hp : B ≠ ⊤)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    B.map a.toMonoidHom ∈ localCComponents (S.mapSurjective (f := a.toMonoidHom) a.surjective) ∧
    B.map a.toMonoidHom ≠ ⊤ ∧
    Nonempty (((B.map a.toMonoidHom) ⧸ pCore 2 (B.map a.toMonoidHom)) ≃*
      alternatingGroup (Fin 5)) := by
  let : Group.IsSolvable a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]
    infer_instance
  refine ⟨Chapter1.Section02.localCComponents_map_of_solvable_ker hB a.toMonoidHom, ?_, ?_⟩
  · intro ht
    apply hp
    apply Subgroup.map_injective (f := a.toMonoidHom) a.injective
    rw [ht,map_top_of_surjective _ a.surjective]
  · let b := a.subgroupMap B
    exact ⟨(QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.trans eB⟩

private theorem not_local_five_of_product_model {E : Type*}
    [Group E] [Finite E] [IsQuasisimple E]
    (hm : ProductComponents.ComponentModel E)
    (S : Sylow 2 E) (B : Subgroup E) (hB : B ∈ localCComponents S)
    (hp : B ≠ ⊤) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False := by
  rcases hm with hm | he
  · cases hm with
    | linear_two F n hn hc ha =>
      obtain ⟨a⟩ := ha
      let e := a.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
      have hsolv : SolvableSylowOvergroups E :=
        SolvableSylowOvergroups.of_equiv e
          (fun S M hSM hn => Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup S M hSM hn)
      have ht : (⊤ : Subgroup E).IsCComponent :=
        (show IsComponent E ⊤ from ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
      exact hp (SourceEmbeddings.eq_of_solvable_sylow_overgroups S hB ht le_top
        (SolvableSylowOvergroups.of_equiv topEquiv hsolv))
    | linear_three F n hn ho hc ha =>
      obtain ⟨a⟩ := ha
      let e := a.trans
        (Matrix.PSL3.OddDegreeProjectiveComparison.specialProjectiveEquiv hc ho).symm
      obtain ⟨hl,hproper,⟨eb⟩⟩ := local_five_equiv_transport e S B hB hp eB
      have hfour := (special_linear_three_five_section_placement_all hc _ _ hl hproper eb).1
      have hpow : 2 ^ n = 2 ^ 2 := hc.symm.trans hfour
      have hn2 : n = 2 := (Nat.pow_right_injective (by decide : 2 ≤ 2)) hpow
      exact (by decide : ¬ Odd (2 : ℕ)) (hn2 ▸ ho)
  · exact AlternatingSmall.not_proper_five S B hB hp he.some

private theorem component_model_of_product {D A B : Type*}
    [Group D] [Group A] [Finite A] [Group B] [Finite B]
    (e : D ≃* A × B) (hA : FFAlternatives.FactorModel A)
    (hB : FFAlternatives.FactorModel B)
    {C : Subgroup D} (hC : C.IsCComponent) : ProductComponents.ComponentModel C := by
  have ha := ProductComponents.factor_residual hA
  have hb := ProductComponents.factor_residual hB
  have hra : solvableResidual A = ⊥ ∨ IsQuasisimple (solvableResidual A) :=
    ha.elim (fun h => Or.inl h.2) (fun h => Or.inr h.1)
  have hrb : solvableResidual B = ⊥ ∨ IsQuasisimple (solvableResidual B) :=
    hb.elim (fun h => Or.inl h.2) (fun h => Or.inr h.1)
  have heC := hC.map_equiv e
  rcases cComponent_eq_residual_factor hra hrb heC with he | he
  · rcases ha with ⟨_,hz⟩ | ⟨_,hm⟩
    · exact (heC.ne_bot (by simpa only [hz,bot_prod_bot] using he)).elim
    · exact hm.of_equiv
        (((e.subgroupMap C).trans (MulEquiv.subgroupCongr he)).trans residualLeftEquiv)
  · rcases hb with ⟨_,hz⟩ | ⟨_,hm⟩
    · exact (heC.ne_bot (by simpa only [hz,bot_prod_bot] using he)).elim
    · exact hm.of_equiv
        (((e.subgroupMap C).trans (MulEquiv.subgroupCongr he)).trans residualRightEquiv)

variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {C : Subgroup D}

private theorem twoFactors_component_model (c : SourceTwoFactorCase ρ)
    (hC : C.IsCComponent) : ProductComponents.ComponentModel C := by
  let d := FFAlternatives.SourceB5.pair c
  exact component_model_of_product d.product.equiv.symm
    (d.firstCase.factorModel ρ) (d.secondCase.factorModel ρ) hC

private theorem hyperplane_component_model (c : HyperplaneCase ρ)
    (hC : C.IsCComponent) : ProductComponents.ComponentModel C := by
  let d := FFAlternatives.SourceB5.hyperplane c
  exact component_model_of_product d.product.equiv.symm
    (.linearThree FFAlternatives.BinaryField.two (by decide) d.firstEquiv)
    (d.secondCase.factorModel ρ) hC

/-- A proper full-Sylow local A₅ section inside the original C-component
selects the quasisimple B.5.6 row and all of its original module conclusions. -/
theorem quasisimple_source_of_adequate_of_proper_local_five
    (h : AdequateAlternative ρ) (hC : C.IsCComponent)
    (S : Sylow 2 C) (B : Subgroup C) (hB : B ∈ localCComponents S)
    (hp : B ≠ ⊤) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    C = generalizedFitting D ∧ Nonempty (ProjectiveLine.QuasisimpleSourceConclusion ρ C) := by
  let : IsQuasisimple C := cComponent_quasisimple_of_adequate h hC
  have hc : IsComponent D C := ⟨hC.subnormal,inferInstance⟩
  rcases h with ht | h
  · let := ht
    exact (hC.ne_bot (Subsingleton.elim _ _)).elim
  cases h with
  | quasisimple hq ha =>
    have hf : IsComponent D (generalizedFitting D) :=
      ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal,hq⟩
    have he : C = generalizedFitting D :=
      hc.eq_of_le hf (component_le_generalizedFitting D C hc)
    exact ⟨he,he.symm ▸ ⟨ha⟩⟩
  | symmetricThree c =>
    let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
      apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
      rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
    let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective
      (f := c.equiv.toMonoidHom) c.equiv.injective
    exact (hC.not_isSolvable inferInstance).elim
  | twoFactors c =>
    exact (not_local_five_of_product_model (twoFactors_component_model c hC) S B hB hp eB).elim
  | outerSixThree c =>
    let := c.first_normal
    let := c.quotient_first_solvable
    have he : C = c.first := hC.eq_of_le c.first_isComponent.isCComponent
      (le_of_isPerfect_of_solvable_quotient C c.first)
    exact (AlternatingSmall.not_proper_six S B hB hp
      ((MulEquiv.subgroupCongr he).trans c.firstEquiv)).elim
  | hyperplane c =>
    exact (not_local_five_of_product_model (hyperplane_component_model c hC) S B hB hp eB).elim

end CFSG.Quasithin.Chapter10.SourceOldResidual
