module
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.Flag.Automorphisms
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerFourOuterG2

/-!
# Excluding the final degree-four unitary outer section

The literal PSU₅(4) Sylow automorphism group has order prime to seven,
whereas A₈ has order divisible by seven. Sylow restriction with its solvable
pointwise kernel preserves a nonsolvable simple outer section. This excludes
the original unitary section after descent through the entire center of
the original perfect component.

The chosen-orbit application in `DoubleNaturalExcludedFourOddNormalizers`
therefore leaves only the constrained SL₅(2) star. No full Schreier theorem
or replacement component is assumed. Source: Aschbacher--Smith 4.4.10--11
and 12.1.9, printed pp.621,793.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.FourOuterModels
open Theory.SpecificGroups

/-- Fourth-power fibers in the actual unitary Sylow group exclude the A₈
outer section. -/
theorem unitary_five_four
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hm : ClassicalGroup.IsPSU Q 5 4)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* alternatingGroup (Fin 8)) :
    ¬ Function.Surjective f := by
  intro hf
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
  let : CharP F 2 := UnitaryFive.charP_two_of_card_sixteen hF
  obtain ⟨a⟩ := UnitaryFive.projective_equiv_identity_four J hF hconj
  let P : Sylow 2 Q := default
  let : Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  have hd := MulAut.simple_outer_section_card_dvd_sylow_aut P
    (Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 8))) U f hf
  apply UnitaryFive.Flag.Automorphisms.not_seven_dvd_sylow_aut_of_equiv
    (BenderSuzuki.MatrixGroups.HermitianForm.IdentityGram.identityGram J)
    hF hconj rfl (e.trans a) P
  apply dvd_trans ?_ hd
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- The unitary exclusion descends through the entire original component center. -/
theorem unitary_five_four_cover_exclusion
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* alternatingGroup (Fin 8),
      Function.Surjective f) : ¬ ClassicalGroup.IsPSU (K ⧸ center K) 5 4 := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  obtain ⟨U,f,hf⟩ := ho
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let a := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  intro hm
  exact unitary_five_four hm _ (f.comp a.symm.toMonoidHom)
    (hf.comp a.symm.surjective)

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.FourOuterModels

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
open BinaryLinear.OuterCyclic

/-- The final two-family outer inspection is impossible for the original
perfect component and its full quotient action. -/
theorem four_lie_outer_model_exclusion
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hm : FourLieOuterModel (K ⧸ center K))
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* LinearGroup 4,
      Function.Surjective f) : False := by
  have hu := four_outer_model_unitary_five hm ho
  obtain ⟨U,f,hf⟩ := ho
  let a := Chapter12.Section02.ChosenModule.doubledFour_linearEquiv
  exact FourOuterModels.unitary_five_four_cover_exclusion
    ⟨U,a.toMonoidHom.comp f,a.surjective.comp hf⟩ hu

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
