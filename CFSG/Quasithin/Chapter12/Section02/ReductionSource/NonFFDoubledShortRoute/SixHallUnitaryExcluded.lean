module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SixHallUnitarySource
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.Flag.SixSections
public import Theory.GroupTheory.SylowOuterSectionImages

/-!
# Excluding the actual unitary-five Hall component for A₆

The literal Sylow calculation excludes an actual A₆ section of the full
outer group. Descent through the entire component center retains the original
cover. The original Hall source forces precisely this outer section whenever
its selected component is PSU₅(4), so that complete family is excluded without
an inner-action or residual-placement premise.
Source: Aschbacher--Smith 4.4.10--12 and 12.1.9,
printed pp.621--622 and 793, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter4 Chapter4.Section04
open Theory.SpecificGroups

private theorem no_unitary_five_six_outer
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hm : ClassicalGroup.IsPSU Q 5 4)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* alternatingGroup (Fin 6))
    (hf : Function.Surjective f) : False := by
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
  let : CharP F 2 := UnitaryFive.charP_two_of_card_sixteen hF
  obtain ⟨a⟩ := UnitaryFive.projective_equiv_identity_four J hF hconj
  let P : Sylow 2 Q := default
  let : Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  obtain ⟨B,q,hq⟩ := MulAut.simple_outer_section_in_sylow_aut P
    (Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 6))) U f hf
  exact UnitaryFive.Flag.SixSections.no_six_section_sylow_of_equiv
    (BenderSuzuki.MatrixGroups.HermitianForm.IdentityGram.identityGram J)
    rfl hF hconj (e.trans a) P B q hq

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The selected original Hall component cannot have PSU₅(4) as its full
central quotient. Both actual inner and outer alternatives are discharged. -/
theorem sourceOrbit_six_oddNormalizer_not_unitary_five
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G)) :
    ¬ ClassicalGroup.IsPSU (K ⧸ center K) 5 4 := by
  intro hm
  obtain ⟨U,f,hf⟩ := D.sourceOrbit_six_oddNormalizer_unitary_five_outer
    h hd hmodel A hne hAC ho hout K hK houtK hm
  let := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let a := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  exact no_unitary_five_six_outer hm (U.map j) (f.comp a.symm.toMonoidHom)
    (hf.comp a.symm.surjective)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
