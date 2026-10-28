module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Normal
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Inputs
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.Held.LocalPair
public import Theory.SpecificGroups.Held.RankOneLocalPair.Maximal
public import Theory.SpecificGroups.Held.RankOneLocalPair.Solvable
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure.Application

/-!
# Generation one for the retained Held row

The actual local pair in every inner overgroup of Aut(He) is now
constructed using the completed permutation realization. Its maximal
member has a normal PSL₃(2) in its literal two-core quotient; this is the
simple generalized Fitting subgroup, supplemented by the image of the
original full Sylow. The PSL₃ generation theorem and two-core lifting give
the local bound, while the other member is solvable. The pair generates.

For the original invariant C-component, the quasisimplicity hypothesis
and the proved trivial center of the concrete Held carrier supply
simplicity; no separate Held simplicity or order certification is required.

Source: Aschbacher--Smith E.1.12--14, p.214, and the corrected intrinsic
1.3.4 row retained in the 10.3.3 calculation, pp.756--757. The imported
concrete realization and local pair retain their ATLAS source attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration
open ChapterE ChapterE.ValuesEvenClassical Held.RankOneLocalPair
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

theorem isEGenerated_of_held_local_section (hH : IsSQTK κ H)
    (hm : HasPSL3TwoCoreQuotient H) : IsEGenerated 1 H := by
  obtain ⟨J, hn, ⟨e⟩, htwo⟩ := hm
  let := hn
  let : IsSimpleGroup (BinaryUpper.PSL 3) := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup J := e.isSimpleGroup
  let : Group.IsPerfect (BinaryLinear.OuterCyclic.LinearGroup 3) :=
    BinaryLinear.linearGroup_isPerfect 3 (by decide)
  let a := BinaryLinear.SmallParabolicLevi.linearThreeEquivProjective
  let : Group.IsPerfect (BinaryUpper.PSL 3) :=
    Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  let : Group.IsPerfect J := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hF := (simple_two_quotient_structure J (Group.IsPerfect.not_isMulCommutative J)
    htwo (pCore_quotient_pCore_eq_bot 2)).1
  let eg := (MulEquiv.subgroupCongr hF).trans e
  let S : Sylow 2 (H ⧸ pCore 2 H) := Classical.choice inferInstance
  apply isEGenerated_of_binary_middle_section hH
  refine ⟨pCore 2 H, inferInstance, pCore_isPGroup, eg.isSimpleGroup, ⟨eg⟩, S, ?_⟩
  rw [hF, sup_comm]
  exact S.sup_eq_top_of_quotient_isPGroup J htwo

theorem isEGenerated_of_held_local_overgroups
    (hmax : MaximalOvergroups) (hsol : SolvableOvergroups)
    (hH : IsSQTK κ H) [IsSimpleGroup (generalizedFitting H)]
    (S : Sylow 2 H) (e : generalizedFitting H ≃* Held.He)
    (hgen : generalizedFitting H ⊔ (S : Subgroup H) = ⊤) : IsEGenerated 1 H := by
  obtain ⟨P, B, hpair⟩ := exists_of_automorphism_overgroups
    hmax hsol e S hgen
  obtain ⟨hcover, hlocal⟩ := held_generatingFamily_of_local_pair S P B hpair
    (isEGenerated_of_held_local_section (hH.subgroup P) hpair.quotient)
  apply IsEGeneratedAt.isEGenerated (T := S)
  intro Ω hΩ
  apply top_unique
  change ⊤ ≤ ChiefOrbit.generationTarget 1 S Ω
  rw [← hcover]
  exact sSup_le fun P hP => ChiefOrbit.overgroup_le_generationTarget S P
    (hlocal P hP).1 hΩ (hlocal P hP).2

theorem invariantHeldGeneration_of_local_overgroups
    (hmax : MaximalOvergroups) (hsol : SolvableOvergroups) :
    InvariantHeldGeneration.{u} := by
  intro H _ _ hH S K hK hn hq hgen he
  obtain ⟨e⟩ := he
  let := hn
  let := hq
  let : IsQuasisimple Held.He := IsQuasisimple.of_mulEquiv e
  let : IsSimpleGroup (Held.He ⧸ center Held.He) := IsQuasisimple.simple
  let z : (Held.He ⧸ center Held.He) ≃* Held.He :=
    (QuotientGroup.quotientMulEquivOfEq Held.LocalPairs.center_eq_bot).trans QuotientGroup.quotientBot
  let : IsSimpleGroup Held.He := z.symm.isSimpleGroup
  let : IsSimpleGroup (K ⧸ pCore 2 K) := e.isSimpleGroup
  obtain ⟨hsF, ⟨a⟩, hFS⟩ := normal_component_quotient_structure S K hK hgen
  let := hsF
  apply IsEGenerated.of_normal_two_subgroup (pCore 2 H) pCore_isPGroup
  exact isEGenerated_of_held_local_overgroups hmax hsol
    (sqtk_quotient_of_two_kernel hH _ pCore_isPGroup)
    (S.mapSurjective (QuotientGroup.mk'_surjective _)) (a.trans e) hFS

theorem invariantHeldGeneration_of_realization
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom) :
    InvariantHeldGeneration.{u} :=
  invariantHeldGeneration_of_local_overgroups
    (maximalOvergroups_of_realization hreal) (solvableOvergroups_of_realization hreal)

/-- The actual Held branch, with all local constructions discharged. -/
theorem invariantHeldGeneration : InvariantHeldGeneration.{u} :=
  invariantHeldGeneration_of_realization Held.Realization.normalizer_surjective

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration
