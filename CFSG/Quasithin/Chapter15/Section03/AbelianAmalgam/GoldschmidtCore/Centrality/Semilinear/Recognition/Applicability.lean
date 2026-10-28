module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.OffenderReduction
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.SourceAlternatives
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import CFSG.Quasithin.ChapterF.Section06.Basic
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import Theory.GroupTheory.QuotientIntersection

/-!
# Applying the source classifications to the actual offender subgroup

A subgroup of a quotient of an SQTK group has a genuine SQTK cover: its
full preimage in the original group. Restriction to the offender-generated
subgroup supplies every action hypothesis of B.5.3. Nontriviality is proved
from a subgroup whose quotient image is nonzero; it is not imposed on every
instance of the universal B.5.6 implication.

When the generalized Fitting subgroup of the quotient is quasisimple, an
actual best offender generates it by commutation. Normality of the offender
subgroup then puts the component inside it. This excludes solvable offender
actors without identifying them with the ordinary Thompson subgroup.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.3 and
B.5.6, pp.104–105, F.6.1/F.6.18, pp.304 and 309–310, and the repaired
15.3.68 argument on pp.1154–1155. The universal classifications remain inputs.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u v
variable {H D : Type u} [Group H] [Group D] [Finite H] [Finite D]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]

/-- The full inverse image gives the source quotient witness, with its actual
first-isomorphism-theorem map. No SQTK inheritance by arbitrary quotients is used. -/
noncomputable def subgroupSQTKQuotient {K : GroupClass.{u}} (hH : IsSQTK K H)
    (q : H →* D) (hq : Function.Surjective q) (I : Subgroup D) : SQTKQuotient K I where
  Cover := I.comap q
  kernel := (q.subgroupComap I).ker
  sqtk := hH.subgroup _
  equiv := QuotientGroup.quotientKerEquivOfSurjective _
    (q.subgroupComap_surjective_of_surjective I hq)

/-- All of B.5.3 applies to the actual restricted offender action. -/
theorem offender_source_hypothesis {K : GroupClass.{u}} (hH : IsSQTK K H)
    (q : H →* D) (hq : Function.Surjective q) (hcore : pCore 2 D = ⊥)
    (ρ : Representation (ZMod 2) D W) [Module.Finite (ZMod 2) W]
    (hfaith : Function.Injective ρ) :
    FFHypothesis K (ρ.comp (offenderSubgroup ρ).subtype) where
  finite_module := inferInstance
  faithful := offenderSubgroup_restriction_faithful ρ hfaith
  twoCore := offenderSubgroup_twoCore ρ hcore
  generated := offenderSubgroup_restriction ρ
  quotient := ⟨subgroupSQTKQuotient hH q hq _⟩

/-- Apply the complete, universal B.5.6 premise, preserving every module clause
and every alternative, to the actual offender subgroup. -/
theorem offender_source_alternative {K : GroupClass.{u}}
    (source : GeneralClassificationInput.{u,v} K) (hH : IsSQTK K H)
    (q : H →* D) (hq : Function.Surjective q) (hcore : pCore 2 D = ⊥)
    (ρ : Representation (ZMod 2) D W) [Module.Finite (ZMod 2) W]
    (hfaith : Function.Injective ρ) : SourceAlternative (ρ.comp (offenderSubgroup ρ).subtype) :=
  source _ _ _ (offender_source_hypothesis hH q hq hcore ρ hfaith)

omit [Finite H] [Finite D] in
/-- An image escaping the kernel makes the actual offender subgroup nontrivial. -/
theorem offender_ne_bot_of_image (q : H →* D) (X : Subgroup H)
    (ρ : Representation (ZMod 2) D W) (hX : ¬ X ≤ q.ker)
    (hXI : X.map q ≤ offenderSubgroup ρ) : offenderSubgroup ρ ≠ ⊥ := by
  intro hi
  apply hX
  exact (Subgroup.map_eq_bot_iff X).mp (le_bot_iff.mp (hi ▸ hXI))

omit [Finite D] in
/-- A nontrivial offender-generated subgroup has an actual generating best offender. -/
theorem exists_bestOffender_of_generated_ne_bot
    (ρ : Representation (ZMod 2) D W) (hne : offenderSubgroup ρ ≠ ⊥) :
    ∃ A, IsBestOffender ρ A := by
  by_contra hn
  apply hne
  apply le_bot_iff.mp
  refine iSup_le fun A => iSup_le fun hA => ?_
  exact (hn ⟨A, hA.1⟩).elim

/-- The component lies in the actual offender subgroup, using a nontrivial
best offender and the generalized-Fitting commutator theorem. -/
theorem fitting_le_offender (ρ : Representation (ZMod 2) D W)
    (hne : offenderSubgroup ρ ≠ ⊥) (hcore : pCore 2 D = ⊥)
    (hL : IsQuasisimple (generalizedFitting D)) :
    generalizedFitting D ≤ offenderSubgroup ρ := by
  obtain ⟨A, hA⟩ := exists_bestOffender_of_generated_ne_bot ρ hne
  let : IsElementaryAbelian 2 A := hA.1.2
  let : (offenderSubgroup ρ).Normal := offenderSubgroup_normal ρ
  rw [← ChapterB.QuasisimpleSections.commutator_fitting_eq hcore hL hA.1.1
    (IsElementaryAbelian.isPGroup 2 A)]
  exact (commutator_mono le_rfl (bestOffender_le_generated ρ hA)).trans
    (commutator_le_right _ _)

/-- In the quasisimple F.6.18 rows the offender actor is not solvable;
in particular the B.5.6 symmetric-three case cannot occur. -/
theorem offender_not_solvable (ρ : Representation (ZMod 2) D W)
    (hne : offenderSubgroup ρ ≠ ⊥) (hcore : pCore 2 D = ⊥)
    (hL : IsQuasisimple (generalizedFitting D)) :
    ¬ Group.IsSolvable (offenderSubgroup ρ) := by
  intro hs
  let : Group.IsSolvable (offenderSubgroup ρ) := hs
  let : IsQuasisimple (generalizedFitting D) := hL
  let : IsSimpleGroup ((generalizedFitting D) ⧸ center (generalizedFitting D)) := hL.simple
  let : Nontrivial (generalizedFitting D) :=
    (QuotientGroup.mk'_surjective (center (generalizedFitting D))).nontrivial
  have : Group.IsSolvable (generalizedFitting D) :=
    Group.isSolvable_of_isSolvable_injective
      (inclusion_injective (fitting_le_offender ρ hne hcore hL))
  exact Group.IsPerfect.not_isSolvable (generalizedFitting D) this

/-- Goldschmidt triples descend through two-group kernels contained in the
common Sylow. The local quotient equivalences and the intersection are transported. -/
theorem goldschmidt_map (q : H →* D) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (A B : Subgroup H)
    (c : ChapterF.IsGoldschmidtTriple A B) (hkAB : q.ker ≤ A ⊓ B) :
    ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) := by
  have hlocal (C : Subgroup H)
      (hc : Nonempty ((C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 3))) :
      Nonempty (((C.map q) ⧸ pCore 2 (C.map q)) ≃* Equiv.Perm (Fin 3)) := by
    have hkC : IsPGroup 2 (q.subgroupMap C).ker := by
      rw [Subgroup.ker_subgroupMap]
      exact hk.comap_subtype
    exact ⟨((q.subgroupMap C).quotientPCoreEquivOfSurjective
      (q.subgroupMap_surjective C) hkC).symm.trans hc.some⟩
  refine ⟨?_, hlocal A c.quotient_left, hlocal B c.quotient_right, ?_⟩
  · rw [← Subgroup.map_sup, c.generated, map_top_of_surjective q hq]
  · obtain ⟨S, hS⟩ := c.intersection_sylow
    refine ⟨S.mapSurjective hq, ?_⟩
    rw [← map_inf_of_ker_le q A B (hkAB.trans inf_le_right), hS]
    rfl

/-- The actual two-core quotient carries the descended source triple. -/
theorem goldschmidt_twoCore_quotient (A B : Subgroup H)
    (c : ChapterF.IsGoldschmidtTriple A B) :
    ChapterF.IsGoldschmidtTriple (A.map (QuotientGroup.mk' (pCore 2 H)))
      (B.map (QuotientGroup.mk' (pCore 2 H))) := by
  apply goldschmidt_map _ (QuotientGroup.mk'_surjective _)
  · rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  · exact c
  · rw [QuotientGroup.ker_mk']; exact c.twoCore_isGreatest.1.1

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
