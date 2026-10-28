module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Inputs

/-!
# The two remaining steps of the parabolic catalogue comparison

Both contracts use the recomputed first parabolic of the literal generated
group. The first excludes the two larger linear star models; the second
recovers the full A₇ quotient above its star marking. A central quotient
alone does not supply the latter, since A₇ has a genuine triple cover.
These are independent proof obligations, not additional source hypotheses.

Source: Aschbacher--Smith original 14.6.10(5), p.1029, comparing
C.2.7(3) with F.6.18.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

/-- The two-core of the first parabolic recomputed inside the generated group. -/
noncomputable def firstCore (T : Sylow 2 G) (M Mc I H2 : Subgroup G) : Subgroup G :=
  let I0 := sourceGeneratedParabolic T M Mc I H2
  ((pResidual 2 (sourceResidual M Mc ⊓ I0 : Subgroup G)).map
    (sourceResidual M Mc ⊓ I0).subtype ⊔ ((T : Subgroup G) ⊓ I0)).pCoreIn 2

/-- The literal C.2.7 star image of the generated residual component. -/
noncomputable abbrev star (T : Sylow 2 G) (M Mc I H2 : Subgroup G) :=
  starImage (sourceGeneratedComponent T M Mc I H2) (firstCore T M Mc I H2)
    (sourceGeneratedComponent T M Mc I H2)

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- The two higher linear star rows are excluded on the original generated group. -/
def LinearExclusionInput : Prop :=
  ∀ (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G),
    I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M) →
    (∀ F : BinaryField, F.degree = 2 →
      ¬ Nonempty (star T M Mc I d.H2 ≃* SL(3,F.Carrier))) ∧
    ¬ Nonempty (star T M Mc I d.H2 ≃* SL(4,ZMod 2))

/-- The actual A₇ marking loses no kernel above the two-core. This must be
proved from the source configuration, not from an abstract central cover. -/
def SevenRecoveryInput : Prop :=
  ∀ (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G),
    I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M) →
    Nonempty (star T M Mc I d.H2 ≃* alternatingGroup (Fin 7)) →
    Nonempty (((sourceGeneratedComponent T M Mc I d.H2) ⧸
      pCore 2 (sourceGeneratedComponent T M Mc I d.H2)) ≃* alternatingGroup (Fin 7))

end CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue
