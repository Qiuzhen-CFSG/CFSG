module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.SeedSpace

/-!
# The faithful local quotient and pending comparison targets

The seed U has only an LA-action. Its literal kernel quotient remains in
the universe of the original group, and the descended action is proved
faithful. `Prepared` records the further outputs required to apply the full
earlier B.5.1 theorem; `LocalAlternative` records the five local comparisons
on U, before any use of U=W or the non-IV projection argument.

Neither record is an earlier-source assumption or a classification theorem.
Their producers must establish them from B.5.3 and the permitted full earlier
source implications. In particular, no reduced component list is assumed.
The natural branch already constructs the literal requested `NaturalSeed`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.9, printed p.107, through cases (I)–(V).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
open QuasisimpleSource
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The action of the original L on U, using its specified inclusion in LA. -/
noncomputable def seedComponentAction {A L : Subgroup G} (hLA : ⁅L,A⁆ = L) :=
  (seedSubrepresentation ρ hLA).toRepresentation.comp
    (Subgroup.inclusion (show L ≤ L ⊔ A from le_sup_left))

/-- The actual quotient LA/C_LA(U); it stays in the universe of G. -/
abbrev SeedQuotient {A L : Subgroup G} (hLA : ⁅L,A⁆ = L) :=
  (L ⊔ A : Subgroup G) ⧸ (seedSubrepresentation ρ hLA).toRepresentation.ker

noncomputable def seedQuotientMap {A L : Subgroup G} (hLA : ⁅L,A⁆ = L) :
    (L ⊔ A : Subgroup G) →* SeedQuotient ρ hLA :=
  QuotientGroup.mk' (seedSubrepresentation ρ hLA).toRepresentation.ker

/-- The faithful action on U descended along its actual kernel. -/
noncomputable def seedQuotientAction {A L : Subgroup G} (hLA : ⁅L,A⁆ = L) :=
  quotientOfLEKer (seedSubrepresentation ρ hLA).toRepresentation
    (seedSubrepresentation ρ hLA).toRepresentation.ker le_rfl

@[simp] theorem seedQuotientAction_apply {A L : Subgroup G} (hLA : ⁅L,A⁆ = L)
    (g : (L ⊔ A : Subgroup G)) :
    seedQuotientAction ρ hLA (seedQuotientMap ρ hLA g) =
      (seedSubrepresentation ρ hLA).toRepresentation g := rfl

/-- Factoring by precisely C_LA(U), rather than by a guessed normal subgroup,
makes the descended representation faithful. -/
theorem seedQuotientAction_faithful {A L : Subgroup G} (hLA : ⁅L,A⁆ = L) :
    Function.Injective (seedQuotientAction ρ hLA) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro q hq
  obtain ⟨g,rfl⟩ := (QuotientGroup.mk'_surjective
    (seedSubrepresentation ρ hLA).toRepresentation.ker) q
  exact (QuotientGroup.eq_one_iff _).mpr hq

noncomputable def seedComponentImage {A L : Subgroup G} (hLA : ⁅L,A⁆ = L) :
    Subgroup (SeedQuotient ρ hLA) :=
  (L.subgroupOf (L ⊔ A)).map (seedQuotientMap ρ hLA)

noncomputable def seedOffenderImage {A L : Subgroup G} (hLA : ⁅L,A⁆ = L) :
    Subgroup (SeedQuotient ρ hLA) :=
  (A.subgroupOf (L ⊔ A)).map (seedQuotientMap ρ hLA)

/-- Preparation target for applying the complete earlier B.5.1 theorem.
These are outputs to prove from B.5.3 and full earlier B.5.2/B.5.5 inputs;
this record is not an earlier theorem or an assumption of B.5.9. -/
structure Prepared (K : GroupClass.{u}) [Finite G]
    {A L : Subgroup G} (hLA : ⁅L,A⁆ = L) : Prop where
  component_normal : L.Normal
  component_faithful : Function.Injective (seedComponentAction ρ hLA)
  centralizer_eq : subspaceKernel ρ (naturalSeedSpace ρ L A) A =
    A ⊓ centralizer (L : Set G)
  noncentral : subspaceCommutator ρ (naturalSeedSpace ρ L A) A ≠ ⊥
  minimal : IsMinimalBestOffender (seedQuotientAction ρ hLA) (seedOffenderImage ρ hLA)
  source : QuasisimpleSourceHypothesis (seedQuotientAction ρ hLA) K
    (seedComponentImage ρ hLA)

/-- The literal image-rank equality consumed by `seed_equality_of_image_rank`.
It is the non-IV conclusion of the local representation comparison. -/
def SeedRankEquality (A L : Subgroup G) : Prop :=
  rank (restrictedSubgroup ρ (naturalSeedSpace ρ L A) A) =
    fixedCodim (subspaceImageRepresentation ρ (naturalSeedSpace ρ L A))
      (restrictedSubgroup ρ (naturalSeedSpace ρ L A) A)

/-- Outputs of the local representation comparison, before U=W and A≤L.
Every representation is on U or its literal central quotient; the offender
orders and Sylow data concern the actual quotient image. The original task
owns transport to W and final assembly of `PreliminaryConclusion`. -/
inductive LocalAlternative {A L : Subgroup G} (hLA : ⁅L,A⁆ = L) : Prop
  | linearTwo (F : BinaryField)
      (natural : IsLinearNatural (reducedAction (seedComponentAction ρ hLA)) F 2)
      (irrPlus : IsIrrPlus ρ L (naturalSeedSpace ρ L A))
      (sylow : ∃ T : Sylow 2 (seedComponentImage ρ hLA),
        seedOffenderImage ρ hLA = (T : Subgroup (seedComponentImage ρ hLA)).map
          (seedComponentImage ρ hLA).subtype)
      (inner : InducesInner A L) (disjoint : Disjoint L (centralizer (L : Set G)))
      (rank_eq : SeedRankEquality ρ A L)
  | symmetricFive
      (action : MarkedActionEquiv (seedSubrepresentation ρ hLA).toRepresentation
        ⊤ (L.subgroupOf (L ⊔ A))
        (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))
      (order : Nat.card (seedOffenderImage ρ hLA) = 2)
      (rank_eq : SeedRankEquality ρ A L)
  | doubleThree (F : BinaryField) (odd_degree : Odd F.degree)
      (natural : IsRepeatedLinearNatural (seedComponentAction ρ hLA) F 3 2)
      (span : naturalSeedSpace ρ L A ≤ sSup {I | IsIrrPlus ρ L I})
      (inner : InducesInner A L) (disjoint : Disjoint L (centralizer (L : Set G)))
      (rank_eq : SeedRankEquality ρ A L)
  | naturalThree (F : BinaryField) (odd_degree : Odd F.degree)
      (natural : ActionEquiv (seedComponentAction ρ hLA) (linearNatural F 3))
      (inner : InducesInner A L)
  | fourCover (cover : FourDimensionalCoverSource (seedComponentAction ρ hLA))
      (klein : Nonempty (seedOffenderImage ρ hLA ≃* Multiplicative (Fin 2 → ZMod 2)))
      (irrPlus : IsIrrPlus ρ L (naturalSeedSpace ρ L A))
      (inner : InducesInner A L) (disjoint : Disjoint L (centralizer (L : Set G)))
      (rank_eq : SeedRankEquality ρ A L)

/-- Case (IV) already gives the requested seed, with only its justified LA-action. -/
theorem naturalSeed_of_localNatural {A L : Subgroup G} (hLA : ⁅L,A⁆ = L)
    (F : BinaryField) (ho : Odd F.degree)
    (hn : ActionEquiv (seedComponentAction ρ hLA) (linearNatural F 3))
    (hi : InducesInner A L) (s : MovedSection ρ L) : PreliminaryConclusion ρ A L s :=
  .naturalSeed ⟨F,ho,seedSubrepresentation ρ hLA,rfl,hn,hi⟩

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
