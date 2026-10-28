module

public import Theory.SpecificGroups.Triality.RootPresentationRecognition.PositiveEvaluation
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.ScalarMarking
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.MarkedLocal

/-!
# Positive triality presentation on the literal marked source quotient

Original cubic-field roots and the fifteen explicit equations construct a
homomorphism from the genuine triality unipotent subgroup onto the specified
source U. The field marking intertwines Frobenius and restricts to the
original fixed field, so every original root parameter retains its value.
The quotient is literally X / Q.D. Its numerator can be the original generated
group or the universal geometric completion.

This supplies only the positive part of the triality presentation. The signed
relations, abstract Bruhat cover, full ambient equivalence and both oriented
parabolic comparisons remain necessary for the source recognition theorem.
No such conclusions or model homomorphisms are fields of this data.

Source: GLS3 2.3.5 and 2.4.5; DGS Theorem D, printed p.224;
Aschbacher–Smith F.1.1. Source construction of the root data remains explicit.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialityPresentation
variable {X F : Type*} [Group X] [Field F] {Psrc : Fin 2 → Subgroup X}

/-- The positive portion of the source contract, with equations on original scalars. -/
structure PositiveRootData (Q : MarkedQuotient Psrc) (split : SplitData Q.tits)
    (m : ℕ) (hm : 0 < m) (σ : F ≃+* F) where
  scalars : ScalarMarking (binaryParameters m hm) σ
  shortRoot : Fin 3 → Multiplicative F →* X ⧸ Q.D
  longRoot : Fin 3 → Multiplicative (ScalarMarking.SourceFixed (σ := σ)) →* X ⧸ Q.D
  relations : scalars.SourceRelations shortRoot longRoot
  positive : (scalars.positiveRoots shortRoot longRoot).positiveClosure = split.U

namespace PositiveRootData
variable {Q : MarkedQuotient Psrc} {split : SplitData Q.tits}
  {m : ℕ} {hm : 0 < m} {σ : F ≃+* F} (d : PositiveRootData Q split m hm σ)
local notation "P" => binaryParameters m hm

/-- The six original maps, expressed in compatible native field coordinates. -/
def roots : PositiveRoots m hm (X ⧸ Q.D) :=
  d.scalars.positiveRoots d.shortRoot d.longRoot

/-- The source equations discharge the map-free positive relation contract. -/
theorem root_relations : d.roots.Relations :=
  d.scalars.transport_relations d.shortRoot d.longRoot d.relations

/-- Constructed from relations and collection; no ambient model map is assumed. -/
def nativeHom : unipotent P →* X ⧸ Q.D :=
  d.roots.positiveHom d.root_relations

/-- Every short root preserves its original source field parameter. -/
theorem nativeHom_short (i : Fin 3) (t : F) (u : unipotent P)
    (hu : u.val = RadicalCoordinates.LeviCommutators.short P rfl i (d.scalars.extension t)) :
    d.nativeHom u = d.shortRoot i (.ofAdd t) := by
  rw [nativeHom, PositiveRoots.positiveHom_short _ _ i _ u hu]
  exact d.scalars.positiveRoots_short d.shortRoot d.longRoot i t

/-- Long root values use the restriction of the same cubic-field marking. -/
theorem nativeHom_long (i : Fin 3) (t : ScalarMarking.SourceFixed (σ := σ))
    (u : unipotent P)
    (hu : u.val = RadicalCoordinates.LeviCommutators.long P rfl i (d.scalars.fixed t)) :
    d.nativeHom u = d.longRoot i (.ofAdd t) := by
  rw [nativeHom, PositiveRoots.positiveHom_long _ _ i _ u hu]
  exact d.scalars.positiveRoots_long d.shortRoot d.longRoot i t

/-- The entire specified source U is the image of this constructed map. -/
theorem nativeHom_range : d.nativeHom.range = split.U :=
  (d.roots.positiveHom_range d.root_relations).trans d.positive

/-- Restrict the constructed evaluation to the actual source unipotent subgroup. -/
def unipotentHom : unipotent P →* split.U :=
  d.nativeHom.codRestrict split.U (fun u => by
    rw [← d.nativeHom_range]
    exact ⟨u, rfl⟩)

@[simp] theorem unipotentHom_val (u : unipotent P) :
    (d.unipotentHom u).val = d.nativeHom u := rfl

theorem unipotentHom_surjective : Function.Surjective d.unipotentHom := by
  intro u
  have hu : u.val ∈ d.nativeHom.range := by
    rw [d.nativeHom_range]
    exact u.property
  obtain ⟨v, hv⟩ := hu
  exact ⟨v, Subtype.ext hv⟩

include d in
/-- The positive equations give the exact bound needed by abstract Bruhat collection. -/
theorem card_unipotent_le : Nat.card split.U ≤ (2 ^ m) ^ 12 := by
  have h := Nat.card_le_card_of_surjective _ d.unipotentHom_surjective
  rw [card_unipotent_binary P rfl] at h
  exact h

section OriginalMarking
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S)

/-- The carrier-general original/geometric marking identifies the same S image. -/
theorem nativeHom_range_marked : d.nativeHom.range = (MarkedLocal.sylowMap Q e h).range :=
  d.nativeHom_range.trans (MarkedLocal.sylow_range Q e h split).symm

/-- Each original S representative has a native positive preimage in this quotient.
The same statement applies to the geometric marking without a descent to J. -/
theorem marked_sylow_preimage (s : S) :
    ∃ u : unipotent P, d.nativeHom u = MarkedLocal.sylowMap Q e h s := by
  have hs : MarkedLocal.sylowMap Q e h s ∈ d.nativeHom.range := by
    rw [d.nativeHom_range_marked e h]
    exact ⟨s, rfl⟩
  exact hs

end OriginalMarking
end PositiveRootData

/-- For the actual generated numerator, the image uses the literal original quotient map. -/
theorem nativeHom_range_original {G : Type*} [Group G]
    {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    {m : ℕ} {hm : 0 < m} {σ : F ≃+* F} (d : PositiveRootData Q split m hm σ) :
    d.nativeHom.range = (S.subgroupOf (generated L S)).map Q.q :=
  d.nativeHom_range.trans (quotient_sourceS_image_eq_unipotent h Q split).symm

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialityPresentation
