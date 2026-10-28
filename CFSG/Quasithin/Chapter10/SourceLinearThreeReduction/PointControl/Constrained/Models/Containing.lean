module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Action
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.AlternatingSmall
public import Theory.SpecificGroups.PSL3Two.SolvableSylowOvergroups
public import Theory.SpecificGroups.G2.BinarySolvableSylowOvergroups

/-!
# Containing groups of the literal constrained FF action

The B.5.1 source action has a proper local C-component containing a full
Sylow two-subgroup. Solvable proper Sylow overgroups exclude the rank-one
and small alternating, symplectic and G₂ endpoints. The remaining actors
are SL₃, Sp₄ and G₂ over a field larger than two, A₇, and SL₄(2) or SL₅(2).
Every alternative carries an actual group isomorphism. The final theorem
applies the list to the original action on VI and its actual smaller image.
This recognizes groups; the original module and containing action markings
remain obligations of qt-d-10-nona5-point-constrained.

Source: Aschbacher--Smith 10.2.9, printed p.751, cases (a)--(c).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings

/-- The possible actual containing actors after the proper local-component sieve. -/
inductive ContainingModel (A : Type*) [Group A] : Prop
  | linearThree (F : BinaryField) (large : 1 < F.degree) (equiv : A ≃* SL(3,F.Carrier))
  | symplecticFour (F : BinaryField) (large : 1 < F.degree)
      (equiv : A ≃* Matrix.symplecticGroup (Fin 2) F.Carrier)
  | g2 (F : BinaryField) (large : 1 < F.degree) (equiv : A ≃* Atlas.G2.Model F.Carrier)
  | alternatingSeven (equiv : A ≃* alternatingGroup (Fin 7))
  | binaryLinear (d : ℕ) (degree : d = 4 ∨ d = 5) (equiv : A ≃* SL(d,ZMod 2))

theorem ContainingModel.of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : ContainingModel B) : ContainingModel A := by
  cases h with
  | linearThree F hn a => exact .linearThree F hn (e.trans a)
  | symplecticFour F hn a => exact .symplecticFour F hn (e.trans a)
  | g2 F hn a => exact .g2 F hn (e.trans a)
  | alternatingSeven a => exact .alternatingSeven (e.trans a)
  | binaryLinear d hd a => exact .binaryLinear d hd (e.trans a)

private theorem no_proper_of_solvable_sylow_overgroups
    {A : Type*} [Group A] [Finite A] [IsQuasisimple A]
    (S : Sylow 2 A) (B : Subgroup A) (hB : B ∈ localCComponents S)
    (hp : B ≠ ⊤) (hs : SolvableSylowOvergroups A) : False := by
  have ht : (⊤ : Subgroup A).IsCComponent :=
    (show IsComponent A ⊤ from ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  exact hp (eq_of_solvable_sylow_overgroups S hB ht le_top
    (SolvableSylowOvergroups.of_equiv topEquiv hs))

private theorem linearThree_large
    {A : Type*} [Group A] [Finite A] [IsQuasisimple A]
    (S : Sylow 2 A) (B : Subgroup A) (hB : B ∈ localCComponents S)
    (hp : B ≠ ⊤) (F : BinaryField) (e : A ≃* SL(3,F.Carrier)) : 1 < F.degree := by
  by_contra hlarge
  have hn : F.degree = 1 := by have := F.degree_pos; omega
  have hc : Nat.card F.Carrier = 2 := by rw [F.card_eq,hn]; norm_num
  exact no_proper_of_solvable_sylow_overgroups S B hB hp
    (SolvableSylowOvergroups.of_equiv e
      (Matrix.PSL3Two.solvableSylowOvergroups_specialLinear_of_card_two hc))

private theorem alt_eight_model {A : Type*} [Group A]
    (e : A ≃* alternatingGroup (Fin 8)) : ContainingModel A :=
  .binaryLinear 4 (Or.inl rfl) ((e.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two).trans
    (_root_.BinaryLinear.OuterCyclic.projectiveEquivSL (by decide)))

/-- B.5.1 together with a proper full-Sylow local component gives the group list. -/
theorem containingModel_of_source_case
    {Q V : Type*} [Group Q] [Finite Q] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Q V) (A : Subgroup Q) [IsQuasisimple A]
    (s : MovedSection ρ A) (hc : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ A s)
    (S : Sylow 2 A) (B : Subgroup A) (hB : B ∈ localCComponents S) (hp : B ≠ ⊤) :
    ContainingModel A := by
  cases hc with
  | irreducible _ _ _ source _ =>
    cases source with
    | linearTwo F _ a _ _ =>
      exact (no_proper_of_solvable_sylow_overgroups S B hB hp
        (SolvableSylowOvergroups.of_equiv a.groupEquiv
          Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup)).elim
    | linearThree F _ a _ =>
      exact .linearThree F (linearThree_large S B hB hp F a.groupEquiv) a.groupEquiv
    | symplectic F hn _ a _ => exact .symplecticFour F hn a.groupEquiv
    | symplecticTwo a _ =>
      exact (FiveLocalFF.AlternatingSmall.not_proper_symplectic_two_derived S B hB hp
        a.subgroupEquiv).elim
    | g2 F hn _ a _ _ => exact .g2 F hn a.groupEquiv
    | g2Two a _ _ =>
      exact (no_proper_of_solvable_sylow_overgroups S B hB hp
        (SolvableSylowOvergroups.of_equiv a.subgroupEquiv
          Atlas.G2.BinaryDerived.solvableSylowOvergroups)).elim
    | symmetric n hn a _ _ =>
      rcases hn with rfl | rfl
      · exact (FiveLocalFF.AlternatingSmall.not_proper_five S B hB hp a.subgroupEquiv).elim
      · exact .alternatingSeven a.subgroupEquiv
    | alternatingSix _ a _ _ =>
      exact (FiveLocalFF.AlternatingSmall.not_proper_six S B hB hp a.groupEquiv).elim
    | alternatingSeven _ _ a _ _ _ => exact .alternatingSeven a
    | tripleSix _ a _ =>
      exact (FiveLocalFF.AlternatingSmall.not_proper_central_six S B hB hp a.quotientEquiv).elim
    | binaryLinear d hd _ a _ => exact .binaryLinear d hd a.groupEquiv
    | orthogonalSix _ _ a _ _ => exact alt_eight_model a.groupEquiv
    | symmetricEight _ a _ => exact alt_eight_model a.subgroupEquiv
    | exteriorFive _ _ a _ _ _ => exact .binaryLinear 5 (Or.inr rfl) a
  | doubleThree F _ a _ _ =>
    exact .linearThree F (linearThree_large S B hB hp F a.groupEquiv) a.groupEquiv
  | naturalDual d hd _ hn => exact .binaryLinear d hd hn.some.groupEquiv
  | repeatedNatural d r hd _ _ _ hn => exact .binaryLinear d hd hn.some.groupEquiv

private theorem containingModel_of_source_overgroup
    {Q V : Type*} [Group Q] [Finite Q] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Q V) (A N : Subgroup Q) (hAN : A ≤ N)
    [IsQuasisimple A]
    (h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp N.subtype) (A.subgroupOf N))
    (S : Sylow 2 A) (B : Subgroup A) (hB : B ∈ localCComponents S) (hp : B ≠ ⊤) :
    ContainingModel A := by
  let e : A ≃* A.subgroupOf N := (subgroupOfEquivOfLe hAN).symm
  let : IsQuasisimple (A.subgroupOf N) := IsQuasisimple.of_mulEquiv e
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    exact Group.isSolvable_of_comm (fun _ _ => Subsingleton.elim _ _)
  have hl := Chapter1.Section02.localCComponents_map_of_solvable_ker
    (G := A) (G' := A.subgroupOf N) (B := B) (S := (S : Subgroup A)) hB e.toMonoidHom

  have hproper : B.map e.toMonoidHom ≠ ⊤ := by
    intro he
    apply hp
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_top_of_surjective e.toMonoidHom e.surjective]
    exact he
  exact ContainingModel.of_equiv e (containingModel_of_source_case _ _ h.sectionData h.clause_one
    (S.mapSurjective (f := e.toMonoidHom) e.surjective) (B.map e.toMonoidHom) hl hproper)


open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The original reduced orbit action has one of the recognized containing groups. -/
theorem Context.containing_model (c : Context D t v I) (a : ActionFacts c) :
    letI := c.reduced.normal
    ContainingModel ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) := by
  let H := pointJoin T v I
  let U := internalModule D v I
  let := c.reduced.normal
  let := c.reduced.elementary
  let q := actionMk U
  let K := I.subgroupOf H
  let A := K.map q
  let ρ := action U
  let N := offenderSubgroup ρ
  obtain ⟨hA,hAN,_,_,_,⟨h⟩⟩ := a.classification
  let : IsQuasisimple A := hA
  obtain ⟨hp,R,_,hB⟩ := a.small_local
  exact containingModel_of_source_overgroup ρ A N hAN h
    (R.mapSurjective (q.subgroupMap_surjective K)) _ hB hp.ne

end CFSG.Quasithin.Chapter10.PointControl.Constrained
