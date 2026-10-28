module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.ModelSieve
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.AlternatingSixCover
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.RadicalQuotient

/-!
# The full source catalogue for the actual moved component

The enlarged flag parabolic is two-local, hence SQTK. Restriction to the
normal component and passage through its literal two-core quotient preserve
SQTK. The proved A.3.6 theorem therefore supplies the full source alternatives,
without assuming that this quotient is already a simple Theorem C model.
The previous action sieve removes the excluded simple rows; the even
special-linear and unitary calculations also remove those covering rows.
The A₆ and A₇ central-cover rows are excluded as well. All other covering
and nonquasisimple cases remain visible.

The escape consumer uses this same component and quotient. Recognition of J₁,
intersection escape and terminal geometry remain with
qt-d-1222-natural-line-action. Source: Aschbacher--Smith A.3.6 and 3.3.12,
printed pp.43--45,588--590.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
open Chapter1.Section02 Chapter1.Section02.LocalModels

/-- The unexcluded simple rows, with actual carrier isomorphisms. -/
def RemainingSimpleModel (Q : Type*) [Group Q] : Prop :=
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ unitary : Bool, IsPSLSign Q unitary 3 p) ∨
    (∃ name : ClassificationModels.SporadicName, name ≠ .j3 ∧
      Nonempty (Q ≃* name.Carrier)) ∨ Nonempty (Q ≃* Janko1.Model)

/-- The full covering rows still requiring exclusion after the even classical sieve. -/
inductive RemainingCoverModel (Q : Type*) [Group Q] : Prop
  | classical (p : ℕ) (hp : p.Prime) (ho : Odd p) (unitary : Bool)
      (model : IsSLSign Q unitary 3 p)
  | mathieu (model : IsM22Cover Q)

/-- The complete source alternatives on the literal quotient. The top subgroup
in the last two cases only expresses the unchanged A.3.6 data. -/
inductive RemainingSourceCases (Q : Type*) [Group Q] [Finite Q] : Prop
  | simple (simple : IsSimpleGroup Q) (model : RemainingSimpleModel Q)
  | cover (quasisimple : IsQuasisimple Q)
      (center : Nonempty (Subgroup.center Q ≃* Multiplicative (ZMod 3)))
      (model : RemainingCoverModel Q)
  | natural (data : A36Natural (⊤ : Subgroup Q))
  | nilpotent (data : A36Nilpotent (⊤ : Subgroup Q))

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c} {A : OddSupplement T}
namespace MovedComponent
variable (E : MovedComponent S f A)

/-- The actual component inherits SQTK from the genuine enlarged local group. -/
theorem component_sqtk : IsSQTK KnownSimple.IsKnownSimple E.component := by
  let H := (f.Li E.index ⊔ (T : Subgroup G)) ⊔ A.subgroup
  have hH := (invariantFlag_geometry D S f).2.2.enlarged_parabolic_source A E.index
  have hHN : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hN : IsTwoLocal (normalizer (H.pCoreIn 2 : Set G)) :=
    ⟨H.pCoreIn 2,hH.1,pCore_isPGroup.map H.subtype,rfl⟩
  have hs : IsSQTK KnownSimple.IsKnownSimple H :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp
      ((S.source.simpleQTKE.twoLocal_sqtk hN).subgroup _)
  exact (IsSQTK.equiv (subgroupOfEquivOfLe E.normal_component.1.1)).mp
    (hs.subgroup (E.component.subgroupOf H))

/-- Quotient SQTK uses the actual two-group kernel, not arbitrary quotient closure. -/
theorem componentQuotient_sqtk :
    IsSQTK KnownSimple.IsKnownSimple (E.component ⧸ pCore 2 E.component) := by
  refine ⟨?_,E.component_sqtk.isKGroup.quotient (pCore 2 E.component)⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (E.component_sqtk.stronglyQuasithin p hp ho)

/-- Every clause of A.3.6 is supplied by the proved earlier theorem. -/
theorem componentQuotient_source :
    A36Conclusion (⊤ : Subgroup (E.component ⧸ pCore 2 E.component)) :=
  ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    _ E.componentQuotient_sqtk (pCore_quotient_pCore_eq_bot 2) _
    E.componentQuotient_isCComponent

private theorem cover_of_top {Q : Type*} {H : Type} [Group Q] [Group H]
    (h : IsThreeCover (⊤ : Subgroup Q) H) : IsThreeCover Q H := by
  let e : (⊤ : Subgroup Q) ≃* Q := topEquiv
  refine ⟨h.1.of_mulEquiv e,?_,?_⟩
  · obtain ⟨z⟩ := h.2.1
    exact ⟨(centerCongr e).symm.trans z⟩
  · obtain ⟨z⟩ := h.2.2
    have he : (center (⊤ : Subgroup Q)).map e.toMonoidHom = center Q := by
      apply le_antisymm
      · rintro _ ⟨x,hx,rfl⟩
        exact (centerCongr e ⟨x,hx⟩).property
      · intro x hx
        exact ⟨e.symm x, (centerCongr e.symm ⟨x,hx⟩).property, e.apply_symm_apply x⟩
    exact ⟨(QuotientGroup.congr _ _ e he).symm.trans z⟩

/-- The exact covering catalogue loses all even classical and alternating rows. -/
theorem remaining_cover (hm : ThreeCoverModel (⊤ : Subgroup
    (E.component ⧸ pCore 2 E.component))) :
    RemainingCoverModel (E.component ⧸ pCore 2 E.component) := by
  let e : (E.component ⧸ pCore 2 E.component) ≃*
    (⊤ : Subgroup (E.component ⧸ pCore 2 E.component)) := topEquiv.symm
  cases hm with
  | classical u q hq hi =>
    have hmodel : IsSLSign (E.component ⧸ pCore 2 E.component) u 3 q := by
      cases u with
      | false =>
        obtain ⟨F,hF,hfin,hcard,⟨a⟩⟩ := hi
        exact ⟨F,hF,hfin,hcard,⟨e.trans a⟩⟩
      | true =>
        obtain ⟨F,hF,hfin,J,hcard,hconj,⟨a⟩⟩ := hi
        exact ⟨F,hF,hfin,J,hcard,hconj,⟨e.trans a⟩⟩
    rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hp,ho⟩
    · cases u with
      | false => exact (E.quotient_not_even_special_linear_three hn hmodel).elim
      | true => exact (E.quotient_not_binary_su3 (by omega) hmodel).elim
    · exact .classical q hp ho u hmodel
  | alternating_six h => exact (E.quotient_not_alternating_six_cover (cover_of_top h)).elim
  | alternating_seven h => exact (E.quotient_not_alternating_seven_cover (cover_of_top h)).elim
  | mathieu h => exact .mathieu (cover_of_top h)

/-- The full source sieve, with no simple-model or covering premise. -/
theorem remaining_source_cases :
    RemainingSourceCases (E.component ⧸ pCore 2 E.component) ∧
      A36Common (⊤ : Subgroup (E.component ⧸ pCore 2 E.component)) := by
  obtain ⟨h,hcommon⟩ := E.componentQuotient_source
  refine ⟨?_,hcommon⟩
  cases h with
  | simple hcomp hs hm =>
    let : IsSimpleGroup (⊤ : Subgroup (E.component ⧸ pCore 2 E.component)) := hs
    let : Group.IsPerfect (⊤ : Subgroup (E.component ⧸ pCore 2 E.component)) :=
      hcomp.2.toIsPerfect
    let : IsSimpleGroup (E.component ⧸ pCore 2 E.component) :=
      (topEquiv : (⊤ : Subgroup (E.component ⧸ pCore 2 E.component)) ≃* _).symm.isSimpleGroup
    let : Group.IsPerfect (E.component ⧸ pCore 2 E.component) :=
      Group.IsPerfect.ofSurjective
        (f := (topEquiv : (⊤ : Subgroup (E.component ⧸ pCore 2 E.component)) ≃* _).toMonoidHom)
        topEquiv.surjective
    have hsq := E.componentQuotient_sqtk
    have hc := ChapterA.Section02.theoremC_knownSimple inferInstance
      (Group.IsPerfect.not_isMulCommutative _) hsq.stronglyQuasithin hsq.isKGroup
    exact .simple inferInstance (E.theoremC_remaining
      (ChapterA.Section03.SourceComponents.sourceTheoremC_to_local
        (Group.IsPerfect.not_isMulCommutative _) hc))
  | cover hcomp hz hm =>
    let e : (⊤ : Subgroup (E.component ⧸ pCore 2 E.component)) ≃* _ := topEquiv
    obtain ⟨z⟩ := hz
    exact .cover (hcomp.2.of_mulEquiv e) ⟨(centerCongr e).symm.trans z⟩
      (E.remaining_cover hm)
  | natural h => exact .natural h
  | nilpotent h => exact .nilpotent h

/-- In a nonquasisimple branch, the original radical quotient is prime-field PSL₂. -/
theorem nonquasisimple_radical_quotient
    (hn : ¬ IsQuasisimple (E.component ⧸ pCore 2 E.component)) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧
      ClassicalGroup.IsPSL (E.component ⧸ solvableRadical E.component) 2 p :=
  radical_quotient_pslTwo_of_a36_image E.component topEquiv.symm
    E.componentQuotient_source hn

end MovedComponent

/-- The original escape feeds the complete source sieve on its actual moved component. -/
theorem exists_moved_component_source_cases (f : InvariantFlag c) (A : OddSupplement T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ E : MovedComponent S f A,
      RemainingSourceCases (E.component ⧸ pCore 2 E.component) ∧
      A36Common (⊤ : Subgroup (E.component ⧸ pCore 2 E.component)) := by
  obtain ⟨E⟩ := exists_movedComponent f A hescape
  exact ⟨E,E.remaining_source_cases⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
