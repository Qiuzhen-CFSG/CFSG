module
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction.ModelRestrictions
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.Catalogue
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable

/-!
# The actual A.1.34 quotient input for G.9

The completed Theorem A bounds every odd rank of either simple quotient
in a pair of distinct isomorphic components of an SQTK quotient. Theorem C
and the checked odd-rank-one inspection then give the four actual models.
Field transport matches the literal `QuotientModel` carriers, retaining the
central quotient and the source's full known-simple class.

`sourceA134Three_knownSimple` discharges the existing A.1.34 input, and
`source_quotient_models_knownSimple` applies it to the original G.9 component
hypothesis and the same component join. No assumption that an arbitrary
quotient is quasithin is used. The final G.9 action classification remains
with its source owner.

Source: Aschbacher--Smith A.1.34(3), A.2.1--3 and G.9.3, printed pp.29--30,
33--34 and 356.
-/

public noncomputable section
open scoped MatrixGroups
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction.ModelRestrictions
universe u v

private def centerQuotientCongr {S D : Type u} [Group S] [Group D]
    (e : S ≃* D) : (S ⧸ center S) ≃* (D ⧸ center D) :=
  QuotientGroup.congr _ _ e (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (centerCongr e ⟨y, hy⟩).property
    · intro hx
      exact ⟨e.symm x, (centerCongr e.symm ⟨x, hx⟩).property, e.apply_symm_apply x⟩)

/-- The complete source Theorem A supplies the exact semisimple section bound. -/
theorem semisimpleSectionRank_knownSimple :
    SemisimpleSectionRankTheorem.{u} KnownSimple.IsKnownSimple :=
  semisimpleSectionRank_of_theoremA
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)

private theorem quotientModel_of_fourModels {S : Type u} [Group S] [Finite S]
    [Nontrivial S] [Group.IsPerfect S]
    (h : Chapter1.Section02.NonnormalCComponentModel S) : QuotientModel S := by
  cases h with
  | linear_even n hn hm =>
    obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    let ef : F ≃+* GaloisField 2 n := FiniteField.ringEquivOfCardEq (by
      simpa only [← Nat.card_eq_fintype_card, GaloisField.card 2 n (by omega)] using hcard)
    exact .inl ⟨n, hn, ⟨(e.trans (Theory.PSL2.OuterSolvable.projectiveRingEquiv ef)).trans
      (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 n)).symm⟩⟩
  | suzuki m hm he => exact .inr (.inl ⟨m, by omega, he⟩)
  | janko he => exact .inr (.inr (.inl he))
  | linear_prime p hp ho hm =>
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hm
    have hlarge : 3 < p := by
      rw [← hcard]
      exact Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
        (hcard ▸ ho) (fun hs => by
          let := hs
          exact Group.IsPerfect.not_isSolvable S
            (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective))
    let : Fintype F := Fintype.ofFinite F
    let : Fintype (GaloisField p 1) := Fintype.ofFinite _
    let ef : F ≃+* GaloisField p 1 := FiniteField.ringEquivOfCardEq (by
      simpa only [← Nat.card_eq_fintype_card, GaloisField.card p 1 (by decide), pow_one] using hcard)
    exact .inr (.inr (.inr ⟨p, inferInstance, 1, hlarge, by decide, by decide,
      ⟨e.trans (Theory.PSL2.OuterSolvable.projectiveRingEquiv ef)⟩⟩))

/-- The original A.1.34 input, with all earlier classification premises discharged. -/
theorem sourceA134Three_knownSimple : SourceA134Three.{u} KnownSimple.IsKnownSimple := by
  intro X _ _ _ hK hcover L M hL hM hne he
  obtain ⟨cover⟩ := hcover
  obtain ⟨e⟩ := he
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Group.IsPerfect (L ⧸ center L) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p (L ⧸ center L) ≤ 1 := by
    intro p hp ho
    exact quotient_odd_rank_le_one semisimpleSectionRank_knownSimple cover
      hL hM hne (centerQuotientCongr e) hp ho
  have hsq : IsStronglyQuasithin (L ⧸ center L) :=
    fun p hp ho => (hr p hp ho).trans (by decide)
  have hna := Group.IsPerfect.not_isMulCommutative (L ⧸ center L)
  have hm := ChapterA.Section02.theoremC_knownSimple inferInstance hna hsq
    ((hK.subgroup L).quotient (center L))
  exact quotientModel_of_fourModels
    (ChapterA.SQTKStructure.NonnormalOuterSource.FourModels.model_of_odd_ranks hr
      (ChapterA.Section03.SourceComponents.sourceTheoremC_to_local hna hm))

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {A L L₂ H : Subgroup G} {m : ℕ}

/-- The literal G.9 component-pair consumer, preserving the actual central quotient. -/
theorem source_quotient_models_knownSimple
    (h : ComponentHypothesis KnownSimple.IsKnownSimple ρ A L H m)
    (hL₂ : IsComponent G L₂) (hH : H = L ⊔ L₂) (hne : L ≠ L₂)
    (e : L ≃* L₂) : QuotientModel (L ⧸ center L) :=
  source_quotient_models semisimpleSectionRank_knownSimple sourceA134Three_knownSimple
    h hL₂ hH hne e

end CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction.ModelRestrictions
