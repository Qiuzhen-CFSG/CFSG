module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.FourDimensional

/-!
# Removing the marked four-dimensional outer rows

The full B.5.1 conclusion supplies faithfulness in its irreducible branch.
The marked S₅ and Sp₄(2) actions have binary dimension four, so the
four-dimensional normalizer obstruction excludes both, retaining the actual
star quotient and the full six-clause source conclusion. The other completed
comparisons remove the natural, binary linear and generated alternating rows.

Only the classical rows and marked S₇/S₈ rows remain. Their comparison, the
exchanged module geometry and p=3 assembly stay with qt-e-14615-quintic-exclusion;
earlier 14.6.12--14 stay with qt-e-suitable-odd-normalizer.
Source: Aschbacher--Smith 14.6.15, printed p.1035, using B.5.1 and C.2.7.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open ComponentExclusion ComponentExtraction ComponentExclusion.ContainedComparison
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)
local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))
variable (d : NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) s.critical.endpoint.representative)
    (j : SourceEscapingComponent Mc (residualClosure H Mc) d.K1 d.K2 (Mc.pCoreIn 2))


private theorem small_alternating_outer_two {n : ℕ}
    (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) :
    IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin n))) := by
  by_cases h6 : n = 6
  · subst n
    exact IsPGroup.of_card (n := 2) AlternatingSix.ShadowLocal.outer_card
  let A := alternatingGroup (Fin n)
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have htwo : IsPGroup 2 (Equiv.Perm (Fin n) ⧸ A) := by
    apply IsPGroup.of_card (n := 1)
    rw [←A.index_eq_card,alternatingGroup.index_eq_two]
    rfl
  apply htwo.of_surjective (MulAut.outerAction A)
  intro x
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
  obtain ⟨t,rfl⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n
    (by omega) h6).surjective a
  exact ⟨QuotientGroup.mk' A t,rfl⟩

private theorem small_alternating_outer_two_of_equiv {D : Type*} [Group D] {n : ℕ}
    (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
    (e : D ≃* alternatingGroup (Fin n)) : IsPGroup 2 (MulAut.Outer D) :=
  (small_alternating_outer_two hn).of_injective (MulAut.outerCongr e).toMonoidHom
    (MulAut.outerCongr e).injective

private theorem small_alternating_centerless {D : Type*} [Group D] {n : ℕ}
    (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
    (e : D ≃* alternatingGroup (Fin n)) : center D = ⊥ := by
  have hc : center (alternatingGroup (Fin n)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp; omega)
  apply _root_.eq_bot_iff.mpr
  intro z hz
  have hh : e z ∈ center (alternatingGroup (Fin n)) := (centerCongr e ⟨z,hz⟩).property
  rw [hc,mem_bot] at hh
  exact e.map_eq_one_iff.mp hh

/-- Remaining classical and large marked permutation actions. -/
inductive LargeQuinticRow {D : Type*} [Group D]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D) : Prop
  | linearThree (F : BinaryField) (degree : ¬4 ∣ F.degree) (e : L ≃* SL(3,F.Carrier))
  | symplectic (F : BinaryField) (large : 1 < F.degree) (degree : Odd F.degree)
      (e : L ≃* Matrix.symplecticGroup (Fin 2) F.Carrier)
  | g2 (F : BinaryField) (large : 1 < F.degree) (degree : Odd F.degree)
      (field_five : 5 ∣ F.degree) (e : L ≃* Atlas.G2.Model F.Carrier)
  | symmetric (n : ℕ) (degree : n = 7 ∨ n = 8)
      (e : MarkedActionEquiv ρ (offenderSubgroup ρ) L
        (BinaryPermutation.naturalRepresentation (Fin n)) (alternatingGroup (Fin n)))

private theorem large_of_nonbinary
    {D : Type*} [Group D] [Finite D]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D)
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ L)
    (rows : NonBinaryQuinticRow c.sectionData.action L)
    (hsmall : Function.Injective c.sectionData.action →
      Module.finrank (ZMod 2)
        (c.sectionData.space.toSubmodule ⧸ c.sectionData.central.toSubmodule) = 4 →
      ∀ n, (n = 5 ∨ n = 6) → (L ≃* alternatingGroup (Fin n)) → False)
    (hlinear : ∀ F : BinaryField, (L ≃* SL(3,F.Carrier)) → ¬4 ∣ F.degree)
    (hfour : L = ⊤ → (L ≃* SL(4,ZMod 2)) → False)
    (hfive : (L ≃* SL(5,ZMod 2)) → False) :
    LargeQuinticRow c.sectionData.action L := by
  cases c.clause_one with
  | irreducible _ hf _ _ _ =>
    cases rows with
    | linearThree F hd e => exact .linearThree F hd e
    | symplectic F hl hd e => exact .symplectic F hl hd e
    | g2 F hl hd h5 e => exact .g2 F hl hd h5 e
    | symplecticTwo e =>
      apply False.elim
      apply hsmall hf (by simpa using e.action.linearEquiv.finrank_eq) 6 (Or.inr rfl)
      exact e.subgroupEquiv.trans
        (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
          (F := ZMod 2) (by simp))
    | symmetric n hn e =>
      rcases hn with rfl | rfl | rfl
      · apply False.elim
        apply hsmall hf _ 5 (Or.inl rfl) e.subgroupEquiv
        exact e.action.linearEquiv.finrank_eq.trans
          (BinaryPermutation.finrank_natural_odd (Fin 5) (by decide))
      · exact .symmetric 7 (Or.inl rfl) e
      · exact .symmetric 8 (Or.inr rfl) e
  | doubleThree F _ e _ _ => exact .linearThree F (hlinear F e.groupEquiv) e.groupEquiv
  | naturalDual n hn hw he =>
    obtain ⟨e⟩ := he
    rcases hn with rfl | rfl
    · exact (hfour hw e.groupEquiv).elim
    · exact (hfive e.groupEquiv).elim
  | repeatedNatural n r hn _ _ hw he =>
    obtain ⟨e⟩ := he
    rcases hn with rfl | rfl
    · exact (hfour hw e.groupEquiv).elim
    · exact (hfive e.groupEquiv).elim

/-- Reduce the complete source classifier, discharging faithfulness and
four-dimensionality from the actual marked rows. -/
theorem source_component_large_row_reduction
    (hCJ : starImage j.J (Mc.pCoreIn 2) j.J ≤
      offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((starRepresentation j.J (Mc.pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))).subtype)
      ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))))) :
    LargeQuinticRow c.sectionData.action
      ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))) := by
  apply large_of_nonbinary _ _ c (source_component_nonbinary_row_reduction s d j hCJ c)
  · intro hf hd n hn e
    let E := (subgroupOfEquivOfLe hCJ).symm.trans e
    have hn' : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := hn.imp_right Or.inl
    exact source_no_four_dimensional_moved s d j
      (small_alternating_centerless hn' E) (small_alternating_outer_two_of_equiv hn' E)
      c.sectionData hf hd
  · intro F e
    exact source_component_linear_degree s d j F ((subgroupOfEquivOfLe hCJ).symm.trans e)
  · intro hw e
    exact source_no_whole_linear_four_row s d j hCJ hw e
  · intro e
    exact source_no_binary_five_star s d j ((subgroupOfEquivOfLe hCJ).symm.trans e)

/-- The actual escaping component supplies the reduced marked catalogue
and every original B.5.1 clause, without a model-selection premise. -/
theorem source_component_large_moved_rows :
    ∃ (_hCJ : starImage j.J (Mc.pCoreIn 2) j.J ≤
      offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))
      (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((starRepresentation j.J (Mc.pCoreIn 2)).comp
          (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))).subtype)
        ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
          (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))))),
      LargeQuinticRow c.sectionData.action
        ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
          (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))) := by
  have hi := source_component_input s d j
  have hc := star_moved_section_from_source hi
  let c := Classical.choice hc.2
  exact ⟨hc.1,c,source_component_large_row_reduction s d j hc.1 c⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
