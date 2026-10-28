module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.SmallRows

/-!
# Remaining moved-section rows in the quintic comparison

Apply the complete B.5.1 classifier to the actual C.2.7 star action.
The natural row is already impossible. The generated small alternating
and triple-six rows contradict the invariant two-subgroup argument, as
do the binary degree-four whole-component rows. The surviving small
outer rows retain their marked action equivalences, not only group names.
The complete six-clause source conclusion remains in the output.

This is a proved reduction, not the final 14.6.15 exclusion. The remaining
classical and outer rows and the exchanged module geometry stay with
qt-e-14615-quintic-exclusion; earlier14.6.12--14 discharge stays with
qt-e-suitable-odd-normalizer. Source: Aschbacher--Smith, pp.99--103,1035.
-/
@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open ComponentExclusion ComponentExtraction ComponentExclusion.ContainedComparison
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource
universe u v

/-- Surviving actual models and the marked small outer action rows. All
source clauses on the moved section are retained separately in the consumer. -/
inductive RemainingQuinticRow {D : Type u} [Group D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D) : Prop
  | linearThree (F : BinaryField) (e : L ≃* SL(3,F.Carrier))
  | symplectic (F : BinaryField) (large : 1 < F.degree)
      (e : L ≃* Matrix.symplecticGroup (Fin 2) F.Carrier)
  | symplecticTwo (e : MarkedActionEquiv ρ (offenderSubgroup ρ) L
      (symplecticNatural (k := ZMod 2) 2)
        (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))))
  | g2 (F : BinaryField) (large : 1 < F.degree) (e : L ≃* Atlas.G2.Model F.Carrier)
  | g2Two (e : MarkedActionEquiv ρ (offenderSubgroup ρ) L
      (g2Natural (ZMod 2)) (commutator (Atlas.G2.Model (ZMod 2))))
  | symmetric (n : ℕ) (degree : n = 5 ∨ n = 7 ∨ n = 8)
      (e : MarkedActionEquiv ρ (offenderSubgroup ρ) L
        (BinaryPermutation.naturalRepresentation (Fin n)) (alternatingGroup (Fin n)))
  | binaryFive (e : L ≃* SL(5,ZMod 2))

private theorem binary_whole_of_source_extension
    {D : Type*} [Group D] [Finite D] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D)
    {d : ℕ} (hd : d = 4 ∨ d = 5)
    (e : ActionEquiv (ρ.comp L.subtype) (linearNatural BinaryField.two d))
    (hext : L = ⊤ ∨ (∀ T : Sylow 2 D, L ⊔ (T : Subgroup D) = ⊤) ∧
      OuterNaturalAction ρ) : L = ⊤ := by
  rcases hext with ht | ⟨_,hout⟩
  · exact ht
  exfalso
  have hdim : Module.finrank (ZMod 2) V = d := by
    have hh := e.linearEquiv.finrank_eq
    change Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) (Fin d → ZMod 2) at hh
    simpa using hh
  rcases hout with ⟨n,hn,hN,⟨a⟩⟩ | ⟨a⟩
  · have ha := a.linearEquiv.finrank_eq
    rw [hdim] at ha
    have hm : Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin n)) =
        if n = 5 ∨ n = 6 then 4 else 6 := by
      interval_cases n <;>
        first
        | simpa using BinaryPermutation.finrank_natural_odd (Fin _) (by decide)
        | simpa using BinaryPermutation.finrank_natural_even (Fin _) (by decide)
    rw [hm] at ha
    have hn6 : n ≤ 6 := by split_ifs at ha <;> omega
    have hd4 : d = 4 := by split_ifs at ha <;> omega
    have hcL : Nat.card L = 20160 := by
      rw [Nat.card_congr e.groupEquiv.toEquiv]
      change Nat.card SL(d,ZMod 2) = _
      rw [hd4,Atlas.Order20160A8.sl4Two_card]
    have hc := Nat.card_le_card_of_injective L.subtype L.subtype_injective
    rw [hcL,Nat.card_congr a.groupEquiv.toEquiv,Nat.card_perm,Nat.card_fin] at hc
    have hb := Nat.factorial_le hn6
    norm_num at hb
    omega
  · obtain ⟨a⟩ := a
    have ha := a.linearEquiv.finrank_eq
    rw [hdim,Atlas.G2.Natural.finrank_space] at ha
    omega

private theorem remaining_of_source_rows
    {D : Type*} [Group D] [Finite D] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D)
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ L)
    (hnatural : ∀ (F : BinaryField),
      ActionEquiv (c.sectionData.action.comp L.subtype) (linearNatural F 2) →
      quadraticRatio c.sectionData.action = 1 →
      (∀ B, IsBestOffender c.sectionData.action B →
        ∃ S : Sylow 2 L, B = (S : Subgroup L).map L.subtype) → False)
    (hsmall : offenderSubgroup c.sectionData.action = L →
      quadraticRatio c.sectionData.action = 1 →
      ∀ n, (n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) → (L ≃* alternatingGroup (Fin n)) → False)
    (htriple : offenderSubgroup c.sectionData.action = L →
      quadraticRatio c.sectionData.action = 1 →
      ChapterB.SourceInduction.ProjectiveLine.TripleSixAction c.sectionData.action L → False)
    (hfour : L = ⊤ → (L ≃* SL(4,ZMod 2)) → False) :
    RemainingQuinticRow c.sectionData.action L := by
  cases c.clause_one with
  | irreducible _ _ _ hs hext =>
    cases hs with
    | linearTwo F _ e ho hr =>
      exact (hnatural F e hr ho).elim
    | linearThree F _ e _ => exact .linearThree F e.groupEquiv
    | symplectic F hl _ e _ => exact .symplectic F hl e.groupEquiv
    | symplecticTwo e _ => exact .symplecticTwo e
    | g2 F hl _ e _ _ => exact .g2 F hl e.groupEquiv
    | g2Two e _ _ => exact .g2Two e
    | symmetric n hn e _ _ => exact .symmetric n (hn.imp_right Or.inl) e
    | alternatingSix hgen e _ hr =>
      exact (hsmall hgen hr _ (Or.inr (Or.inl rfl)) e.groupEquiv).elim
    | alternatingSeven hgen _ e _ _ hr =>
      exact (hsmall hgen hr _ (Or.inr (Or.inr (Or.inl rfl))) e).elim
    | tripleSix hgen e hr =>
      exact (htriple hgen hr e).elim
    | binaryLinear n hn _ e _ =>
      have hw := binary_whole_of_source_extension _ _ hn e hext
      rcases hn with rfl | rfl
      · exact (hfour hw e.groupEquiv).elim
      · exact .binaryFive e.groupEquiv
    | orthogonalSix hgen _ e _ hr =>
      exact (hsmall hgen hr _ (Or.inr (Or.inr (Or.inr rfl))) e.groupEquiv).elim
    | symmetricEight _ e _ => exact .symmetric 8 (Or.inr (Or.inr rfl)) e
    | exteriorFive _ _ e _ _ _ => exact .binaryFive e
  | doubleThree F _ e _ _ => exact .linearThree F e.groupEquiv
  | naturalDual n hn hw he =>
    obtain ⟨e⟩ := he
    rcases hn with rfl | rfl
    · exact (hfour hw e.groupEquiv).elim
    · exact .binaryFive e.groupEquiv
  | repeatedNatural n r hn _ _ hw he =>
    obtain ⟨e⟩ := he
    rcases hn with rfl | rfl
    · exact (hfour hw e.groupEquiv).elim
    · exact .binaryFive e.groupEquiv

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

/-- Sieve the complete source conclusion on the same marked moved section. -/
theorem source_component_moved_row_reduction
    (hCJ : starImage j.J (Mc.pCoreIn 2) j.J ≤
      offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((starRepresentation j.J (Mc.pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))).subtype)
      ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))))) :
    RemainingQuinticRow c.sectionData.action
      ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))) := by
  apply remaining_of_source_rows _ _ c
  · intro F e hr ho
    exact source_component_no_natural_row s d j ⟨⟨hCJ,c.sectionData,F,e,hr,ho⟩⟩
  · intro hg hr n hn e
    exact source_no_small_alternating_ratio_one_row s d j hCJ c.sectionData hg hr hn e
  · intro hg hr e
    exact source_no_triple_six_ratio_one_row s d j hCJ c.sectionData hg hr e
  · intro hw e
    exact source_no_whole_linear_four_row s d j hCJ hw e

/-- No row-selection callback is used: construct and reduce the original
six-clause classification on its literal C.2.7 representation. -/
theorem source_component_remaining_moved_rows :
    ∃ (_hCJ : starImage j.J (Mc.pCoreIn 2) j.J ≤
      offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))
      (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((starRepresentation j.J (Mc.pCoreIn 2)).comp
          (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))).subtype)
        ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
          (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))))),
      RemainingQuinticRow c.sectionData.action
        ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
          (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))) := by
  have hi := source_component_input s d j
  have hc := star_moved_section_from_source hi
  let c := Classical.choice hc.2
  exact ⟨hc.1,c,source_component_moved_row_reduction s d j hc.1 c⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
