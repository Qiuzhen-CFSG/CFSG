module

public import Theory.GroupTheory.NoncentralChiefRefinement
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Source

/-!
# Refinement and chief-factor accounting for the actual L₁

Restrict G.2.5(5)'s commutator bound to the embedded two-residual `Setup.L₁`.
Both central-stratum endpoints are literal intersections with L₁, and their
normality follows from the existing conjugation bounds. Refinement contributes
zero noncentral two-chief factors on this interval.

For a supplied normal filtration from 1 to the literal two-core of L₁,
`residual_chief_accounting` fills that central slot using G.2.5(5), refines the
other supplied homogeneous strata, and extends to the whole residual using
the explicit absence of two-chief factors in its terminal quotient. Every
complete chief series has the computed count, and every actual noncentral
two-chief interval has the specified equivariant one-copy coordinates.

The earlier G.2.2 containments and L≤I remain explicit. Construction of the
other source strata, their coordinates, the terminal quotient property and
the numerical r+s+2 identification belongs to the parent source assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.2.5(5,8),
printed pp.335–336, PDF pp.346–347.
-/

@[expose] public section
open Subgroup

namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors
open NoncentralChiefRefinement
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G] {D : Setup G}
  {F : Type*} [Field F] [Finite F] {n : ℕ} {g h : G}

omit [Finite G] in
private theorem residual_le_L (D : Setup G) : D.L₁ ≤ D.L :=
  (Subgroup.map_subtype_le _).trans inf_le_left

/-- The actual intersection V∩L₁, as a normal subgroup of L₁. -/
def residualCentralLower (d : Hypothesis D F n g h) : NormalNode D.L₁ :=
  ⟨D.V.subgroupOf D.L₁, by
    exact normal_subgroupOf_of_le_normalizer
      ((residual_le_L D).trans (normalizes_of_span D d.span_eq))⟩

/-- The actual intersection S₂∩L₁, with normality from the G.2.5(5)
commutator bound and the earlier containment L≤I. -/
def residualCentralUpper (d : Hypothesis D F n g h)
    (hUT : D.U ≤ D.T) (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hLI : D.L ≤ I D g h) : NormalNode D.L₁ := by
  have hs := d.intersection hUT hf
  have hn : I D g h ≤ normalizer (S₂ D g h : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hs.2.2.2.1.trans hs.1)
  exact ⟨(S₂ D g h).subgroupOf D.L₁, by
    exact normal_subgroupOf_of_le_normalizer
      (((residual_le_L D).trans hLI).trans hn)⟩

/-- Restriction of the source central stratum retains literal subgroup
intersections and the conjugation action of the embedded two-residual. -/
theorem residual_stratum_central (d : Hypothesis D F n g h)
    (hUT : D.U ≤ D.T) (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hLI : D.L ≤ I D g h) :
    IsCentral (residualCentralLower d) (residualCentralUpper d hUT hf hLI) := by
  rw [isCentral_iff_commutator_le, Subgroup.commutator_le]
  intro k _ b hb
  have hc : ⁅I D g h, S₂ D g h⁆ ≤ D.V := by
    rw [Subgroup.commutator_comm]
    exact (d.intersection hUT hf).2.2.2.1
  exact hc (Subgroup.commutator_mem_commutator
    (((residual_le_L D).trans hLI) k.property) hb)

/-- The G.2.5(5) stratum has an actual L₁-chief refinement, all of whose
factors are central. It contributes zero to the count in clause (8). -/
theorem residual_central_chief_refinement (d : Hypothesis D F n g h)
    (hUT : D.U ≤ D.T) (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hLI : D.L ≤ I D g h) :
    ∃ s : ChiefSeries D.L₁,
      s.head = residualCentralLower d ∧ s.last = residualCentralUpper d hUT hf hLI ∧
      (∀ i : Fin s.length, IsCentral (s i.castSucc) (s i.succ)) ∧
      s.noncentralTwoCount = 0 := by
  have hle : residualCentralLower d ≤ residualCentralUpper d hUT hf hLI :=
    fun _ hx => (d.intersection hUT hf).1 hx
  obtain ⟨s, hs0, hsl⟩ := exists_chiefSeries _ _ hle
  have hc : IsCentral s.head s.last := by
    rw [hs0, hsl]
    exact residual_stratum_central d hUT hf hLI
  exact ⟨s, hs0, hsl, fun i => hc.subinterval
    (CompositionSeries.head_le i.castSucc) (CompositionSeries.le_last i.succ),
    s.noncentralTwoCount_eq_zero_of_central hc⟩

section Accounting
variable (d : Hypothesis D F n g h)
  (hUT : D.U ≤ D.T) (hfrattini : (frattini D.U).map D.U.subtype ≤ D.V₁)
  (hLI : D.L ≤ I D g h)
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) D.L₁ W)
  {l : ℕ} (f : Filtration D.L₁ l) (m : Fin l → ℕ) (a : Fin l)
  (hlower : f.term a.castSucc = residualCentralLower d)
  (hupper : f.term a.succ = residualCentralUpper d hUT hfrattini hLI)
  (hzero : m a = 0)
  (hstrata : ∀ i, i ≠ a → IsModuleStratum ρ (f.term i.castSucc) (f.term i.succ) (m i))

include hlower hupper hzero hstrata

/-- G.2.5(5) supplies the central slot in the actual L₁ filtration. Only the
other slots require supplied equivariant section coordinates. -/
theorem residual_filtration_strata :
    ∀ i, IsModuleStratum ρ (f.term i.castSucc) (f.term i.succ) (m i) := by
  intro i
  by_cases hi : i = a
  · subst i
    rw [hlower, hupper]
    exact Or.inl ⟨residual_stratum_central d hUT hfrattini hLI, hzero⟩
  · exact hstrata i hi

variable [Representation.IsIrreducible ρ] (hρ : ∃ k v, ρ k v ≠ v)
  (hfirst : f.term 0 = ⊥) (hcore : (f.term (Fin.last l)).val = pCore 2 D.L₁)
  (hterminal : HasNoTwoChiefFactors (D.L₁ ⧸ pCore 2 D.L₁))

include hρ hfirst hcore hterminal

/-- Chief-factor accounting for the genuine local residual L₁. The normal
filtration runs from 1 to its literal two-core and contains the central
`(S₂∩L₁)/(V∩L₁)` stratum proved by G.2.5(5). The other strata and the precise
terminal quotient property remain source inputs, not assumed chief counts.

The result constructs a complete refinement, computes the count in every
complete chief series, and identifies the actual conjugation action on every
noncentral two-chief interval. The parent G.2.5(8) assembly must construct the
remaining strata and identify the sum of their multiplicities with r+s+2. -/
theorem residual_chief_accounting :
    (∃ (s : ChiefSeries D.L₁) (ι : Fin (l + 1) →o Fin (s.length + 1)),
      (∀ i, s (ι i) = f.term i) ∧ ι 0 = 0 ∧ s.head = ⊥ ∧ s.last = ⊤ ∧
      s.noncentralTwoCount = ∑ i, m i ∧
      ∀ i : Fin s.length, IsNoncentralTwo (s i.castSucc) (s i.succ) →
        Nonempty (SectionCoordinates (s i.castSucc) (s i.succ) ρ 1)) ∧
    (∀ s : ChiefSeries D.L₁, s.head = ⊥ → s.last = ⊤ →
      s.noncentralTwoCount = ∑ i, m i) ∧
    ∀ A B : NormalNode D.L₁, ChiefFactor.IsChief B.val A.val →
      IsPGroup 2 (Section A B) → ¬ IsCentral A B →
        Nonempty (SectionCoordinates A B ρ 1) := by
  have hs := residual_filtration_strata d hUT hfrattini hLI ρ f m a
    hlower hupper hzero hstrata
  have ht : HasNoTwoChiefFactors (D.L₁ ⧸ (f.term (Fin.last l)).val) := by
    have he : f.term (Fin.last l) =
        (⟨pCore 2 D.L₁, inferInstanceAs (pCore 2 D.L₁).Normal⟩ : NormalNode D.L₁) := Subtype.ext hcore
    rw [he]
    exact hterminal
  refine ⟨f.exists_complete_marked_refinement m hs hρ hfirst ht, ?_, ?_⟩
  · intro s hs0 hsl
    exact (f.complete_series_accounting m hs hρ hfirst ht s hs0 hsl).1
  · exact f.chief_factor_coordinates m hs hρ hfirst ht

end Accounting

end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors
