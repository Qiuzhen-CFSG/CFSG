module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.HAccounting.CentralIntervals
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.HAccounting.SymmetricQuotient
public import Theory.GroupTheory.NoncentralChiefRefinement.CentralChiefStrata

/-!
# Exact H-chief accounting for 14.7.71(1)

Refine the actual normal filtration
`1 ≤ U₀ ≤ U ≤ C_H(U) ≤ Q_K ≤ O₂(H) ≤ H`.
The two marked steps have the original natural H-action. Every binary chief
factor in each complementary interval is central, including those in the
terminal S₅ quotient. Concatenation gives exactly two noncentral binary
factors; equivariant Jordan–Hölder supplies their coordinates in every
complete series and on every actual noncentral binary chief interval.

The final source applications construct the dual witness from 14.5.21,
retaining the original natural projection and functional commutator formula.
No equality U₀ = V₁ or elementary abelian structure on C_H(U)/U is used.
Source: Aschbacher–Smith, 14.7.71(1), printed p.1075 (PDF p.1092).
-/

public section
noncomputable section
open Subgroup Representation NoncentralChiefRefinement
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.HAccounting
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- Multiplicities will be justified by the literal section coordinates and
centrality of all complementary binary chief intervals. -/
@[expose] def sourceMultiplicities : Fin 6 → ℕ := ![0, 1, 0, 1, 0, 0]

/-- Each step in the original filtration has the asserted module structure
or only central binary chief sections. -/
theorem source_strata (c : CriticalPath (L := L) F) (e : Earlier d c)
    (b : QKDualCoordinates d) (i : Fin 6) :
    IsChiefModuleStratum (naturalAction d)
      ((sourceFiltration d e.sectionCentralizer b).term i.castSucc)
      ((sourceFiltration d e.sectionCentralizer b).term i.succ)
      (sourceMultiplicities i) := by
  fin_cases i
  · exact Or.inl ⟨fun A B _ hB hAB hp => isCentral_of_fixedNode d A B hAB hp hB, rfl⟩
  · exact Or.inr ⟨naturalChiefCoordinates d⟩
  · exact Or.inl ⟨fun A B hA hB hAB hp => isCentral_of_cNode d c e A B hAB hp hA hB, rfl⟩
  · exact Or.inr ⟨naturalDualChiefCoordinates d b⟩
  · exact Or.inl ⟨fun A B hA hB hAB hp =>
      isCentral_of_coreNode d c e b A B hAB hp hA hB, rfl⟩
  · exact Or.inl ⟨fun _ _ hA _ hAB hp => isCentral_above_core d hAB hA hp, rfl⟩

/-- A complete actual H-chief series retaining all seven source terms has
exactly the two natural noncentral binary factors. -/
theorem exists_marked_source_refinement (c : CriticalPath (L := L) F)
    (e : Earlier d c) (b : QKDualCoordinates d) :
    ∃ (s : ChiefSeries F.H) (ι : Fin 7 →o Fin (s.length + 1)),
      (∀ i, s (ι i) = (sourceFiltration d e.sectionCentralizer b).term i) ∧
      ι 0 = 0 ∧ ι (Fin.last 6) = Fin.last s.length ∧
      s.head = ⊥ ∧ s.last = ⊤ ∧ s.noncentralTwoCount = 2 ∧
      ∀ i : Fin s.length, IsNoncentralTwo (s i.castSucc) (s i.succ) →
        Nonempty (SectionCoordinates (s i.castSucc) (s i.succ) (naturalAction d) 1) := by
  let := naturalAction_irreducible d
  obtain ⟨s, ι, hi, hi0, hi1, hs0, hs1, hcount, hcoord⟩ :=
    (sourceFiltration d e.sectionCentralizer b).exists_chief_strata_refinement
      sourceMultiplicities (source_strata d c e b) (naturalAction_nontrivial d)
  refine ⟨s, ι, hi, hi0, hi1, hs0, hs1, ?_, hcoord⟩
  simpa [sourceMultiplicities, Fin.sum_univ_succ] using hcount

/-- Equivariant Jordan–Hölder transfers the exact count and the original
natural action to every complete H-chief series. -/
theorem complete_series_accounting_of_coordinates (c : CriticalPath (L := L) F)
    (e : Earlier d c) (b : QKDualCoordinates d)
    (t : ChiefSeries F.H) (ht0 : t.head = ⊥) (ht1 : t.last = ⊤) :
    t.noncentralTwoCount = 2 ∧
      ∀ i : Fin t.length, IsNoncentralTwo (t i.castSucc) (t i.succ) →
        Nonempty (SectionCoordinates (t i.castSucc) (t i.succ) (naturalAction d) 1) := by
  obtain ⟨s, _, _, _, _, hs0, hs1, hcount, hcoord⟩ :=
    exists_marked_source_refinement d c e b
  obtain ⟨hc, ha⟩ := s.marked_of_same_endpoints t (hs0.trans ht0.symm)
    (hs1.trans ht1.symm) hcoord
  exact ⟨hc.trans hcount, ha⟩

/-- Retaining the literal source terms retains the two marked chief
intervals as actual adjacent steps, in their original order. -/
theorem marked_steps_of_source_refinement (hc : d.SectionCentralizer)
    (b : QKDualCoordinates d) (s : ChiefSeries F.H)
    (ι : Fin 7 →o Fin (s.length + 1))
    (hι : ∀ i, s (ι i) = (sourceFiltration d hc b).term i) :
    ∃ i j : Fin s.length, i < j ∧
      s i.castSucc = fixedNode d ∧ s i.succ = uNode d ∧
      s j.castSucc = cNode d ∧ s j.succ = qKNode d b := by
  have hn := (covBy_iff_isChief (fixedNode d) (uNode d)).mpr (natural_chief d)
  have hd := (covBy_iff_isChief (cNode d) (qKNode d b)).mpr (dual_chief d b)
  obtain ⟨i, hi0, hi1⟩ := s.exists_step_of_covBy _ _ hn (ι 1) (ι 2) (hι 1) (hι 2)
  obtain ⟨j, hj0, hj1⟩ := s.exists_step_of_covBy _ _ hd (ι 3) (ι 4) (hι 3) (hι 4)
  refine ⟨i, j, ?_, hi0, hi1, hj0, hj1⟩
  have hlt : s i.castSucc < s j.castSucc := by
    rw [hi0, hj0]
    exact hn.lt.trans_le (uNode_le_cNode d)
  exact s.strictMono.lt_iff_lt.mp hlt

/-- Every complete H-chief series has two distinguished, distinct factors,
matched equivariantly to the literal U/U₀ and Q_K/C_H(U) sections. These are
exactly its noncentral binary factors. -/
theorem complete_series_representatives (c : CriticalPath (L := L) F)
    (e : Earlier d c) (b : QKDualCoordinates d)
    (t : ChiefSeries F.H) (ht0 : t.head = ⊥) (ht1 : t.last = ⊤) :
    ∃ i j : Fin t.length, i ≠ j ∧
      Nonempty (SectionEquiv (t i.castSucc) (t i.succ) (fixedNode d) (uNode d)) ∧
      Nonempty (SectionEquiv (t j.castSucc) (t j.succ) (cNode d) (qKNode d b)) ∧
      ∀ k : Fin t.length, IsNoncentralTwo (t k.castSucc) (t k.succ) ↔ k = i ∨ k = j := by
  obtain ⟨s, ι, hι, _, _, hs0, hs1, hcount, _⟩ :=
    exists_marked_source_refinement d c e b
  obtain ⟨i, j, hij, hi0, hi1, hj0, hj1⟩ :=
    marked_steps_of_source_refinement d e.sectionCentralizer b s ι hι
  obtain ⟨a, ha⟩ := t.exists_sectionEquiv_matching s (ht0.trans hs0.symm)
    (ht1.trans hs1.symm)
  have hi : Nonempty (SectionEquiv (t (a.symm i).castSucc) (t (a.symm i).succ)
      (fixedNode d) (uNode d)) := by
    simpa only [Equiv.apply_symm_apply, hi0, hi1] using ha (a.symm i)
  have hj : Nonempty (SectionEquiv (t (a.symm j).castSucc) (t (a.symm j).succ)
      (cNode d) (qKNode d b)) := by
    simpa only [Equiv.apply_symm_apply, hj0, hj1] using ha (a.symm j)
  have hne : a.symm i ≠ a.symm j := fun h => hij.ne (a.symm.injective h)
  have hc : t.noncentralTwoCount = 2 :=
    (t.noncentralTwoCount_eq_of_matching s a ha).trans hcount
  obtain ⟨fi⟩ := hi
  obtain ⟨fj⟩ := hj
  exact ⟨a.symm i, a.symm j, hne, ⟨fi⟩, ⟨fj⟩,
    t.noncentralTwo_iff_eq_or_eq hc _ _ hne
      (fi.isNoncentralTwo_iff.mpr (natural_noncentral_two d))
      (fj.isNoncentralTwo_iff.mpr (dual_noncentral_two d b))⟩

/-- Both noncentral factors already occur below the actual two-core. -/
theorem core_series_count (c : CriticalPath (L := L) F)
    (e : Earlier d c) (b : QKDualCoordinates d)
    (s : ChiefSeries F.H) (hs0 : s.head = ⊥) (hs1 : s.last = coreNode d) :
    s.noncentralTwoCount = 2 := by
  obtain ⟨t, ht0, ht1⟩ := exists_chiefSeries (coreNode d) ⊤ le_top
  have hst := hs1.trans ht0.symm
  have hc := (complete_series_accounting_of_coordinates d c e b (s.smash t hst)
    ((RelSeries.head_smash hst).trans hs0) ((RelSeries.last_smash hst).trans ht1)).1
  rw [ChiefSeries.noncentralTwoCount_smash, terminal_noncentralTwoCount d t ht0.ge,
    add_zero] at hc
  exact hc

/-- The literal O₂(H)/C_H(U) interval has just the one natural noncentral
binary factor, represented on Q_K/C_H(U). -/
theorem centralizer_core_accounting (c : CriticalPath (L := L) F)
    (e : Earlier d c) (b : QKDualCoordinates d)
    (t : ChiefSeries F.H) (ht0 : t.head = cNode d) (ht1 : t.last = coreNode d) :
    t.noncentralTwoCount = 1 ∧
      ∀ i : Fin t.length, IsNoncentralTwo (t i.castSucc) (t i.succ) →
        Nonempty (SectionCoordinates (t i.castSucc) (t i.succ) (naturalAction d) 1) := by
  let := naturalAction_irreducible d
  let f : Filtration F.H 2 :=
    ⟨![cNode d, qKNode d b, coreNode d], by
      apply Fin.monotone_iff_le_succ.mpr
      intro i
      fin_cases i
      · exact cNode_le_qKNode d b
      · exact qKNode_le_coreNode d e.sectionCentralizer b⟩
  have hf : ∀ i : Fin 2, IsChiefModuleStratum (naturalAction d)
      (f.term i.castSucc) (f.term i.succ) (![1, 0] i) := by
    intro i
    fin_cases i
    · exact Or.inr ⟨naturalDualChiefCoordinates d b⟩
    · exact Or.inl ⟨fun A B hA hB hAB hp =>
        isCentral_of_coreNode d c e b A B hAB hp hA hB, rfl⟩
  obtain ⟨s, _, _, _, _, hs0, hs1, hc, ha⟩ :=
    f.exists_chief_strata_refinement ![1, 0] hf (naturalAction_nontrivial d)
  obtain ⟨he, hcoord⟩ := s.marked_of_same_endpoints t (hs0.trans ht0.symm)
    (hs1.trans ht1.symm) ha
  refine ⟨he.trans ?_, hcoord⟩
  simpa [Fin.sum_univ_succ] using hc

/-- All actual noncentral binary chief intervals, whether or not originally
chosen in the source filtration, carry the same natural H-action. -/
theorem chief_factor_coordinates_of_coordinates (c : CriticalPath (L := L) F)
    (e : Earlier d c) (b : QKDualCoordinates d)
    (A B : NormalNode F.H) (hAB : ChiefFactor.IsChief B.val A.val)
    (hp : IsPGroup 2 (Section A B)) (hn : ¬ IsCentral A B) :
    Nonempty (SectionCoordinates A B (naturalAction d) 1) := by
  obtain ⟨s, hs0, hs1, i, hi0, hi1⟩ :=
    exists_complete_chiefSeries_containing A B ((covBy_iff_isChief A B).mpr hAB)
  have ha := (complete_series_accounting_of_coordinates d c e b s hs0 hs1).2 i
  rw [hi0, hi1] at ha
  exact ha ⟨hp, hn⟩

variable {X Y : Type u} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

/-- Source 14.7.71(1), with the dual-coordinate premise discharged using
precisely the earlier duality and commutator identity from 14.5.21. -/
theorem complete_series_accounting (c : CriticalPath (L := L) F) (e : Earlier d c)
    (duality : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (t : ChiefSeries F.H) (ht0 : t.head = ⊥) (ht1 : t.last = ⊤) :
    t.noncentralTwoCount = 2 ∧
      ∀ i : Fin t.length, IsNoncentralTwo (t i.castSucc) (t i.succ) →
        Nonempty (SectionCoordinates (t i.castSucc) (t i.succ) (naturalAction d) 1) := by
  obtain ⟨b⟩ := exists_qKDualCoordinates d e.sectionCentralizer duality hcomm
  exact complete_series_accounting_of_coordinates d c e b t ht0 ht1

/-- Construct the original dual witness once, then identify exactly the
two literal representatives in every complete series. This also supplies the
witness consumed independently by the Q_K-placement branch. -/
theorem source_representatives (c : CriticalPath (L := L) F) (e : Earlier d c)
    (duality : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    ∃ b : QKDualCoordinates d,
      ∀ (t : ChiefSeries F.H), t.head = ⊥ → t.last = ⊤ →
        ∃ i j : Fin t.length, i ≠ j ∧
          Nonempty (SectionEquiv (t i.castSucc) (t i.succ) (fixedNode d) (uNode d)) ∧
          Nonempty (SectionEquiv (t j.castSucc) (t j.succ) (cNode d) (qKNode d b)) ∧
          ∀ k : Fin t.length, IsNoncentralTwo (t k.castSucc) (t k.succ) ↔ k = i ∨ k = j := by
  obtain ⟨b⟩ := exists_qKDualCoordinates d e.sectionCentralizer duality hcomm
  exact ⟨b, complete_series_representatives d c e b⟩

/-- The source inputs also give the natural coordinates on an arbitrary
actual noncentral binary chief interval, without assuming a dual witness. -/
theorem chief_factor_coordinates (c : CriticalPath (L := L) F) (e : Earlier d c)
    (duality : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (A B : NormalNode F.H) (hAB : ChiefFactor.IsChief B.val A.val)
    (hp : IsPGroup 2 (Section A B)) (hn : ¬ IsCentral A B) :
    Nonempty (SectionCoordinates A B (naturalAction d) 1) := by
  obtain ⟨b⟩ := exists_qKDualCoordinates d e.sectionCentralizer duality hcomm
  exact chief_factor_coordinates_of_coordinates d c e b A B hAB hp hn

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.HAccounting
