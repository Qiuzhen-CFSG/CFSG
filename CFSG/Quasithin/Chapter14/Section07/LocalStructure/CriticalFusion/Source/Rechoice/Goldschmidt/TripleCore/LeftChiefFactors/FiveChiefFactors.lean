module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.SourceBorel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.ResidualComparison
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.BorelRefinements.SourceChief
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.CriticalIntersections.Construction


/-!
# Five noncentral binary chief factors on the original left residual

The three Borel-action refinements contribute two factors on U/V₁, two on
Q_H/C_H(U), and one above Q_H. Refine the two remaining intervals and
concatenate all five series. Counts add, so additional factors cannot spoil
the lower bound. Equivariant Jordan–Hölder gives the bound on every complete
series and on a refinement retaining the entire original source filtration.

The literal actor equivalence transports this bound to the left vertex in I.
Restriction to its two-residual and the original inclusion into G then give
at least five factors for the original L₁. The residual comparison already
proves survival of the noncentral action; no extra survival premise occurs.

The source adapter constructs the compatible Borel and SectionCentralizer from
the original upper marking and the genuine earlier structural and uniqueness
implications, then constructs the duality on the literal centralizer sections.
Constructing that marking and [U,Q_H]=V₁ remains with the corresponding source
producers and the final assembly owner. No chief count, nontrivial core of I,
or later 14.7.71 conclusion is assumed.

Source: Aschbacher–Smith, Lemma 14.7.70, printed p.1074 (PDF p.1091).
-/

public section
noncomputable section
open Subgroup NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors
open Chapter12.Section08 BorelRefinements
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

local notation "B" => (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)

private theorem five_of_source_intervals (hc : d.SectionCentralizer)
    (hnat : ∃ s : ChiefSeries B, s.head = sourcePointNode (F := F) (L := L) ∧
      s.last = sourceUNode d ∧ 2 ≤ s.noncentralTwoCount)
    (hdual : ∃ s : ChiefSeries B, s.head = sourceCentralizerNode d ∧
      s.last = sourceQNode (F := F) (L := L) ∧ 2 ≤ s.noncentralTwoCount)
    (hcore : ∃ s : ChiefSeries B, s.head = sourceQNode (F := F) (L := L) ∧
      s.last = ⊤ ∧ 1 ≤ s.noncentralTwoCount) :
    ∃ s : ChiefSeries B, s.head = ⊥ ∧ s.last = ⊤ ∧ 5 ≤ s.noncentralTwoCount := by
  obtain ⟨a, ha0, ha1, ha⟩ := hnat
  obtain ⟨b, hb0, hb1, hb⟩ := hdual
  obtain ⟨c, hc0, hc1, hcc⟩ := hcore
  obtain ⟨p, hp0, hp1⟩ := exists_chiefSeries (⊥ : NormalNode B)
    (sourcePointNode (F := F) (L := L)) bot_le
  obtain ⟨q, hq0, hq1⟩ := exists_chiefSeries (sourceUNode d)
    (sourceCentralizerNode d) (fun _ hx => (source_filtration_containments d hc).2.1 hx)
  have hpa : p.last = a.head := hp1.trans ha0.symm
  have hpaq : (p.smash a hpa).last = q.head :=
    (RelSeries.last_smash hpa).trans (ha1.trans hq0.symm)
  have hpaqb : ((p.smash a hpa).smash q hpaq).last = b.head :=
    (RelSeries.last_smash hpaq).trans (hq1.trans hb0.symm)
  have hpaqbc : (((p.smash a hpa).smash q hpaq).smash b hpaqb).last = c.head :=
    (RelSeries.last_smash hpaqb).trans (hb1.trans hc0.symm)
  refine ⟨(((p.smash a hpa).smash q hpaq).smash b hpaqb).smash c hpaqbc, ?_, ?_, ?_⟩
  · exact (RelSeries.head_smash hpaqbc).trans ((RelSeries.head_smash hpaqb).trans
      ((RelSeries.head_smash hpaq).trans ((RelSeries.head_smash hpa).trans hp0)))
  · exact (RelSeries.last_smash hpaqbc).trans hc1
  · rw [ChiefSeries.noncentralTwoCount_smash, ChiefSeries.noncentralTwoCount_smash,
      ChiefSeries.noncentralTwoCount_smash, ChiefSeries.noncentralTwoCount_smash]
    omega

variable {X Y : Type u} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

/-- Every complete chief series of the actual L₁T has the five contributions. -/
theorem sourceChief_count (h : CompatibleBorel d) (hc : d.SectionCentralizer)
    (duality : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (s : ChiefSeries B) (hs0 : s.head = ⊥) (hs1 : s.last = ⊤) :
    5 ≤ s.noncentralTwoCount := by
  obtain ⟨hnat, hdual, hcore⟩ := sourceChief_refinement_family d h hc duality hcomm
  obtain ⟨t, ht0, ht1, ht⟩ := five_of_source_intervals d hc hnat hdual hcore
  rw [s.noncentralTwoCount_eq t (hs0.trans ht0.symm) (hs1.trans ht1.symm)]
  exact ht

/-- The same lower bound retains all six original filtration nodes in order. -/
theorem exists_five_source_refinement (h : CompatibleBorel d) (hc : d.SectionCentralizer)
    (duality : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    ∃ (s : ChiefSeries B) (ι : Fin 6 →o Fin (s.length + 1)),
      (∀ i, s (ι i) = (sourceFiltration d hc).term i) ∧
      ι 0 = 0 ∧ ι (Fin.last 5) = Fin.last s.length ∧
      s.head = ⊥ ∧ s.last = ⊤ ∧ 5 ≤ s.noncentralTwoCount := by
  obtain ⟨s, ι, hi, hi0, hi1, hs0, hs1⟩ := exists_complete_source_refinement d hc
  exact ⟨s, ι, hi, hi0, hi1, hs0, hs1, sourceChief_count d h hc duality hcomm s hs0 hs1⟩

/-- Transfer the count to the literal left vertex of the Goldschmidt triple. -/
theorem leftChief_count (c : CriticalPath (L := L) F)
    (h : CompatibleBorel d) (hc : d.SectionCentralizer)
    (duality : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (s : ChiefSeries (left c)) (hs0 : s.head = ⊥) (hs1 : s.last = ⊤) :
    5 ≤ s.noncentralTwoCount := by
  let e := (sourceToLeftEquiv c).symm
  obtain ⟨ht0, ht1⟩ := s.mapActor_complete e hs0 hs1
  have ht := sourceChief_count d h hc duality hcomm (s.mapActor e) ht0 ht1
  exact ht.trans_eq (s.mapActor_noncentralTwoCount e)

/-- Restriction to the actual two-residual gives the source bound for L₁. -/
theorem originalChief_count (c : CriticalPath (L := L) F)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (h : CompatibleBorel d) (hc : d.SectionCentralizer)
    (duality : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (t : ChiefSeries (F.Li L 1)) (ht0 : t.head = ⊥) (ht1 : t.last = ⊤) :
    5 ≤ t.noncentralTwoCount := by
  obtain ⟨s, hs0, hs1⟩ := exists_chiefSeries (⊥ : NormalNode B) ⊤ bot_le
  have hs := sourceChief_count d h hc duality hcomm s hs0 hs1
  obtain ⟨r, hr0, hr1, hr, _⟩ := source_series_original d c structural s hs0 hs1
  rw [t.noncentralTwoCount_eq r (ht0.trans hr0.symm) (ht1.trans hr1.symm)]
  exact hs.trans hr

/-- The earlier source setup discharges Borel compatibility and the section kernel. -/
theorem originalChief_count_of_upperMarking (c : CriticalPath (L := L) F)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Chapter12.Section08.Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (mark : LocalGeometry.Preparation.UpperMarking d)
    (duality : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (t : ChiefSeries (F.Li L 1)) (ht0 : t.head = ⊥) (ht1 : t.last = ⊤) :
    5 ≤ t.noncentralTwoCount :=
  originalChief_count d c structural (compatibleBorel_of_upperMarking d structural mark)
    (d.sectionCentralizer_of_earlier_setup structural uniqueness) duality hcomm t ht0 ht1

/-- The source kernel constructs the duality, leaving only the actual marking
and independent nontrivial commutator identity beyond the earlier setup. -/
theorem originalChief_count_of_source (c : CriticalPath (L := L) F)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Chapter12.Section08.Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (mark : LocalGeometry.Preparation.UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (t : ChiefSeries (F.Li L 1)) (ht0 : t.head = ⊥) (ht1 : t.last = ⊤) :
    5 ≤ t.noncentralTwoCount := by
  have hc := d.sectionCentralizer_of_earlier_setup structural uniqueness
  obtain ⟨X, aX, mX, hs⟩ := CriticalIntersections.exists_sourceDuality d hc
  let := aX
  let := mX
  obtain ⟨duality⟩ := hs
  exact originalChief_count_of_upperMarking d c structural uniqueness mark duality hcomm t ht0 ht1

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors
