module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.DualNatural
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice
public import Theory.GroupTheory.NoncentralChiefRefinement.Accounting

/-!
# The literal normal filtration for the left chief-factor calculation

The original point, U, C_H(U), and Q_H are normal in the actual group L₁T.
They form the source chain, completed by 1 and L₁T. Finite normal-lattice
refinement supplies a complete chief series containing every one of these
terms, with its literal conjugation sections. No factor count is assumed.
The Borel calculations and residual comparison must still prove the five
noncentral contributions for this filtration and the original L₁ actor.

SectionCentralizer is the precise earlier 14.5.15(4) input (qt-14-05).
This branch and TripleCore share the original Source.FixedCoordinates API.
Final five-factor assembly remains with
qt-14-07-rechoice-left-chief-factors.

Source: Aschbacher–Smith, 14.7.70, printed p.1074 (PDF p.1091).
-/

@[expose] public section
noncomputable section
open Subgroup NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

local notation "B" => (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)

/-- The original point, as a normal subgroup of L₁T. -/
def sourcePointNode : NormalNode B :=
  ⟨(F.Vi 1).subgroupOf B, normal_subgroupOf_of_le_normalizer group_le_H⟩

/-- The original U, with the same ambient conjugation action restricted to L₁T. -/
def sourceUNode : NormalNode B :=
  ⟨F.U.subgroupOf B, normal_subgroupOf_of_le_normalizer
    (group_le_H.trans d.conjugationSection.normalized)⟩

/-- The source denominator C_H(U), retained as a relative subgroup. -/
def sourceCentralizerNode : NormalNode B :=
  ⟨(F.H ⊓ centralizer (F.U : Set G)).subgroupOf B,
    normal_subgroupOf_of_le_normalizer ((le_inf
      (group_le_H.trans F.H.le_normalizer)
      ((group_le_H.trans d.conjugationSection.normalized).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf)⟩

/-- The intrinsic core of H, embedded and then restricted to the left group. -/
def sourceQNode : NormalNode B := by
  have hn : F.H ≤ normalizer (F.H.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pCore 2 F.H).le_normalizer_map F.H.subtype
  exact ⟨(F.H.pCoreIn 2).subgroupOf B,
    normal_subgroupOf_of_le_normalizer (group_le_H.trans hn)⟩

/-- The complete coarse source filtration. Its noncentral factor count is
not part of this definition or its assumptions. -/
def sourceFiltration (hc : d.SectionCentralizer) : Filtration B 5 where
  term := ![⊥, sourcePointNode (F := F) (L := L), sourceUNode d,
    sourceCentralizerNode d, sourceQNode (F := F) (L := L), ⊤]
  monotone := by
    obtain ⟨hZU, hUC, hCQ, _⟩ := source_filtration_containments d hc
    rw [Fin.monotone_iff_le_succ]
    intro i
    fin_cases i
    · exact bot_le
    · exact fun _ hx => hZU hx
    · exact fun _ hx => hUC hx
    · exact fun _ hx => hCQ hx
    · exact le_top

/-- An actual complete chief series containing the original normal sections,
ready for the independent Borel-action contributions. -/
theorem exists_complete_source_refinement (hc : d.SectionCentralizer) :
    ∃ (s : ChiefSeries B) (ι : Fin 6 →o Fin (s.length + 1)),
      (∀ i, s (ι i) = (sourceFiltration d hc).term i) ∧
      ι 0 = 0 ∧ ι (Fin.last 5) = Fin.last s.length ∧
      s.head = ⊥ ∧ s.last = ⊤ := by
  obtain ⟨s, ι, hi, h0, hlast⟩ := exists_refinement (sourceFiltration d hc)
  refine ⟨s, ι, hi, h0, hlast, ?_, ?_⟩
  · have h := hi 0
    rw [h0] at h
    exact h
  · have h := hi (Fin.last 5)
    rw [hlast] at h
    exact h

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors
