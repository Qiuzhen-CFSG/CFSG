module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianGeometry

/-!
# Excluding the natural A₇ row in 12.9.4

The source geometry supplies every premise of the concrete seven-point
calculation, including detection of the conjugate center. This excludes
G.11.2(4) for the original nonabelian point action. The corrected catalogue
therefore leaves only the split orthogonal six-space, in degree four.
The final application selects the original flag and adjacent conjugator.
Catalogue exhaustion and the orthogonal contradiction remain obligations
of the natural-branch assembly; no catalogue theorem is asserted here.

Source: Aschbacher--Smith 12.8.13(6) and 12.9.4, printed pp.856,859.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- The natural A₇ row is excluded from the original nonabelian point action.
The actual transvections, fixed space, rank and terminal center detection
are all proved from the higher-rank source hypotheses. -/
theorem nonabelian_not_caseFour
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ¬ ChapterG.Section11.CaseFour F.terminalRepresentation := by
  rintro ⟨_,eK,eV,he⟩
  obtain ⟨hX,B,v,hB,hAlt,hInv,hv,hline,hXT,hiso,htrans,_,hfixed,hWX,hperp,hrank⟩ :=
    nonabelian_transvection_geometry h earlier F hne g hgP hgH
  let := hX
  refine F.sevenModel_excluded g (generalizedFitting F.TerminalHdot) eK eV he
    B hB hInv v hv hline hXT (sylow_fixes_plane_hat_point F v hv hline)
    hiso ?_ hfixed hWX hperp hrank ?_
  · intro x hx e he
    obtain ⟨φ,_,hφ⟩ := htrans ⟨x,hx⟩
    rw [hφ ⟨e,he⟩,add_sub_cancel_left,hline]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · exact nonabelian_conjugate_center_detected h hn earlier F hne g hgP hgH v hline

/-- In the original nonabelian branch the corrected catalogue now leaves
only the split orthogonal six-space, in degree four. Catalogue construction
and the orthogonal source argument remain with the natural-branch owner. -/
theorem nonabelian_corrected_catalogue_orthogonal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (W : Submodule (ZMod 2) (Additive F.Uhat))
    (X : Subgroup F.TerminalHdot) (X₀ : Subgroup X)
    (hc : ChapterG.Section11.FullLinearFour.ConclusionWithFullLinearFour
      F.terminalRepresentation B v W X X₀) :
    n = 4 ∧ ChapterG.Section11.CaseFive F.terminalRepresentation B := by
  obtain ⟨hd,h4 | h5⟩ := nonabelian_corrected_catalogue_six_space h hn earlier F hne B v W X X₀ hc
  · exact (nonabelian_not_caseFour h hn earlier F hne g hgP hgH h4).elim
  · exact ⟨hd,h5⟩


/-- Select the source flag and its actual omitted-point conjugator. The
natural A₇ action is excluded for this flag whenever its point span is
nonabelian; no flag, conjugator or terminal detection premise is assumed. -/
theorem exists_flag_not_caseFour
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple) :
    ∃ (F : InvariantFlag T V n) (g : G), g ∈ F.P L ∧ g ∉ F.H ∧
      ∀ hne : ¬ IsMulCommutative F.U,
        let := nonabelian_hat_elementary h earlier F hne
        ¬ ChapterG.Section11.CaseFour F.terminalRepresentation := by
  obtain ⟨_,F,_,_,_,_,g,hgP,hgH⟩ := h.exists_flag_geometry earlier.structural
  refine ⟨F,g,hgP,hgH,?_⟩
  intro hne
  let := nonabelian_hat_elementary h earlier F hne
  exact nonabelian_not_caseFour h hn earlier F hne g hgP hgH

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
