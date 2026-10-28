module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Escaping.Inputs

/-!
# Constructing the terminal configuration

The construction below is the formal version of the final paragraph on p.822.
The local source supplies the H-star member, its `O²` subgroup and supplement,
the G.2.2 setup, and the escaping conjugate.  G.2.2 itself supplies the
two-group property of the H-span; all other fields are transported to the
literal definitions in `Terminal.lean`.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}

namespace SylowExteriorMarking

variable (s : SylowExteriorMarking D)

/-- Transport the G.2.2 two-group conclusion to the literal `U_H`. -/
theorem escaping_span_isPGroup
    {h : Hypothesis1223 KnownSimple.IsKnownSimple T L}
    (e : s.EscapingSource h) : IsPGroup 2 (s.marking.UH e.H) := by
  rw [← e.span_eq]
  exact e.g2.U_isPGroup

theorem escaping_B_commutator
    {h : Hypothesis1223 KnownSimple.IsKnownSimple T L}
    (e : s.EscapingSource h) :
    ⁅s.marking.UH e.H, s.escapingB e⁆ ≤ s.marking.Vi 1 := by
  change ⁅s.marking.UH e.H,
      V.map (MulAut.conj e.g).toMonoidHom ⊓
        (s.marking.Li 1 ⊔ e.H).pCoreIn 2⁆ ≤ s.marking.Vi 1
  exact e.commutator_line

theorem escaping_B_corank_le_two
    {h : Hypothesis1223 KnownSimple.IsKnownSimple T L}
    (e : s.EscapingSource h) :
    ChapterE.subgroupCorank (s.escapingA e) (s.escapingB e) ≤ 2 := by
  change ChapterE.subgroupCorank (V.map (MulAut.conj e.g).toMonoidHom)
      (V.map (MulAut.conj e.g).toMonoidHom ⊓
        (s.marking.Li 1 ⊔ e.H).pCoreIn 2) ≤ 2
  exact e.corank_le_two

theorem escaping_B_corank_lt_globalS
    {h : Hypothesis1223 KnownSimple.IsKnownSimple T L}
    (e : s.EscapingSource h) :
    let := D.elementary
    let := IsElementaryAbelian.map (p := 2) (A := V)
      (MulAut.conj e.g).toMonoidHom
    (ChapterE.subgroupCorank (V.map (MulAut.conj e.g).toMonoidHom)
      (V.map (MulAut.conj e.g).toMonoidHom ⊓
        (s.marking.Li 1 ⊔ e.H).pCoreIn 2) : ℕ∞) <
      ChapterE.globalS (V.map (MulAut.conj e.g).toMonoidHom) := by
  exact e.corank_lt_globalS

/-- The actual source record yields the exact terminal configuration consumed
by the commutator contradiction. -/
theorem terminalConfiguration_of_escapingSource
    {h : Hypothesis1223 KnownSimple.IsKnownSimple T L}
    (e : s.EscapingSource h) :
    Nonempty (TerminalConfiguration s.marking) := by
  let A := s.escapingA e
  let Q := s.escapingQ e
  let := D.elementary
  let : IsElementaryAbelian 2 A := by
    change IsElementaryAbelian 2 (V.map (MulAut.conj e.g).toMonoidHom)
    exact IsElementaryAbelian.map (p := 2) (A := V)
      (MulAut.conj e.g).toMonoidHom
  have hA_le : A ≤ e.H := by
    simpa [A, escapingA] using e.A_le_H
  have hescape : ¬ A ≤ e.H.pCoreIn 2 := by
    simpa [A, escapingA] using e.escapes_core
  have hnorm : s.marking.UH e.H ≤ normalizer (A : Set G) := by
    simpa [A, escapingA] using e.span_normalizes
  have hcomm : ⁅s.marking.UH e.H, A ⊓ Q⁆ ≤ s.marking.Vi 1 := by
    change ⁅s.marking.UH e.H,
        V.map (MulAut.conj e.g).toMonoidHom ⊓
          (escapingH₁ s e.H).pCoreIn 2⁆ ≤ s.marking.Vi 1
    simpa [escapingH₁] using e.commutator_line
  have hsmall :
      let := D.elementary
      let := IsElementaryAbelian.map (p := 2) (A := V)
        (MulAut.conj e.g).toMonoidHom
      (ChapterE.subgroupCorank A (A ⊓ Q) : ℕ∞) < ChapterE.globalS A := by
    simpa [A, Q, escapingA, escapingQ, escapingH₁] using e.corank_lt_globalS
  have hkernel : e.H ⊓ centralizer (s.marking.UH e.H : Set G) ≤ Q := by
    change e.H ⊓ centralizer (s.marking.UH e.H : Set G) ≤
      (escapingH₁ s e.H).pCoreIn 2
    simpa [escapingH₁] using e.faithful_action_kernel
  refine ⟨{
      H := e.H,
      sylow_le := e.hH.1.1.2,
      point_le := e.H_le_G₁,
      g := e.g,
      conjugate_le := hA_le,
      escapes_core := hescape,
      span_two := escaping_span_isPGroup s e,
      span_normalizes := hnorm,
      commutator_line := by
        simpa [terminalIntersection, terminalCore, A, Q, escapingA, escapingQ,
          escapingH₁] using hcomm,
      small_corank := by
        simpa [terminalIntersection, terminalCore, A, Q, escapingA, escapingQ,
          escapingH₁] using hsmall,
      action_kernel := by
        simpa [terminalCore, Q, escapingQ, escapingH₁] using hkernel
    }⟩

/-- Application to the already proved terminal contradiction.  `PointControl`
is retained as the independent fusion input, exactly as in the source proof. -/
theorem exterior_false_of_escapingSource
    {h : Hypothesis1223 KnownSimple.IsKnownSimple T L}
    (e : s.EscapingSource h) (p : PointControl s.marking) : False := by
  exact exterior_contradiction_of_point_and_terminal s.marking p
    (terminalConfiguration_of_escapingSource s e).some

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
