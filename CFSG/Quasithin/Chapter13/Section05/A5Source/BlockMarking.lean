module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.BlockCoordinates
public import CFSG.Quasithin.Chapter13.Section05.A5Source.SourceF9
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Structure
public import CFSG.Quasithin.ChapterF.Section09.NonabelianStar

/-!
# G.2.4 on the original A₅ source groups

F.9.1 supplies G.2.1 on V₃,V₁,L,T,H. Nonabelian U_H has nontrivial
image in LT/O₂(LT): a trivial image would centralize V and hence every
H-conjugate of V₃. The actual star and module coordinates therefore
construct the full G.2.4 hypothesis for every original line-moving
element of L. Such elements exist by irreducibility of V.
Source: Aschbacher–Smith13.5.14(3–4), printed p.919.
-/
@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ChapterG.Section02.AlternatingFive
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
include d hA312 hH

theorem nonabelian_star_ne_bot (hU : ¬ IsMulCommutative (Source.UH H V₃)) :
    (chapter13Setup V₁ V₃ L T H).star (Source.UH H V₃) ≠ ⊥ := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  exact hf.nonabelian_star_ne_bot hU

/-- All G.2.4 hypotheses, with the original ambient and quotient maps. -/
noncomputable def blockMarking (hU : ¬ IsMulCommutative (Source.UH H V₃))
    {g : G} (hg : g ∈ L) (hg₁ : g ∉ normalizer (V₁ : Set G)) :
    Hypothesis (chapter13Setup V₁ V₃ L T H) g := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  refine {
    setup := hf.g2_hypothesis
    model := d.blockModel H
    coordinates := d.blockCoordinates H
    equivariant := d.blockCoordinates_equivariant H
    point_card := d.flag.one_card
    seed_eq := ?_
    star_U_ne_bot := nonabelian_star_ne_bot d hA312 hH hU
    g_mem := hg
    g_not_normalizes := hg₁ }
  change V₃ = ⁅conjugateSpanBy V₁ L,D.g2.L₁⁆
  rw [d.line_span_eq,hf.g2_L₁]
  exact d.third_eq_commutator

omit [IsElementaryAbelian 2 V] hA312 hH in
/-- The source conjugator exists in L outside its original line normalizer. -/
theorem Context.exists_block_conjugator : ∃ g ∈ L, g ∉ normalizer (V₁ : Set G) := by
  apply SetLike.not_le_iff_exists.mp
  intro hn
  have hs := conjugateSpanBy_le (le_refl V₁) hn
  rw [d.line_span_eq] at hs
  exact d.third_strict.not_ge (d.third_le.trans hs)

end CFSG.Quasithin.Chapter13.Section05.A5Source
