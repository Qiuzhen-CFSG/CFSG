module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesGeometry
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesBinary

/-!
# The original opposite subgroup in the escaping-cubic obstruction

The chosen module supplies normalization of L by T. The Cartan quotient
and local four-plane then construct the natural G.2.3 input on the full
involution centralizer, under the nonabelian-span alternative. An element
of the original cubic moves the point, and its opposite subgroup has
kernel precisely S₂ in the faithful action on U/⟨z⟩. Its elementary image
satisfies the source index |U:S₂| = 2 |A*|.

This discharges the natural-coordinate and exact-image steps of 5.1.23
for the literal classification groups. The multiplicity bound, small
cubic ratio and constituent contradiction remain to be established.

Source: Aschbacher--Smith, 5.1.23, printed p.645, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape ChapterG.Section02 ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ} {z : G}

/-- The exact opposite image for the actual centralizer span. All G.2.3
natural-coordinate premises are constructed from the original data. -/
theorem linear_cubic_nonabelian_opposite_image
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G)))) :
    let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
    let s := linear_cubic_centralizer_setup h d
    ∃ g ∈ C, g ∉ normalizer (zpowers z : Set G) ∧
      let A₀ := (conjugate (S.W g) g).subgroupOf S.H
      let E := A₀.map (SpanAction.projection s)
      (SpanAction.projection s).ker ⊓ A₀ = (S.S₂ g).subgroupOf S.H ∧
        IsElementaryAbelian 2 E ∧ (S.S₂ g).relIndex S.U = 2 * Nat.card E := by
  let s := linear_cubic_centralizer_setup h d
  let b := d.binaryNaturalData c D.sylow_normalizes_component hpsl s hne
  obtain ⟨g, hg, hgn⟩ := d.exists_moving_cubic
  have hga : g ∈ CubicEscape.actor T C := le_conjugateSpanBy C (T : Subgroup G) hg
  exact ⟨g, hg, hgn, SpanAction.binary_opposite_kernel s b g hga hgn,
    SpanAction.binary_opposite_image s b g hga hgn⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
