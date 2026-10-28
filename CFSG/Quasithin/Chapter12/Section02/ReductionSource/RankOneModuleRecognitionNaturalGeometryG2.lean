module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryG2
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometryProduct
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometrySetup

/-!+# The G.2.3 geometry on the original Chapter 12 reduced layer

The source E.6.1 and normalizer results discharge the local premises in
the natural G.2.3 application. This gives L₁ = LU, the literal two-core
product, elementary E, and [L₁,E] ≤ V_L. The moving-pair calculation and
opposite-line geometry also give both crossed fixed-space identities.

The final theorem applies these constructions to |U/Z_S| ≤ 256. Its
remaining inputs are the degree-two reduction, the moving pair, and the
natural section R/E with its index four. These and the initial natural
marking remain with qt-d-1222-rankone-recognition-natural. No unconditional
6.1.27 conclusion is asserted.

Source: Aschbacher–Smith, 6.1.21 and 6.1.26, printed pp.675–676, 678–679.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The original escaping closure has the source core product and elementary
central intersection. E.6.1 and the local normalizer premise are discharged. -/
theorem source_escape_core_geometry
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hnon : ¬ Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G))
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L (wholeReduced T L)) :
    Escape.L1 (T : Subgroup G) L (wholeReduced T L) l =
      L ⊔ Escape.U (T : Subgroup G) L (wholeReduced T L) ∧
    Escape.R (T : Subgroup G) L (wholeReduced T L) l =
      (Escape.U (T : Subgroup G) L (wholeReduced T L) ⊓ centralizer (commutatorLayer T L : Set G)) ⊔
        ((Escape.U (T : Subgroup G) L (wholeReduced T L)).map (MulAut.conj l⁻¹).toMonoidHom ⊓
          centralizer (commutatorLayer T L : Set G)) ∧
    IsElementaryAbelian 2 (Escape.E (T : Subgroup G) L (wholeReduced T L) l) ∧
    ⁅Escape.L1 (T : Subgroup G) L (wholeReduced T L) l,
      Escape.E (T : Subgroup G) L (wholeReduced T L) l⁆ ≤ commutatorLayer T L ∧
    L ⊔ (T : Subgroup G) ≤ normalizer (Escape.R (T : Subgroup G) L (wholeReduced T L) l : Set G) :=
  natural_escape_core_geometry h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_central_line_S_normalizer_le D h h611) hnon hl hlout

/-- Construct all fields of the escaping geometry except the later natural
section and its multiplicity. All literal subgroup identities are proved. -/
theorem source_escape_geometry_of_section
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) 2)
    (hnatural : IsNaturalModule L (commutatorLayer T L) 2)
    {g l : G} (hg : g ∈ Escape.I (T : Subgroup G) L (wholeReduced T L)) (hl : l ∈ L)
    (hlout : l ∉ Escape.H (T : Subgroup G) L (wholeReduced T L))
    (hmove : ¬ (commutatorLayer T L).map (MulAut.conj g⁻¹).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G))
    (hsection : Escape.IsNaturalSectionFour (Escape.L1 (T : Subgroup G) L (wholeReduced T L) l)
      (Escape.R (T : Subgroup G) L (wholeReduced T L) l) (Escape.E (T : Subgroup G) L (wholeReduced T L) l))
    (hindex : (Escape.E (T : Subgroup G) L (wholeReduced T L) l).relIndex
      (Escape.U (T : Subgroup G) L (wholeReduced T L) ⊓ centralizer (commutatorLayer T L : Set G)) = 4) :
    Nonempty (NaturalEscape.Geometry (T : Subgroup G) L (wholeReduced T L)) :=
  natural_escape_geometry_of_section h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2
    (source_central_line_S_normalizer_le D h h611) hg hl hlout hmove hsection hindex

/-- The G.2.3 identities and crossed fixed spaces feed the terminal order
estimate. Initial naturalness, degree two, the moving pair and the later
natural-section/index claims remain with the final assembly in this task. -/
theorem source_escape_small_quotient_of_section
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) 2)
    (hnatural : IsNaturalModule L (commutatorLayer T L) 2)
    (hCT : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥)
    {g l : G} (hg : g ∈ Escape.I (T : Subgroup G) L (wholeReduced T L)) (hl : l ∈ L)
    (hlout : l ∉ Escape.H (T : Subgroup G) L (wholeReduced T L))
    (hmove : ¬ (commutatorLayer T L).map (MulAut.conj g⁻¹).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G))
    (hsection : Escape.IsNaturalSectionFour (Escape.L1 (T : Subgroup G) L (wholeReduced T L) l)
      (Escape.R (T : Subgroup G) L (wholeReduced T L) l) (Escape.E (T : Subgroup G) L (wholeReduced T L) l))
    (hindex : (Escape.E (T : Subgroup G) L (wholeReduced T L) l).relIndex
      (Escape.U (T : Subgroup G) L (wholeReduced T L) ⊓ centralizer (commutatorLayer T L : Set G)) = 4) :
    letI := h611.ZS_normal_in_escape_U
    Nat.card (NaturalEscape.Quotient (T : Subgroup G) L (wholeReduced T L)) ≤ 256 := by
  let := h611.ZS_normal_in_escape_U
  obtain ⟨d⟩ := source_escape_geometry_of_section D h h611 hnatural hg hl hlout hmove hsection hindex
  exact d.quotient_card_le hnatural hCT

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
