module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryProduct
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometryCore

/-!
# Escaping pair products on the original Chapter 12 reduced layer

The chosen-module source construction supplies E.6.1 and the exact global-s
rank for B = [R₂(LT),L]. Applying the pair argument gives both action indices
and U = B Bᵍ C_U(B Bᵍ), using the book's right-conjugation convention.
Those identities construct the product and index fields of the existing
escape geometry and feed its actual bound |U/Z_S| ≤ 256.

The natural marking, moving pair, degree-two reduction, remaining geometric
identities and marked PSL₂ component still belong to
qt-d-1222-rankone-recognition-natural. These applications do not assert the
unconditional 6.1.27 reduction.

Source: Aschbacher–Smith, 6.1.20(4) and 6.1.26, printed pp.675, 678–679.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- A noncommuting pair in the original closure splits off its centralizer,
with both actual action indices equal to the field order. -/
theorem source_escape_pair_product
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    {g : G} (hg : g ∈ Escape.I (T : Subgroup G) L (wholeReduced T L))
    (hmove : ¬ (commutatorLayer T L).map (MulAut.conj g⁻¹).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G)) :
    let B := commutatorLayer T L
    let A := B.map (MulAut.conj g⁻¹).toMonoidHom
    let U := Escape.U (T : Subgroup G) L (wholeReduced T L)
    U = (B ⊔ A) ⊔ (U ⊓ centralizer ((B ⊔ A : Subgroup G) : Set G)) ∧
      (U ⊓ centralizer (B : Set G)).relIndex U = 2 ^ n ∧
      (centralizer (A : Set G)).relIndex U = 2 ^ n :=
  natural_escape_pair_product h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2
    ((Escape.I (T : Subgroup G) L (wholeReduced T L)).inv_mem hg) hmove

/-- Apply the pair construction on the literal Chapter 12 layer. No product,
closure containment, line order, commutator or action-index input is needed. -/
theorem source_escape_geometry_of_pair
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) 2)
    (hnatural : IsNaturalModule L (commutatorLayer T L) 2)
    {g l : G} (hg : g ∈ Escape.I (T : Subgroup G) L (wholeReduced T L)) (hl : l ∈ L)
    (hlout : l ∉ Escape.H (T : Subgroup G) L (wholeReduced T L))
    (hmove : ¬ (commutatorLayer T L).map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer (commutatorLayer T L : Set G))
    (hgen : Escape.L1 (T : Subgroup G) L (wholeReduced T L) l = L ⊔ Escape.U (T : Subgroup G) L (wholeReduced T L))
    (hEE : Escape.E (T : Subgroup G) L (wholeReduced T L) l ≤ centralizer (Escape.E (T : Subgroup G) L (wholeReduced T L) l : Set G))
    (hcore : Escape.R (T : Subgroup G) L (wholeReduced T L) l =
      (Escape.U (T : Subgroup G) L (wholeReduced T L) ⊓ centralizer (commutatorLayer T L : Set G)) ⊔
        ((Escape.U (T : Subgroup G) L (wholeReduced T L)).map (MulAut.conj l⁻¹).toMonoidHom ⊓
          centralizer (commutatorLayer T L : Set G)))
    (hcentral : ⁅Escape.L1 (T : Subgroup G) L (wholeReduced T L) l, Escape.E (T : Subgroup G) L (wholeReduced T L) l⁆ ≤ commutatorLayer T L)
    (hfixedR : ZS (T : Subgroup G) L (wholeReduced T L) ⊓ centralizer
      ((commutatorLayer T L).map (MulAut.conj (g * l)⁻¹).toMonoidHom : Set G) = ⊥)
    (hfixedL : (ZS (T : Subgroup G) L (wholeReduced T L)).map (MulAut.conj l⁻¹).toMonoidHom ⊓ centralizer
      ((commutatorLayer T L).map (MulAut.conj g⁻¹).toMonoidHom : Set G) = ⊥)
    (hsection : Escape.IsNaturalSectionFour (Escape.L1 (T : Subgroup G) L (wholeReduced T L) l)
      (Escape.R (T : Subgroup G) L (wholeReduced T L) l) (Escape.E (T : Subgroup G) L (wholeReduced T L) l))
    (hindex : (Escape.E (T : Subgroup G) L (wholeReduced T L) l).relIndex
      (Escape.U (T : Subgroup G) L (wholeReduced T L) ⊓ centralizer (commutatorLayer T L : Set G)) = 4) :
    Nonempty (NaturalEscape.Geometry (T : Subgroup G) L (wholeReduced T L)) := by
  exact natural_escape_geometry_of_pair h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2
    hg hl hlout hmove hgen hEE hcore hcentral hfixedR hfixedL hsection hindex

/-- The constructed product and indices feed the actual terminal size estimate.
The remaining geometry and initial natural marking stay with this task. -/
theorem source_escape_small_quotient_of_pair
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) 2)
    (hnatural : IsNaturalModule L (commutatorLayer T L) 2)
    (hCT : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥)
    {g l : G} (hg : g ∈ Escape.I (T : Subgroup G) L (wholeReduced T L)) (hl : l ∈ L)
    (hlout : l ∉ Escape.H (T : Subgroup G) L (wholeReduced T L))
    (hmove : ¬ (commutatorLayer T L).map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer (commutatorLayer T L : Set G))
    (hgen : Escape.L1 (T : Subgroup G) L (wholeReduced T L) l = L ⊔ Escape.U (T : Subgroup G) L (wholeReduced T L))
    (hEE : Escape.E (T : Subgroup G) L (wholeReduced T L) l ≤ centralizer (Escape.E (T : Subgroup G) L (wholeReduced T L) l : Set G))
    (hcore : Escape.R (T : Subgroup G) L (wholeReduced T L) l =
      (Escape.U (T : Subgroup G) L (wholeReduced T L) ⊓ centralizer (commutatorLayer T L : Set G)) ⊔
        ((Escape.U (T : Subgroup G) L (wholeReduced T L)).map (MulAut.conj l⁻¹).toMonoidHom ⊓
          centralizer (commutatorLayer T L : Set G)))
    (hcentral : ⁅Escape.L1 (T : Subgroup G) L (wholeReduced T L) l, Escape.E (T : Subgroup G) L (wholeReduced T L) l⁆ ≤ commutatorLayer T L)
    (hfixedR : ZS (T : Subgroup G) L (wholeReduced T L) ⊓ centralizer
      ((commutatorLayer T L).map (MulAut.conj (g * l)⁻¹).toMonoidHom : Set G) = ⊥)
    (hfixedL : (ZS (T : Subgroup G) L (wholeReduced T L)).map (MulAut.conj l⁻¹).toMonoidHom ⊓ centralizer
      ((commutatorLayer T L).map (MulAut.conj g⁻¹).toMonoidHom : Set G) = ⊥)
    (hsection : Escape.IsNaturalSectionFour (Escape.L1 (T : Subgroup G) L (wholeReduced T L) l)
      (Escape.R (T : Subgroup G) L (wholeReduced T L) l) (Escape.E (T : Subgroup G) L (wholeReduced T L) l))
    (hindex : (Escape.E (T : Subgroup G) L (wholeReduced T L) l).relIndex
      (Escape.U (T : Subgroup G) L (wholeReduced T L) ⊓ centralizer (commutatorLayer T L : Set G)) = 4) :
    letI := h611.ZS_normal_in_escape_U
    Nat.card (NaturalEscape.Quotient (T : Subgroup G) L (wholeReduced T L)) ≤ 256 := by
  let := h611.ZS_normal_in_escape_U
  obtain ⟨d⟩ := source_escape_geometry_of_pair D h h611 hnatural hg hl hlout hmove
    hgen hEE hcore hcentral hfixedR hfixedL hsection hindex
  exact d.quotient_card_le hnatural hCT

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
