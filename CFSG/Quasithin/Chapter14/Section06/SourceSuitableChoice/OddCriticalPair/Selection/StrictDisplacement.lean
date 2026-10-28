module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Selection.ReturnedGeometry
public import Theory.LinearAlgebra.DisplacementFiltration

/-!
# Displacement bound from the selected strict denominator

The denominator maps into the transported central line under every endpoint
actor displacement. The image dimension is at most that line's dimension
plus the denominator codimension. The latter is the literal logarithmic
relative index, with containment of the original central line verified.

Selection.StrictOrthogonalSource applies this to the remaining rank-eight
endpoint to bound each displacement by three.

Source: Aschbacher--Smith 14.6.13, equation (*) and its following paragraph,
printed p.1032; F.9.13 supplies the denominator commutator.
-/

public section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
open Subgroup Representation Representation.BinaryOffender
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open Chapter13.Section08.CriticalGeometry Chapter13.Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G]

/-- The literal denominator is mapped into the transported central line.
Thus each displacement has rank at most the denominator codimension plus one. -/
theorem SelectedQuadraticEndpoint.displacement_rank_le
    {D : ChapterF.Section09.Setup G} {h : D.Hypothesis}
    [IsElementaryAbelian 2 D.UH] {a : LocalQuotientAction D.H D.UH D.V₁}
    (c : SelectedQuadraticEndpoint h a) (hb : 3 ≤ h.b)
    {t : D.H ⧸ pCore 2 D.H} (ht : t ∈ actorImage D.H (c.endpoint.conjugate D.UH)) :
    Module.finrank (ZMod 2) (LinearMap.range (a.representation t - LinearMap.id)) ≤
      Nat.log 2 ((commutatorPreimage D.UH (c.endpoint.conjugate D.UH)
        (c.endpoint.conjugate D.V₁)).relIndex D.UH) + 1 := by
  let s := ModuleBound.OriginalF916.conjugationSection a h.H_centralizes
  let B := c.endpoint.conjugate D.UH
  let C := c.endpoint.conjugate D.V₁
  let E := commutatorPreimage D.UH B C
  have hUV : D.UH ≤ D.VH := conjugateSpanBy_mono h.plus_le le_rfl
  have hBH : B ≤ D.H := (map_mono hUV).trans (c.endpoint.large_le hb)
  have hnorm : D.UH ≤ normalizer (C : Set G) := by
    have hn := map_mono (f := (MulAut.conj c.endpoint.representative).toMonoidHom)
      (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    rw [map_equiv_normalizer_eq] at hn
    exact (hUV.trans (c.endpoint.reverse_le hb)).trans hn
  have hC : Nat.card C = 2 := by
    change Nat.card (D.V₁.map (MulAut.conj c.endpoint.representative).toMonoidHom) = 2
    rw [card_map_of_injective (MulAut.conj c.endpoint.representative).injective,h.point_card]
  obtain ⟨hline,hdisp⟩ := s.critical_line_displacement B C hnorm hC
  have hm : (s.image E).map (a.representation t - LinearMap.id) ≤ s.image C := by
    rintro _ ⟨v,hv,rfl⟩
    exact hdisp t ht v hv
  have hh := LinearMap.finrank_range_le_quotient_add_map
    (a.representation t - LinearMap.id) (s.image E)
  rw [s.quotient_finrank E (s.line_le_DH B C hBH)] at hh
  exact hh.trans (Nat.add_le_add_left ((Submodule.finrank_mono hm).trans hline) _)
end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
