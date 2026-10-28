module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuMarkings
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.NoFF
public import CFSG.Quasithin.ChapterH.Section10To12.TripleDisplacement.Cubic
public import Theory.Representation.MathieuCodeRestriction.QuadraticActors.NoFF

/-!
# The Mathieu involution minimum

Every involution of the full marked source actor moves at least three binary
dimensions. The proof uses the actual M₁₂ heart, the outer M₂₂ code/cocode,
the triple M₂₂ cover, and the M₂₃/M₂₄ code/cocode actions. In the triple
case a cubic displacement estimate supplies the bound without removing
the covering center. Taking the actual involution minimum gives m > 2.

The chosen-module consumer in NonFFSourceMathieuParameters transports this
bound through the original Sylow image and applies E.6.3 and the generation
cap to prove the complete initial inequalities of 7.3.4.

Source: Aschbacher--Smith, Table 7.2.1 and 7.3.2--4, printed pp.698--699;
H.11.1, H.12.1 and H.14.4, pp.392--394,397--398.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open ChapterE MathieuCode Sporadic.Mathieu
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open ChapterH.Section10To12

private theorem m12_involution_bound (t : MulAut M12) (ht : orderOf t = 2) :
    4 ≤ fixedCodim M12Calculations.Ambient.automorphismRepresentation (zpowers t) := by
  by_cases hi : t ∈ MulAut.innerSubgroup M12
  · obtain ⟨x,rfl⟩ := hi
    have hx : orderOf x = 2 :=
      (orderOf_injective _ M12AutomorphismRank.conjugation_injective x).symm.trans ht
    have he := fixedSpace_comp_map M12Calculations.Ambient.automorphismRepresentation
      MulAut.conj (zpowers x)
    rw [M12Calculations.Ambient.automorphismRepresentation_inner, MonoidHom.map_zpowers] at he
    change 4 ≤ Module.finrank (ZMod 2) (M12Heart ⧸ fixedSpace _ _)
    rw [←he]
    exact le_of_eq (M12Calculations.fixedCodim_involution x hx).symm
  · rw [M12Calculations.LocalActors.fixedCodim_native_outer
      M12Calculations.outer_involution_fusion _
      M12Calculations.Ambient.automorphismRepresentation_faithful hi ht]
    decide

private theorem fixedCodim_marked_element
    {A B E F : Type*} [Group A] [Group B]
    [AddCommGroup E] [Module (ZMod 2) E] [AddCommGroup F] [Module (ZMod 2) F]
    (ρ : Representation (ZMod 2) A E) (σ : Representation (ZMod 2) B F)
    (f : A →* B) (e : ρ.Equiv (σ.comp f)) (t : A) :
    fixedCodim ρ (zpowers t) = fixedCodim σ (zpowers (f t)) := by
  simpa only [MonoidHom.map_zpowers] using
    fixedCodim_map_equivariant ρ σ f e.toLinearEquiv
      (fun g v => LinearMap.congr_fun (e.isIntertwining' g) v) (zpowers t)

variable {A E : Type*} [Group A] [Finite A]
  [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
  (ρ : Representation (ZMod 2) A E) (L : Subgroup A)

/-- Every involution of the original Mathieu actor moves at least three
binary dimensions, including the outer M₂₂ and triple-cover actors. -/
theorem mathieu_involution_fixedCodim
    (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hm : HasMathieuCentralQuotient L) (t : A) (ht : orderOf t = 2) :
    3 ≤ fixedCodim ρ (zpowers t) := by
  rcases hm with h12 | h22 | h23 | h24
  · obtain ⟨d⟩ := MathieuMarkings.m12_marking ρ L h h12
    rw [fixedCodim_marked_element ρ _ d.embedding d.equivalence t]
    exact (by decide : 3 ≤ 4).trans
      (m12_involution_bound _ ((orderOf_injective _ d.injective t).trans ht))
  · rcases MathieuMarkings.m22_marking ρ L h h22 with hc | hd | ht'
    · obtain ⟨d⟩ := hc
      rw [fixedCodim_marked_element ρ _ d.embedding d.equivalence t]
      exact (m22Outer_involution_displacement_ge_three _
        ((orderOf_injective _ d.injective t).trans ht)).1
    · obtain ⟨d⟩ := hd
      rw [fixedCodim_marked_element ρ _ d.embedding d.equivalence t]
      exact (m22Outer_involution_displacement_ge_three _
        ((orderOf_injective _ d.injective t).trans ht)).2
    · obtain ⟨d⟩ := ht'
      have hs : M22Source.SourceHypotheses ρ L :=
        ⟨h.sqtk,h.fitting.symm,h.quasisimple,h.faithful,h.irreducible,h.smallCubic,h22⟩
      let : ρ.IsIrreducible := M22Source.source_irreducible ρ L hs
      have hc : Nat.card (center L) = 3 :=
        (Nat.card_congr (centerCongr d.componentEquiv).toEquiv).trans M22TripleCover.center_card
      exact (by decide : 3 ≤ 4).trans (TripleDisplacement.four_le_fixedCodim_involution
        L ⟨h.quasisimple,hc,h22⟩ h.fitting ρ h.faithful d.degree t ht)
  · rcases (MathieuMarkings.m23_marking ρ L h h23).2 with hc | hd
    · obtain ⟨e,E,he⟩ := hc
      have hh := fixedCodim_map_equivariant ρ codeRepresentation
        (pointEmbedding.comp e.toMonoidHom) E he (zpowers t)
      rw [MonoidHom.map_zpowers, code_cocode_fixedCodim_zpowers] at hh
      rw [hh]
      exact QuadraticActors.m24_cocode_involution_gt_two _
        ((orderOf_injective pointEmbedding pointEmbedding_injective (e t)).trans ((e.orderOf_eq t).trans ht))
    · obtain ⟨e,E,he⟩ := hd
      have hh := fixedCodim_map_equivariant ρ cocodeRepresentation
        (pointEmbedding.comp e.toMonoidHom) E he (zpowers t)
      rw [MonoidHom.map_zpowers] at hh
      rw [hh]
      exact QuadraticActors.m24_cocode_involution_gt_two _
        ((orderOf_injective pointEmbedding pointEmbedding_injective (e t)).trans ((e.orderOf_eq t).trans ht))
  · obtain ⟨e,hc | hd⟩ := MathieuMarkings.m24_marking ρ L h h24
    · obtain ⟨E⟩ := hc
      rw [fixedCodim_marked_element ρ _ e.toMonoidHom E t]
      exact QuadraticActors.m24_cocode_involution_gt_two _ ((e.orderOf_eq t).trans ht)
    · obtain ⟨E⟩ := hd
      rw [fixedCodim_marked_element ρ _ e.toMonoidHom E t, code_cocode_fixedCodim_zpowers]
      exact QuadraticActors.m24_cocode_involution_gt_two _ ((e.orderOf_eq t).trans ht)

/-- The involution minimum on every source Mathieu actor is greater than two. -/
theorem mathieu_moduleM_ge_three
    (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hm : HasMathieuCentralQuotient L) : 3 ≤ moduleM ρ := by
  apply le_csInf ⟨_, Set.mem_insert _ _⟩
  rintro d (rfl | ⟨t,ht,rfl⟩)
  · have hd := MathieuMarkings.MarkedRows.finrank_cases ρ L
      (MathieuMarkings.markedRows ρ L h hm)
    omega
  · exact mathieu_involution_fixedCodim ρ L h hm t ht
end CFSG.Quasithin.Chapter7.NormalizedSource

