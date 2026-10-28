module
public import Theory.Representation.BinaryConjugationSection.ComplementPlaneKernel
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceOriginalSpan

/-!
# The original maximal kernel on the natural seed

The actual L₀ matrix image contains the complementary cubic. Its irreducible
binary action modulo V₃, together with U_L = ⟨U_H^L⟩, makes every proper
L-invariant kernel above V meet U_H exactly in V₃. Thus the image of U_H
in the literal selected maximal quotient has order four. This discharges
the seed-kernel premise without assuming a separately marked irreducible
U_H/V₃ representation.

The selected-quotient application retains the canonical covered-A₆ map,
full ambient kernel, binary degree alternatives and original L₀ chief count.
Excluding degree six and compatible extra-line movement remain required;
this does not establish 13.8.30 or the terminal 13.8.28 contradiction.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
13.8.30, printed p.964.
-/

public noncomputable section
open Subgroup Representation NoncentralChiefRefinement
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open BinaryParabolicExteriorSquare.PlaneSpan BinaryLinear.FlagCoordinates
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The original natural action determines the intersection with any proper
L-normal kernel above V. No irreducible-seed hypothesis is supplied. -/
theorem source_original_maximal_seed_kernel
    (s : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hab : IsMulCommutative (conjugateSpanBy V G₁))
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hcentral : centralizer (V₃:Set G) ≤ M ⊓ normalizer (V:Set G))
    (hDH : zero L ≤ H)
    (eL : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V₃) V₁ ρ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = (Source.QH H).subgroupOf H)
    (honto : Function.Surjective π)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (hplane : d.imageSpace V₃ = plane)
    (N : Subgroup G) (hN : L ≤ normalizer N) (hVN : V ≤ N)
    (hproper : ¬ Source.UL L H V₃ ≤ N) :
    Source.UH H V₃ ⊓ N = V₃ := by
  have hlocal := source_zero_matrix_image_from_original_seed s hab h hH hcentral
    hDH eL ρ d π hker honto hnatural hplane
  have hcubic : complementElement ∈ ((zero L).subgroupOf H).map π := by
    rw [hlocal]
    exact (show zpowers complementElement ≤ BinaryParabolicExteriorSquare.PlaneRadical.complementLocal
      from le_sup_right) (mem_zpowers _)
  apply d.inf_eq_plane_of_complement H (zero L) (Source.UH H V₃) V₁ V₃ N
    ρ π hnatural (s.line_le_plane.trans s.plane_le_seed) (le_conjugateSpanBy _ _)
    hplane hcubic ((zero_le L).trans hN) (s.seed_le.trans hVN)
  intro hUN
  exact hproper (conjugateSpanBy_le hUN hN)

/-- On the same literal quotient the natural seed image has order four. -/
theorem source_original_maximal_seed_image
    (s : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hab : IsMulCommutative (conjugateSpanBy V G₁))
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hcentral : centralizer (V₃:Set G) ≤ M ⊓ normalizer (V:Set G))
    (hDH : zero L ≤ H)
    (eL : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V₃) V₁ ρ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = (Source.QH H).subgroupOf H)
    (honto : Function.Surjective π)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (hplane : d.imageSpace V₃ = plane)
    (N : Subgroup G) (hN : L ≤ normalizer N) (hVN : V ≤ N)
    (hproper : ¬ Source.UL L H V₃ ≤ N)
    {Z : Type*} [AddCommGroup Z] [Module (ZMod 2) Z]
    (η : Representation (ZMod 2) L Z)
    (q : BinaryConjugationSection L (Source.UL L H V₃) N η) :
    Source.UH H V₃ ⊓ N = V₃ ∧ Nat.card (q.imageSpace (Source.UH H V₃)) = 4 := by
  have hk := source_original_maximal_seed_kernel s hab h hH hcentral hDH eL
    ρ d π hker honto hnatural hplane N hN hVN hproper
  have hUc : Nat.card (Source.UH H V₃) = 32 := by
    have hc := d.card_section
    rw [s.line_card] at hc
    simpa using hc
  have hindex : V₃.relIndex (Source.UH H V₃) = 4 := by
    have h3U : V₃ ≤ Source.UH H V₃ := le_conjugateSpanBy _ _
    have hh := (V₃.subgroupOf (Source.UH H V₃)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe h3U).toEquiv,
      s.seed_card,hUc] at hh
    change 8 * V₃.relIndex (Source.UH H V₃) = 32 at hh
    omega
  refine ⟨hk,?_⟩
  rw [q.imageSpace_card_eq_relIndex (Source.UH H V₃) (le_conjugateSpanBy _ _),
    ←inf_relIndex_right N (Source.UH H V₃),inf_comm,hk]
  exact hindex

/-- The selected original maximal quotient now includes the exact seed
intersection and its order-four image under the unchanged coordinates. -/
theorem exists_source_original_span_maximal_seed
    (s : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hab : IsMulCommutative (conjugateSpanBy V G₁))
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcentral : centralizer (V₃:Set G) ≤ M ⊓ normalizer (V:Set G))
    (hDH : zero L ≤ H)
    (eL : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V₃) V₁ ρ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = (Source.QH H).subgroupOf H)
    (honto : Function.Surjective π)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (hplane : d.imageSpace V₃ = plane) :
    ∃ U W : NormalNode L,
      U.val.map L.subtype = Source.UL L H V₃ ∧
      V ≤ W.val.map L.subtype ∧ W ⋖ U ∧
      U.val ≤ W.val ⊔ (zero L).subgroupOf L ∧
      ∃ hbin : IsElementaryAbelian 2 (Section W U),
        let _ := hbin
        ∃ σ : Representation (ZMod 2) Atlas.Codes.HexEvenAutomorphisms
            (Additive (Section W U)),
          IsIrreducible σ ∧ Function.Injective σ ∧
          σ.comp (eL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) =
            binarySectionRepresentation W U ∧
          (∃ q : BinaryConjugationSection L (Source.UL L H V₃)
            (W.val.map L.subtype)
            (σ.comp (eL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))),
            Source.UH H V₃ ⊓ W.val.map L.subtype = V₃ ∧
              Nat.card (q.imageSpace (Source.UH H V₃)) = 4) ∧
          (Module.finrank (ZMod 2) (Additive (Section W U)) = 6 ∨
            Module.finrank (ZMod 2) (Additive (Section W U)) = 18) ∧
          ∀ t : ChiefSeries (zero L), t.head = ⊥ → t.last = ⊤ →
            Module.finrank (ZMod 2) (Additive (Section W U)) ≤
              2 * t.noncentralTwoCount := by
  obtain ⟨U,W,hUm,hVW,hWU,hcover,hbin,σ,hirr,hfaith,hσ,⟨q⟩,hdegree,hcount⟩ :=
    exists_source_original_span_maximal_chief s hab h hH hF hcentral hDH eL
      ρ d π hker honto hnatural hplane
  let := hbin
  have hN : L ≤ normalizer (W.val.map L.subtype) := by
    have hh := W.val.le_normalizer_map L.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  have hproper : ¬ Source.UL L H V₃ ≤ W.val.map L.subtype := by
    intro hh
    rw [←hUm] at hh
    exact hWU.lt.not_ge ((map_le_map_iff_of_injective L.subtype_injective).mp hh)
  have hk := source_original_maximal_seed_image s hab h hH hcentral hDH eL
    ρ d π hker honto hnatural hplane (W.val.map L.subtype) hN hVW hproper _ q
  exact ⟨U,W,hUm,hVW,hWU,hcover,hbin,σ,hirr,hfaith,hσ,⟨q,hk⟩,hdegree,hcount⟩

end CFSG.Quasithin.Chapter13.Section08.LinearFour
