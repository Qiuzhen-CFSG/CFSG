module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition.Offenders
public import Theory.Representation.BinaryOffender.MarkedCentralQuotient
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.G2OrthogonalCover.Universal

/-!
# Recognition on the actual irreducible central section

The central-section kernel centralizes the normal component and hence is
trivial. The original quadratic actor acts quadratically on this same
section, with no larger fixed codimension. The proved binary G₂ cubic
recognition, underlying B.4.2/B.4.5, supplies the derived-group marking and
natural intertwiner without a natural-quotient hypothesis.

Source: Aschbacher–Smith B.4.2, B.4.5 and K.3, applied in 13.8.27, p.963.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition

variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) (L : Subgroup D) [L.Normal] [IsQuasisimple L]

/-- Recognize the actual central quotient of an invariant Irr⁺ member. The
 original quadratic actor passes to this faithful section before recognition. -/
theorem central_section_natural
    (hc : centralizer (L : Set D) = ⊥)
    (e : L ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (I : Subrepresentation ρ) (hI : IsIrrPlus ρ L I.toSubmodule)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hquad : IsQuadratic ρ A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) :
    ∃ e' : L ≃* commutator (Atlas.G2.Model (ZMod 2)),
      ∃ f : centralQuotient ρ L I.toSubmodule ≃ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2),
        ∀ g : L, ∀ v, f (normalCentralQuotient ρ L I g v) =
          Atlas.G2.Natural.OrthogonalCover.binaryNatural (ZMod 2) (e' g) (f v) := by
  let σ := normalCentralQuotient ρ L I
  have hs : (⊤ : Subgroup D) ≤ subspaceStabilizer ρ I.toSubmodule := by
    apply le_subspaceStabilizer
    intro g _ v hv
    exact I.apply_mem_toSubmodule g hv
  have hσ : Function.Injective σ := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    have hx' : (⟨x, mem_top x⟩ : (⊤ : Subgroup D)) ∈
        (centralSectionRepresentation ρ L ⊤ I.toSubmodule hs le_normalizer_of_normal).ker := hx
    have hh := (centralSection_kernel_le_centralizer ρ L ⊤ le_top I.toSubmodule
      hI hs le_normalizer_of_normal (mem_map_of_mem (⊤ : Subgroup D).subtype hx')).2
    change x ∈ centralizer (L : Set D) at hh
    rwa [hc] at hh
  have hi : IsIrreducible (σ.comp L.subtype) := hI.choose_spec.2
  let := hi
  let C := fixedSubrepresentation ρ L
  have hcod : fixedCodim σ A ≤ fixedCodim ρ A := fixedCodim_section_le ρ C I A
  have hquad' : IsQuadratic σ A := quadratic_section ρ C I hquad
  have hsmall : cubicRatio σ ≤ 2 := (cubicRatio_le_quadraticRatio σ).trans
    ((quadraticRatio_le_two_iff σ).mpr ⟨A, hA, hquad', hcod.trans hbound⟩)
  obtain ⟨e', f, hf⟩ := ChapterK.Exceptional.SourceAssembly.g2_binary_natural σ L e hσ hsmall
  exact ⟨e', LinearEquiv.ofBijective (f.toAddMonoidHom.toZModLinearMap 2) f.bijective,
    fun g v => hf g v⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition
