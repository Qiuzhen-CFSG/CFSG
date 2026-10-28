module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.Extensions
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.AssemblySupport
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.Earlier

/-!
# The full six-letter alternative from the literal natural section

The component's natural section gives a perfect central covering projection
from the original U_H/V₁. The cover comparison identifies the whole module
with the four-dimensional natural module or the five-dimensional augmentation
module. In either case its faithful H/O₂(H) action extends the same marked
component action to a subgroup of S₆ containing A₆. This proves the actual
A₆/S₆ actor alternative without requiring a transvection.

The source consumer applies the universal earlier 13.7.6 implications to
construct H=KT, relative component normality, the ordinary local A₆ quotient,
and both noncentral chief factors on U_H/V₁. Its remaining input is recognition
of the literal component section, not recognition of the whole source module.
The strict-case recognition in 13.8.26, the equality H=G₁ and the G₂ exclusion
remain obligations of the 13.8.27 assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.26–27, printed pp.962–963, using 13.7.6(3), pp.938–939.
-/

@[expose] public section

open Subgroup Representation
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceSix
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension

variable {G : Type*} [Group G] [Finite G] {H K V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- Both whole modules, with the same permutation embedding of the actual actor.
The component compatibility is stated on the original K representatives. -/
def MarkedFullAction
    (hKH : K ≤ H) (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁))) : Prop :=
  ∃ f : Source.Hstar H →* Equiv.Perm (Fin 6), Function.Injective f ∧
    (∀ k : K, f (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) =
      (eK (QuotientGroup.mk' (pCore 2 K) k)).val) ∧
    ((∃ eH : Source.Hstar H ≃* alternatingGroup (Fin 6), ∀ a, (eH a).val = f a) ∨
      (∃ eH : Source.Hstar H ≃* Equiv.Perm (Fin 6), ∀ a, eH a = f a)) ∧
    ((∃ eU : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6),
      ∀ a v, eU (ρ a v) = BinaryPermutation.naturalRepresentation (Fin 6) (f a) (eU v)) ∨
     (∃ eU : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 6),
      ∀ a v, eU (ρ a v) = BinaryPermutation.coreRepresentation (Fin 6) (f a) (eU v)))

/-- Extend the recognized section to the whole faithful source action. Neither
an A₆/S₆ identification of H* nor a transvection is assumed. -/
theorem full_action_of_section
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKn : (K.subgroupOf H).Normal)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hcentralizer : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK) :
    MarkedFullAction hKH eK ρ := by
  let : (Source.starImage H K).Normal :=
    Subgroup.Normal.map hKn (QuotientGroup.mk' (pCore 2 H))
      (QuotientGroup.mk'_surjective (pCore 2 H))
  have hf := faithful_of_centralizer_le_core ρ hρ hcentralizer
  have hrep (f : Source.Hstar H →* Equiv.Perm (Fin 6))
      (he : ∀ k : Source.starImage H K, f k = (componentModelEquiv hKH hK eK k).val)
      (k : K) : f (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) =
        (eK (QuotientGroup.mk' (pCore 2 K) k)).val := by
    let a := eK (QuotientGroup.mk' (pCore 2 K) k)
    let x := Components.componentStarEquiv H K hKH hK (eK.symm a)
    have hx : (x : Source.Hstar H) =
        QuotientGroup.mk' (pCore 2 H) (inclusion hKH k) := modelActor_mk hKH hK eK k
    rw [← hx, he]
    simp only [componentModelEquiv, MulEquiv.trans_apply, x,
      MulEquiv.symm_apply_apply, a]
  rcases alternatingSix_module_of_section hKH hK ρ hρ hgen eK hs with
    ⟨eU, heU⟩ | ⟨eU, heU⟩
  · obtain ⟨f, hf, hfK, hact, hmodels⟩ := NaturalSix.faithful_extension
      (Source.starImage H K) ρ hf (componentModelEquiv hKH hK eK) eU
      (fun k v => by
        simpa only [modelActor_componentModelEquiv] using
          heU (componentModelEquiv hKH hK eK k) v)
    exact ⟨f, hf, hrep f hfK, hmodels, Or.inl ⟨eU, hact⟩⟩
  · obtain ⟨f, hf, hfK, hact, hAlt, _⟩ :=
      TransvectionParabolic.Marking.CompatibleFlags.AugmentationExtension.faithful_extension
        (Source.starImage H K) ρ hf (componentModelEquiv hKH hK eK) eU
        (fun k v => by
          simpa only [modelActor_componentModelEquiv, BinaryPermutation.alternatingCoreRepresentation,
            MonoidHom.comp_apply, Subgroup.coe_subtype] using
            heU (componentModelEquiv hKH hK eK k) v)
    exact ⟨f, hf, hrep f hfK, NaturalSix.extension_equiv_of_embedding f hf hAlt,
      Or.inr ⟨eU, hact⟩⟩

/-- The original local source application. The earlier universal 13.7.6(3)
implication supplies the local A₆ quotient and chief factors, while the
preceding theorem constructs both full actor and module alternatives. -/
theorem source_alternative_of_section
    (T : Sylow 2 G) {L V V₂ M G₁ : Subgroup G}
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK) :
    let := d.uh_elementary hH
    (H : Set G) = (K : Set G) * (T : Set G) ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      MarkedFullAction hKH eK ρ ∧
      CriticalGeometry.Reorientation.TwoNoncentralChiefFactors
        (ChiefQuotient.loneQuotientRepresentation H V₃ V₁ (sourceOne L T V₁)
          (le_sup_left.trans hH.1.2) ρ) := by
  let := d.uh_elementary hH
  obtain ⟨hgen, _, hprod, hcases⟩ :=
    earlier.alternating d H hH ρ hρ K hKH hK 6 (by decide) eK hs
  rcases hcases with ⟨_, hL, hchief⟩ | ⟨hfalse, _⟩
  · have hn := component_normal_of_product T (le_sup_right.trans hH.1.2) hKH hK hprod
    exact ⟨hprod, hL, full_action_of_section hKH hK hn ρ hρ
      (earlier.centralizer d H hH).le hgen eK hs,
      ChiefQuotient.twoNoncentralChiefFactors_utilde H V₃ V₁
        (sourceOne L T V₁) (le_sup_left.trans hH.1.2) ρ hρ
        (d.line_le_uh H) d.line_card hchief⟩
  · omega

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceSix
end
