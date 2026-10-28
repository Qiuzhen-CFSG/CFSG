module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.AlternatingCovers
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.Lifting
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.SixExtension
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.CompatibleFlags.AugmentationExtension

/-!
# Compatible extensions of the recognized component action

The prescribed K/O₂(K) model determines coordinates for its literal image K*
in H*. With those same coordinates, a transvection rules out the alternating
actor in both six-letter extensions, yielding actual S₆ isomorphisms and
full-module equivariance for the natural and augmentation alternatives.
Faithfulness is deduced from the source centralizer bound; relative normality
is transported through H → H*. For seven letters the component action is
also expressed on the six-dimensional augmentation core.

In the linear branch, equal orders of H* and the intrinsic component quotient
force K*=H*. The quotient product then lifts to H=KT using the actual Sylow
subgroup and absorbing O₂(H) in T.

These conditional extension deductions are applied in `ModelExtension.Assembly`.
There, universal 13.7.6 supplies commutator generation and H=KT, from which
component normality is proved. The seven-letter extension and chief-series
quotient transport are assembled with the concrete local quotient alternatives.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.7.6(1),(3),
printed pp.938–940; I.1.5–6, p.408; and 13.8.5, p.947.
-/

@[expose] public section

open Subgroup Representation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

/-- A transvection selects S₆ among faithful normal extensions of the marked
augmentation action, retaining the original module coordinates. -/
theorem symmetricSix_of_augmentation_extension
    {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
    [Module.Finite (ZMod 2) E]
    (K : Subgroup A) [K.Normal]
    (ρ : Representation (ZMod 2) A E) (hρ : Function.Injective ρ)
    (eK : K ≃* alternatingGroup (Fin 6))
    (eV : E ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 6))
    (he : ∀ k : K, ∀ v, eV (ρ k v) =
      BinaryPermutation.alternatingCoreRepresentation (Fin 6) (eK k) (eV v))
    (t : A) (ht : IsTransvection ρ t) :
    ∃ e : A ≃* Equiv.Perm (Fin 6),
      (∀ k : K, e k = (eK k).val) ∧
      ∀ a v, eV (ρ a v) = BinaryPermutation.coreRepresentation (Fin 6) (e a) (eV v) := by
  obtain ⟨f, hf, hfK, hfV, hfAlt, _⟩ :=
    TransvectionParabolic.Marking.CompatibleFlags.AugmentationExtension.faithful_extension
      K ρ hρ eK eV he
  rcases ComponentSieve.SixAndG2.NaturalSix.extension_equiv_of_embedding f hf hfAlt with h | h
  · exact (not_alternatingSix hρ ht ⟨h.choose⟩).elim
  · obtain ⟨e, he⟩ := h
    exact ⟨e, fun k => (he k).trans (hfK k), fun a v => by rw [he]; exact hfV a v⟩

variable {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
  {A : Type*} [Group A]

/-- The prescribed intrinsic component model, expressed on its actual image in H*. -/
noncomputable def componentModelEquiv (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (eK : (K ⧸ pCore 2 K) ≃* A) :
    Source.starImage H K ≃* A :=
  (Components.componentStarEquiv H K hKH hK).symm.trans eK

/-- The component-coordinate equivalence inverts the transported model actor. -/
theorem modelActor_componentModelEquiv (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (eK : (K ⧸ pCore 2 K) ≃* A)
    (k : Source.starImage H K) :
    modelActor hKH hK eK (componentModelEquiv hKH hK eK k) = k := by
  change ((Components.componentStarEquiv H K hKH hK)
    (eK.symm (eK ((Components.componentStarEquiv H K hKH hK).symm k))) :
      Source.Hstar H) = k
  rw [eK.symm_apply_apply, MulEquiv.apply_symm_apply]

/-- When the component quotient and H* have the same order, the source Sylow
subgroup absorbs the two-core and gives the actual product H=KT. -/
theorem product_of_equiv_component_quotient
    (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent)
    (e : Source.Hstar H ≃* (K ⧸ pCore 2 K)) :
    (H : Set G) = (K : Set G) * (T : Set G) := by
  have htop : Source.starImage H K = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    exact (Nat.card_congr (Components.componentStarEquiv H K hKH hK).toEquiv).symm.trans
      (Nat.card_congr e.toEquiv).symm
  apply product_of_star_product_sylow T H K hTH hKH
  intro x
  exact ⟨x, htop.symm ▸ Subgroup.mem_top x, 1, one_mem _, (mul_one x).symm⟩

variable {V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- Both recognized six-letter section alternatives extend to the full H* action.
The intrinsic component marking agrees with the returned S₆ equivalence. -/
theorem alternatingSix_full_module_of_section
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKn : (K.subgroupOf H).Normal)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hcentralizer : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK)
    (t : Source.Hstar H) (ht : IsTransvection ρ t) :
    (∃ eH : Source.Hstar H ≃* Equiv.Perm (Fin 6),
      ∃ eV : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6),
        (∀ k : Source.starImage H K, eH k = (componentModelEquiv hKH hK eK k).val) ∧
        ∀ a v, eV (ρ a v) = BinaryPermutation.naturalRepresentation (Fin 6) (eH a) (eV v)) ∨
    (∃ eH : Source.Hstar H ≃* Equiv.Perm (Fin 6),
      ∃ eV : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 6),
        (∀ k : Source.starImage H K, eH k = (componentModelEquiv hKH hK eK k).val) ∧
        ∀ a v, eV (ρ a v) = BinaryPermutation.coreRepresentation (Fin 6) (eH a) (eV v)) := by
  let : Module.Finite (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) := Module.Finite.of_finite
  let : (K.subgroupOf H).Normal := hKn
  let : (Source.starImage H K).Normal :=
    Subgroup.Normal.map hKn (QuotientGroup.mk' (pCore 2 H))
      (QuotientGroup.mk'_surjective (pCore 2 H))
  rcases alternatingSix_module_of_section hKH hK ρ hρ hgen eK hs with h | h
  · obtain ⟨eV, heV⟩ := h
    obtain ⟨eH, heH, he⟩ := symmetricSix_of_natural_extension (Source.starImage H K) ρ
      (faithful_of_centralizer_le_core ρ hρ hcentralizer)
      (componentModelEquiv hKH hK eK) eV (fun k v => by
        simpa only [modelActor_componentModelEquiv] using
          heV (componentModelEquiv hKH hK eK k) v) t ht
    exact Or.inl ⟨eH, eV, heH, he⟩
  · obtain ⟨eV, heV⟩ := h
    obtain ⟨eH, heH, he⟩ := symmetricSix_of_augmentation_extension (Source.starImage H K) ρ
      (faithful_of_centralizer_le_core ρ hρ hcentralizer)
      (componentModelEquiv hKH hK eK) eV (fun k v => by
        simpa only [modelActor_componentModelEquiv] using
          heV (componentModelEquiv hKH hK eK k) v) t ht
    exact Or.inr ⟨eH, eV, heH, he⟩

/-- The recognized seven-letter section identifies the whole module with the
six-dimensional core, equivariantly for the original component marking. -/
theorem seven_core_of_section
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 7)) eK) :
    ∃ eV : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 7),
      ∀ k : Source.starImage H K, ∀ v, eV (ρ k v) =
        BinaryPermutation.alternatingCoreRepresentation (Fin 7)
          (componentModelEquiv hKH hK eK k) (eV v) := by
  obtain ⟨e, he⟩ := alternatingSeven_module_of_section hKH hK ρ hρ hgen eK hs
  let c := BinaryPermutation.coreEquivNatural (Fin 7) (by decide : Odd (Fintype.card (Fin 7)))
  refine ⟨e.trans c.symm, ?_⟩
  intro k v
  apply c.injective
  change c (c.symm (e (ρ k v))) =
    c (BinaryPermutation.alternatingCoreRepresentation (Fin 7)
      (componentModelEquiv hKH hK eK k) (c.symm (e v)))
  rw [c.apply_symm_apply]
  change e (ρ k v) = c (BinaryPermutation.coreRepresentation (Fin 7)
    (componentModelEquiv hKH hK eK k).val (c.symm (e v)))
  rw [BinaryPermutation.coreEquivNatural_equivariant, c.apply_symm_apply]
  simpa only [modelActor_componentModelEquiv,
    BinaryPermutation.alternatingNaturalRepresentation, MonoidHom.comp_apply,
    Subgroup.coe_subtype] using he (componentModelEquiv hKH hK eK k) v

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

end
