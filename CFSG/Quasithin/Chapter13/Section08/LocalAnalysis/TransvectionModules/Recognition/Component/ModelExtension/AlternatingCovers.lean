module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.CoverProjection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Cover
public import Theory.Representation.BinaryAlternatingNaturalCohomology

/-!
# Full alternating modules from the recognized component section

The constructed projection is a cover in the precise sense of I.1.5.
For A₆ the concrete augmentation comparison gives either the natural module
or its five-dimensional augmentation cover. For A₇ self-duality and H¹=0
make the projection injective, hence an equivariant linear equivalence.
In both cases the acting group is transported through the same prescribed
K/O₂(K) equivalence as in the recognized section.

These are full vector-space identifications with the restricted component
action. Extending that action to H*, proving normality and applying universal
13.7.6 under the standing source setup are still separate obligations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
I.1.5–6(1), printed p.408, and 13.8.5, printed p.947.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

variable {G : Type*} [Group G] [Finite G]
  {H V₃ V₁ K : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]

private theorem cover_injective_of_H1_dual_zero
    [Finite A] [FiniteDimensional (ZMod 2) E]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) A E} {τ : Representation (ZMod 2) A W}
    (p : τ.IntertwiningMap σ) (hp : IsCover p)
    (hH : Module.finrank (ZMod 2) (H1 σ.dual) = 0) : Function.Injective p := by
  let : FiniteDimensional (ZMod 2) (Module.Dual (ZMod 2) (cocycles σ.dual)) :=
    Subspace.instModuleDualFiniteDimensional (K := ZMod 2) (V := cocycles σ.dual)
  have hu : (universalCoverProjection σ).toLinearMap.ker = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    rw [finrank_ker_universalCoverProjection, hH]
  obtain ⟨q, hq, hqp⟩ := exists_universalCover_quotient p hp
  intro x y he
  obtain ⟨u, rfl⟩ := hq x
  obtain ⟨v, rfl⟩ := hq y
  apply congrArg q
  apply LinearMap.ker_eq_bot.mp hu
  exact (hqp u).symm.trans (he.trans (hqp v))

private theorem alternatingSeven_natural_dual_finrank_H1 :
    Module.finrank (ZMod 2)
      (H1 (BinaryPermutation.alternatingNaturalRepresentation (Fin 7)).dual) = 0 := by
  let E := H1Congr (BinaryPermutation.alternatingNaturalRepresentation (Fin 7))
    (BinaryPermutation.alternatingNaturalRepresentation (Fin 7)).dual
    (MulEquiv.refl (alternatingGroup (Fin 7))) (BinaryPermutation.naturalDualEquiv (Fin 7))
    (fun g v => BinaryPermutation.naturalDualEquiv_equivariant (Fin 7) g.val v)
  rw [← E.finrank_eq]
  exact BinaryPermutation.alternatingSeven_natural_finrank_H1

/-- The full source module is natural or augmentation for the same A₆ actor. -/
theorem alternatingSix_module_of_section
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK) :
    (∃ e : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6),
      ∀ a v, e (ρ (modelActor hKH hK eK a) v) =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 6) a (e v)) ∨
    (∃ e : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 6),
      ∀ a v, e (ρ (modelActor hKH hK eK a) v) =
        BinaryPermutation.alternatingCoreRepresentation (Fin 6) a (e v)) := by
  let : Module.Finite (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) := Module.Finite.of_finite
  obtain ⟨p, hp⟩ := exists_cover_of_section hKH hK ρ hρ hgen _ eK hs
  rcases ComponentSieve.SixAndG2.natural_or_augmentation_of_cover p hp with h | h
  · obtain ⟨e, he, _⟩ := h
    exact Or.inl ⟨e, he⟩
  · obtain ⟨e, he, _⟩ := h
    exact Or.inr ⟨e, he⟩

/-- Vanishing of H¹ rules out a nontrivial central cover of the natural A₇ module. -/
theorem alternatingSeven_module_of_section
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 7)) eK) :
    ∃ e : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 7),
      ∀ a v, e (ρ (modelActor hKH hK eK a) v) =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 7) a (e v) := by
  let : Module.Finite (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) := Module.Finite.of_finite
  obtain ⟨p, hp⟩ := exists_cover_of_section hKH hK ρ hρ hgen _ eK hs
  let e := LinearEquiv.ofBijective p.toLinearMap
    ⟨cover_injective_of_H1_dual_zero p hp alternatingSeven_natural_dual_finrank_H1, hp.1⟩
  exact ⟨e, fun a v => LinearMap.congr_fun (p.isIntertwining' a) v⟩

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
