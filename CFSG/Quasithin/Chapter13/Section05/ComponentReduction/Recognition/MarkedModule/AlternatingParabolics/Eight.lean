module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.Basic
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics.Common
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics.LinearGeneration
public import Theory.Representation.BinaryPermutationEightCover
public import CFSG.KnownSimple.CarrierCatalogue
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Augmentation-cover generation in the A₈ branch of 13.5.21

Normality of the selected component and simplicity of the supplied A₈ model
show that the actual K*V* is K*. The original central projection is therefore
a perfect central cover. The seven-dimensional augmentation core surjects onto
the whole original module, compatibly with that projection and the given
actor equivalence. The full module is not identified with its natural quotient.

A marked even pair stabilizer generates the augmentation core. This descends
to the original local product, then to its embedded two-residual L₁*, and
finally to the literal tilde-group commutator required by 13.5.14. These are
conditional generation applications: the pair-parabolic marking of the original
local product still requires the Sylow-invariant-plane recognition. The index
bound and discharge of that marking remain part of the A₈ source assembly.

The earlier seed identity and natural central-quotient coordinates are the
same inputs retained by `MarkedModule.CentralQuotient.source_central_quotient`.
The genuine setup, selected component, full proper-K hypothesis, and original
star and tilde maps are retained throughout.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.5.21(5),(6),
printed p.924 (PDF p.941), using I.1.5–6, printed p.408.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics
open Section08.Source
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
variable {G : Type*} [Group G] [Finite G]
  (D : ChapterF.Section09.Setup G) (h : D.Hypothesis) {K : Subgroup G}

include h in
/-- In the A₈ branch the actual component fills the actual model supplement. -/
theorem alternating_eight_actor_eq_component
    (s : Selected D K)
    (hSQ : IsStronglyQuasithin (Hstar D.H))
    (hLK : D.L₁ ≤ K)
    (hm : ⁅starImage D.H K, starImage D.H D.L₁⁆ ≠ ⊥)
    (e : (starImage D.H K ⊔ starImage D.H D.V : Subgroup (Hstar D.H)) ≃*
      alternatingGroup (Fin 8)) :
    starImage D.H K ⊔ starImage D.H D.V = starImage D.H K := by
  have hn := normal_in_H s h hSQ hLK hm
  let : (starImage D.H K).Normal := hn.map (QuotientGroup.mk' (pCore 2 D.H))
    (QuotientGroup.mk'_surjective _)
  let B := starImage D.H K ⊔ starImage D.H D.V
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup B := e.isSimpleGroup
  have ht : (starImage D.H K).subgroupOf B = ⊤ := by
    rcases (inferInstance : ((starImage D.H K).subgroupOf B).Normal).eq_bot_or_eq_top
      with hb | ht
    · have hz : starImage D.H K = ⊥ := by
        have he := congrArg (Subgroup.map B.subtype) hb
        simpa only [map_subgroupOf_eq_of_le (show starImage D.H K ≤ B from le_sup_left),
          Subgroup.map_bot] using he
      exact (hm (by rw [hz, commutator_bot_left])).elim
    · exact ht
  exact le_antisymm (subgroupOf_eq_top.mp ht) le_sup_left

variable [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]

/-- The seven-dimensional augmentation core covers the original whole module,
over the literal central projection and the given A₈ marking. -/
theorem alternating_eight_core_quotient
    (s : Selected D K)
    (_proper : HasProperKSubgroups KnownSimple.IsKnownSimple G)
    (hSQ : IsStronglyQuasithin (Hstar D.H))
    (hLK : D.L₁ ≤ K)
    (hm : ⁅starImage D.H K, starImage D.H D.L₁⁆ ≠ ⊥)
    (hseed : D.Vplus = ⁅D.V, D.L₁⁆)
    (e : (starImage D.H K ⊔ starImage D.H D.V : Subgroup (Hstar D.H)) ≃*
      alternatingGroup (Fin 8))
    (eV : (Action.Space D ⧸ fixedSpace (Action.starRepresentation D h)
      (starImage D.H K)) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8))
    (heV : ∀ b : (starImage D.H K ⊔ starImage D.H D.V : Subgroup (Hstar D.H)),
      ∀ u, centralProjection D h eV (Action.starRepresentation D h b.val u) =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (e b)
          (centralProjection D h eV u)) :
    ∃ f : BinaryPermutation.core (Fin 8) →ₗ[ZMod 2] Action.Space D,
      Function.Surjective f ∧
      (∀ b : (starImage D.H K ⊔ starImage D.H D.V : Subgroup (Hstar D.H)), ∀ v,
        f (BinaryPermutation.alternatingCoreRepresentation (Fin 8) (e b) v) =
          Action.starRepresentation D h b.val (f v)) ∧
      ∀ v, centralProjection D h eV (f v) = BinaryPermutation.coreToNatural (Fin 8) v := by
  have hB := alternating_eight_actor_eq_component D h s hSQ hLK hm e
  apply BinaryPermutation.EightCover.core_quotient_of_marked_cover
    (Action.starRepresentation D h) _ e (centralProjection D h eV) heV
  · exact eV.surjective.comp (Submodule.mkQ_surjective _)
  · rw [centralProjection_ker, hB]
  · rw [hB]
    exact linear_generation D h s hLK (normal_in_H s h hSQ hLK hm) hseed

/-- Once the model geometry marks the original local product, the augmentation
cover calculation gives full linear L₁-generation, including central extensions. -/
theorem alternating_eight_linear_generation_of_pair_marking
    (s : Selected D K)
    (_proper : HasProperKSubgroups KnownSimple.IsKnownSimple G)
    (hSQ : IsStronglyQuasithin (Hstar D.H))
    (hLK : D.L₁ ≤ K)
    (hm : ⁅starImage D.H K, starImage D.H D.L₁⁆ ≠ ⊥)
    (hseed : D.Vplus = ⁅D.V, D.L₁⁆)
    (e : (starImage D.H K ⊔ starImage D.H D.V : Subgroup (Hstar D.H)) ≃*
      alternatingGroup (Fin 8))
    (eV : (Action.Space D ⧸ fixedSpace (Action.starRepresentation D h)
      (starImage D.H K)) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8))
    (heV : ∀ b : (starImage D.H K ⊔ starImage D.H D.V : Subgroup (Hstar D.H)),
      ∀ u, centralProjection D h eV (Action.starRepresentation D h b.val u) =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (e b)
          (centralProjection D h eV u))
    (g : alternatingGroup (Fin 8))
    (hmark : ((localStar D).subgroupOf (starImage D.H K ⊔ starImage D.H D.V)).map
      e.toMonoidHom = (pairStabilizer.subgroupOf (alternatingGroup (Fin 8))).map
        (MulAut.conj g).toMonoidHom) :
    subspaceCommutator (Action.starRepresentation D h) ⊤ (starImage D.H D.L₁) = ⊤ := by
  obtain ⟨f, hf, he, _⟩ := alternating_eight_core_quotient D h s _proper hSQ hLK hm
    hseed e eV heV
  have hg := BinaryPermutation.EightCover.generation_of_core_surjection
    (Action.starRepresentation D h) _ (localStar D) e f hf he g hmark
  have hr := commutator_pResidual_eq_top (Action.starRepresentation D h) (localStar D) hg
  rwa [localStar_twoResidual D h] at hr

/-- Literal tilde-group application for 13.5.21(6) and the hypotheses of 13.5.14.
The only remaining model input is the marked pair-parabolic geometry. -/
theorem alternating_eight_tilde_generation_of_pair_marking
    (s : Selected D K)
    (_proper : HasProperKSubgroups KnownSimple.IsKnownSimple G)
    (hSQ : IsStronglyQuasithin (Hstar D.H))
    (hLK : D.L₁ ≤ K)
    (hm : ⁅starImage D.H K, starImage D.H D.L₁⁆ ≠ ⊥)
    (hseed : D.Vplus = ⁅D.V, D.L₁⁆)
    (e : (starImage D.H K ⊔ starImage D.H D.V : Subgroup (Hstar D.H)) ≃*
      alternatingGroup (Fin 8))
    (eV : (Action.Space D ⧸ fixedSpace (Action.starRepresentation D h)
      (starImage D.H K)) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8))
    (heV : ∀ b : (starImage D.H K ⊔ starImage D.H D.V : Subgroup (Hstar D.H)),
      ∀ u, centralProjection D h eV (Action.starRepresentation D h b.val u) =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (e b)
          (centralProjection D h eV u))
    (g : alternatingGroup (Fin 8))
    (hmark : ((localStar D).subgroupOf (starImage D.H K ⊔ starImage D.H D.V)).map
      e.toMonoidHom = (pairStabilizer.subgroupOf (alternatingGroup (Fin 8))).map
        (MulAut.conj g).toMonoidHom) :
    D.tilde D.UH = ⁅D.tilde D.UH, D.tilde D.L₁⁆ :=
  local_tilde_generation_of_linear D h
    (alternating_eight_linear_generation_of_pair_marking D h s _proper hSQ hLK hm hseed
      e eV heV g hmark)

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics
