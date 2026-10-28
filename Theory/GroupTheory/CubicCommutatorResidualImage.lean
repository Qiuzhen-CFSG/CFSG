module
public import Theory.GroupTheory.CubicCommutatorResidual
public import Theory.GroupTheory.Commutator.SylowNormalGeneration
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.SylowNormalGenerationFrattini
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual

/-!
# Commutator residual images in the symmetric-three pair

A Sylow two-subgroup normally generates a product of two symmetric-three
factors. The normal two-residual therefore equals its commutator with this
Sylow. Surjective residual transport identifies the exact source subgroup
O²([O²(G),P]) when P covers the image Sylow.

Source: Aschbacher--Smith15.1.11, printed p.1089.
-/

public section
open Subgroup
namespace Subgroup
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]

theorem cubicCommutatorResidual_map_of_symmetricThree_pair
    (f : G →* D) (hf : Function.Surjective f)
    (e : D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (P : Subgroup G) (S : Sylow 2 D) (hP : P.map f = S) :
    (cubicCommutatorResidual P).map f = pResidual 2 D := by
  have hS : normalClosure (S : Set D) = ⊤ := by
    apply (map_injective (f := e.toMonoidHom) e.injective)
    rw [map_normalClosure _ _ e.surjective,map_top_of_surjective _ e.surjective]
    exact normalClosure_sylow_eq_top_of_involutions (S.mapSurjective e.surjective)
      (symmetric_product_involutions_generate (Fin 3) (Fin 3))
  have hcomm : ⁅pResidual 2 D,(S : Subgroup D)⁆ = pResidual 2 D :=
    (eq_commutator_of_sylow_normal_generation S (pResidual 2 D) (S : Subgroup D) ⊥
      (pResidual_sup_sylow_eq_top S) (isPPerfect_pResidual 2) (S : Subgroup D).le_normalizer
      bot_le (by rw [sup_bot_eq]) hS).symm
  change ((pResidual 2 (⁅pResidual 2 G,P⁆ : Subgroup G)).map _).map f = _
  rw [map_embedded_pResidual,map_commutator,map_pResidual_of_surjective 2 f hf,hP,hcomm]
  rw [(pResidual_eq_top_iff 2 _).mpr (isPPerfect_pResidual 2)]
  exact (MonoidHom.range_eq_map _).symm.trans (range_subtype _)

end Subgroup
