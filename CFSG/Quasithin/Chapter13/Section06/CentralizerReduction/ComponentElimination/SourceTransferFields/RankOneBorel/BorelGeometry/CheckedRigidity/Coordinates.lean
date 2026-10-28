module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BlockRigidity

/-!
# Aligning the block model with the actual Borel

The component Sylow maps to a Sylow subgroup of SL₂. Conjugate its actor
and module coordinates together to obtain the upper unipotent Sylow;
the relative normalizer defining the Borel then maps onto the standard
Borel. The existing natural-layer rigidity applies in these coordinates,
without an extra compatibility assumption.

Source: Aschbacher–Smith, proof of 13.6.18, printed p.931 (PDF p.948).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.CheckedRigidity
open Subgroup ChapterC Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

private def conjugateModel {K : Type*} [Group K]
    (ρ : SL(2,F) →* MulAut (Multiplicative (Fin 2 → F)))
    (m : BlockModuleModel K ρ) (g : SL(2,F)) : BlockModuleModel K ρ where
  quotientIso := m.quotientIso.trans (MulAut.conj g)
  moduleIso := m.moduleIso.trans (ρ g)
  intertwining k u := by
    change ρ g (m.moduleIso _) = ρ (g * m.quotientIso _ * g⁻¹) (ρ g (m.moduleIso _))
    rw [m.intertwining]
    simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply_self]

/-- Simultaneous actor/module conjugation marks the actual relative Borel. -/
theorem exists_marked_model (K S : Subgroup G)
    (hSK : S ≤ normalizer (K : Set G))
    (hSylow : Chapter1.IsSylowIn 2 S (K ⊔ S))
    (ρ : SL(2,F) →* MulAut (Multiplicative (Fin 2 → F)))
    (m : BlockModuleModel K ρ) :
    ∃ m' : BlockModuleModel K ρ,
      ((borel K S).subgroupOf K).map
        (m'.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) = rankOneBorel F := by
  obtain ⟨P, hP⟩ := exists_component_sylow K S hSylow hSK
  let q := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  let Pq := P.mapSurjective hq
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2,F) Pq (upperUnipotentSylow F 2)
  have hU : ((P : Subgroup K).map q).map (MulAut.conj g).toMonoidHom =
      upperUnipotent F := congrArg Sylow.toSubgroup hg
  refine ⟨conjugateModel ρ m g, ?_⟩
  change ((borel K S).subgroupOf K).map ((MulAut.conj g).toMonoidHom.comp q) = _
  rw [← Subgroup.map_map, borel_subgroupOf, ← hP]
  change ((normalizer (P : Set K)).map q).map (MulAut.conj g).toMonoidHom = _
  rw [P.normalizer_map_surjective q hq,
    map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective, hU]

/-- The block's own natural coordinates suffice for the literal Borel. -/
theorem centralizes_of_natural_borel_fixation (K S : Subgroup G)
    (hSK : S ≤ normalizer (K : Set G))
    (hSylow : Chapter1.IsSylowIn 2 S (K ⊔ S))
    (ρ : SL(2,F) →* MulAut (Multiplicative (Fin 2 → F)))
    (m : BlockModuleModel K ρ)
    (hρ : ∀ (g : SL(2,F)) (w : Multiplicative (Fin 2 → F)),
      Multiplicative.toAdd (ρ g w) = g.val *ᵥ Multiplicative.toAdd w)
    (hF : 2 < Nat.card F) (a : G) (ha2 : a ^ 2 = 1) (haS : a ∈ S)
    (haB : a ∈ centralizer (borel K S : Set G)) :
    a ∈ centralizer (K : Set G) := by
  obtain ⟨m', hm'⟩ := exists_marked_model K S hSK hSylow ρ m
  exact BlockRigidity.centralizes_of_borel_fixation K S (borel K S) hSK hSylow
    (le_borel K S hSK) (borel_le K S) ρ m' hρ hF hm' a ha2 haS haB
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.CheckedRigidity
