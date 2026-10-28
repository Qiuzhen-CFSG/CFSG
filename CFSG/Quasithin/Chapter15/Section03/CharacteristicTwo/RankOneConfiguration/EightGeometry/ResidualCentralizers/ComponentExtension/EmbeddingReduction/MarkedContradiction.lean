module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.ComponentExtension.EmbeddingReduction.Placement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.ComponentExtension.EmbeddingReduction.Transport

/-!
# Comparing the containing-component action with the marked star action

The actual image of L in C/O₂(C) has two-core quotient A₈, by the marked
component equivalence and the exact kernel of the restricted projection.
Inner stabilizer action in a normal containing component lifts first inside
C and then to G, where it contradicts the marked S₈ action. Thus any proved
proper-embedding branch supplying that stabilizer action is impossible.

Source: Aschbacher–Smith, proof of 15.3.32(3), printed pp.1132–1133.
This is an action adapter; the full A.3.12 case elimination remains separate.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ComponentExtension.EmbeddingReduction
open Chapter1 Chapter1.Section02 Chapter1.Terminal Chapter1.Terminal.LinearFourActions
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The section of the actual image carries the marked A₈ isomorphism. -/
noncomputable def imageCoreEquivEight (d : LocalData G) {I C : Subgroup G}
    (c : ComponentWitness d I) (hLC : c.L ≤ C) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S)
    (hc : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hm : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8)) :
    XiQuotient (twoQuotientImage c.L C) ≃* alternatingGroup (Fin 8) :=
  (imageSectionEquiv hLC).symm.trans (componentCoreEquivEightOfModule d c P hP hc e hm)

/-- The non-inner marked Sylow action is unchanged when computed inside C. -/
theorem sylow_not_le_inner_subgroupOf (d : LocalData G) {I C : Subgroup G}
    (c : ComponentWitness d I) (hLC : c.L ≤ C)
    (hn : (c.L.subgroupOf I).Normal) (hj : I = c.L ⊔ d.S)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (T : Sylow 2 C) (hT : (T : Subgroup C).map C.subtype = d.S)
    (hc : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hm : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8)) :
    ¬ (T : Subgroup C) ≤ innerTwoQuotientNormalizer (c.L.subgroupOf C) := by
  have hSC : d.S ≤ C := hT ▸ map_subtype_le (T : Subgroup C)
  have hTeq : (T : Subgroup C) = d.S.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [map_subgroupOf_eq_of_le hSC]
    exact hT
  have hSL : d.S ≤ normalizer (c.L : Set G) :=
    (show d.S ≤ I from hj ▸ le_sup_right).trans
      ((normal_subgroupOf_iff_le_normalizer (component_le c)).mp hn)
  intro hi
  rw [hTeq] at hi
  exact sylow_not_le_innerNormalizer d c hn hj P hP hc e hm
    (le_innerNormalizer_of_subgroupOf hLC hSC hSL hi)

/-- A normal containing component with inner two-stabilizer action contradicts
this section's actual marking. All action lifting uses the original inclusions. -/
theorem contradiction_of_containing_image_inner (d : LocalData G) {I C : Subgroup G}
    (c : ComponentWitness d I) (hLC : c.L ≤ C)
    (hn : (c.L.subgroupOf I).Normal) (hj : I = c.L ⊔ d.S)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (T : Sylow 2 C) (hT : (T : Subgroup C).map C.subtype = d.S)
    (hc : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hm : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8))
    (K : Subgroup C) (hBK : c.L.subgroupOf C ≤ K) (hK : K.Normal)
    (hi : TwoStabilizerActsInner (twoQuotientImage (c.L.subgroupOf C) K)) : False := by
  have hSL : d.S ≤ normalizer (c.L : Set G) :=
    (show d.S ≤ I from hj ▸ le_sup_right).trans
      ((normal_subgroupOf_iff_le_normalizer (component_le c)).mp hn)
  have hTB : (T : Subgroup C) ≤ normalizer (c.L.subgroupOf C : Set C) := by
    rw [← subgroupOf_normalizer_eq hLC]
    intro t ht
    exact hSL (hT ▸ mem_map_of_mem C.subtype ht)
  let := hK
  exact sylow_not_le_inner_subgroupOf d c hLC hn hj P hP T hT hc e hm
    (le_innerNormalizer_of_image_stabilizer hBK T.isPGroup' hTB
      le_normalizer_of_normal hi)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ComponentExtension.EmbeddingReduction
