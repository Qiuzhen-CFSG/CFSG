module
public import CFSG.Quasithin.Chapter13.Section09.NormalizerStructure.Fusion
public import CFSG.Quasithin.Chapter13.Section09.NormalizerStructure.FullFusion
public import CFSG.Quasithin.Chapter13.Section09.NormalizerStructure.NaturalPoints

/-!
# Original-input normalizer geometry in source 13.9.9

All centralizer growth, transfer, native orbit and action premises have
been discharged. The actual normalizer quotient is S5; its action has
orbits of lengths five and ten on B minus identity, and the five-point
circuit marks the original t as a two-point product. The final named
Delta3/Delta5 selection is kept separate because the printed local
product assertion is false for the source coordinates.

Source: Aschbacher–Smith 13.9.9, printed pp.972–973.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section09
open Subgroup
variable {G:Type*} [Group G] [Finite G]

theorem source13_9_9_normalizer_complete {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (d:Configuration G) (m:Marking d) :
    Nat.card (normalizer (m.B:Set G))=1920 ∧ m.normalizerOrbit.ncard=5 ∧
      m.normalizerTOrbit.ncard=10 ∧
      Nonempty ((normalizer (m.B:Set G)⧸m.B.subgroupOf (normalizer (m.B:Set G)))≃*Equiv.Perm (Fin 5)) ∧
      Function.Surjective (m.normalizerS5Action hG) ∧
      (m.normalizerS5Action hG).ker=m.B.subgroupOf (normalizer (m.B:Set G)) ∧
      (∀x:G,orderOf x=2→IsConj m.z x ∨ IsConj m.t x) ∧
      IsConj m.z m.s ∧
      Subgroup.closure {x:G | x∈m.core ∧ IsConj m.t x}=m.B⊓m.core :=
  ⟨m.normalizer_card_1920 hG,m.normalizerOrbit_card_five hG,m.normalizerTOrbit_card_ten hG,
    ⟨m.normalizerQuotientS5 hG⟩,m.normalizerS5Action_surjective hG,m.normalizerS5Action_kernel hG,
    m.original_two_involution_classes hG,
    (source13_9_9_fusion hG d m).1,(source13_9_9_fusion hG d m).2.1⟩

/-- The original normalizer API, retained as a projection of the full source result. -/
theorem source13_9_9_normalizer {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (d:Configuration G) (m:Marking d) :
    Nat.card (normalizer (m.B:Set G))=1920 ∧ m.normalizerOrbit.ncard=5 ∧
      m.normalizerTOrbit.ncard=10 ∧
      Nonempty ((normalizer (m.B:Set G)⧸m.B.subgroupOf (normalizer (m.B:Set G)))≃*Equiv.Perm (Fin 5)) ∧
      Function.Surjective (m.normalizerS5Action hG) ∧
      (m.normalizerS5Action hG).ker=m.B.subgroupOf (normalizer (m.B:Set G)) ∧
      (∀x:G,orderOf x=2→IsConj m.z x ∨ IsConj m.t x) := by
  obtain ⟨hcard,hz,ht,he,hs,hk,hclasses,_,_⟩ :=
    source13_9_9_normalizer_complete hG d m
  exact ⟨hcard,hz,ht,he,hs,hk,hclasses⟩

end CFSG.Quasithin.Chapter13.Section09
