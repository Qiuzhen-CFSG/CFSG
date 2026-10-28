module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.Support.Normalizer
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.Projection
public import Theory.SpecificGroups.AlternatingFiveBorelProjection.PermutationAction
public import Theory.SpecificGroups.AlternatingFiveBorelProjection.SupportedTransposition
public import Theory.Representation.BinaryAlternatingFiveSupport
/-!
# The actual residual image equals its supported A₄ projection

In the faithful W_K action, a supported transposition has all commutators
inside K⁺. Its A₄ projection detects a nontrivial cubic commutator. Since
Lᵥ⁺ is two-perfect with cubic quotient by its two-core, it lies in K⁺.
The preceding projection therefore describes its whole action on W_K.
The supported actor is retained here for its independent source producer.
Source: Aschbacher–Smith, 13.6.15, printed p.930 (PDF p.947).
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed
open ComponentSelection ChapterB.QuasisimpleSource SourceContainment SourceContainment.LinearThree
open SourceContainment.LinearThree.CentralAction.ModuleAlternatives
variable {G : Type*} [Group G] [Finite G]
theorem residualPlus_le_component (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (I : Subrepresentation (componentRepresentation K L T z v hL hz))
    (e : ActionEquiv I.toRepresentation (alternatingNatural 5))
    (hs : IsCompl I.toSubmodule (fixedSpace (wkRepresentation K L T z v hL hz) (plusImage K L T z v hL hz K)))
    (f : Lv L v →* plusImage K L T z v hL hz K)
    (hf : ∀ (l : Lv L v) (k : plusImage K L T z v hL hz K),
      (f l : Gplus K L T z v hL hz)*k*(f l : Gplus K L T z v hL hz)⁻¹ =
      residualPlusMap K L T z v hL hz l*k*(residualPlusMap K L T z v hL hz l)⁻¹)
    (hB : f.range.map e.groupEquiv.toMonoidHom = BinaryPermutation.AlternatingFiveBorel.B)
    (r : Gplus K L T z v hL hz →* Equiv.Perm (Fin 5))
    (hr : ∀ c : plusImage K L T z v hL hz K, r c = (e.groupEquiv c).val)
    (he : ∀ g (w : I.toSubmodule), wkRepresentation K L T z v hL hz g w =
      (e.linearEquiv.symm (BinaryPermutation.naturalRepresentation (Fin 5) (r g) (e.linearEquiv w)) : Additive (WK K L T z v)))
    (hc : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (hcomm : ⁅plusImage K L T z v hL hz K,plusImage K L T z v hL hz (Lv L v)⁆ ≠ ⊥)
    (a : Gplus K L T z v hL hz) (ha : a ∈ plusImage K L T z v hL hz (Tv T v))
    (hat : (r a).IsSwap)
    (hasupport : ∀ w ∈ fixedSpace (wkRepresentation K L T z v hL hz) (plusImage K L T z v hL hz K),
      wkRepresentation K L T z v hL hz a w=w) :
    plusImage K L T z v hL hz (Lv L v) ≤ plusImage K L T z v hL hz K := by
  let C := plusImage K L T z v hL hz K
  let := plus_component_normal K L T z v hL hz hK hn
  let q := residualPlusMap K L T z v hL hz
  let H := q.range
  have hq : H = plusImage K L T z v hL hz (Lv L v) := residualPlusMap_range K L T z v hL hz
  have hne : H ≠ ⊥ := by
    intro hb
    apply hcomm
    rw [←hq,hb,commutator_bot_right]
  have hp : IsPPerfect 2 H := (isPPerfect_embedded_pResidual 2 (L ⊓ Gv v)).of_surjective
    q.rangeRestrict q.rangeRestrict_surjective
  have hcard : Nat.card (H ⧸ pCore 2 H)=3 := residual_image_core_quotient_card L v hc q hne
  have hperm (l : Lv L v) : r (q l)=(e.groupEquiv (f l)).val :=
    AlternatingFiveProjection.permutation_eq_projection C e.groupEquiv r hr q f hf l
  have hrange : H.map r = BinaryPermutation.AlternatingFiveBorel.B.map (alternatingGroup (Fin 5)).subtype := by
    rw [←hB]
    ext y
    constructor
    · rintro ⟨x,⟨l,rfl⟩,rfl⟩
      exact ⟨e.groupEquiv (f l),⟨f l,⟨l,rfl⟩,rfl⟩,(hperm l).symm⟩
    · rintro ⟨b,⟨c,⟨l,rfl⟩,rfl⟩,rfl⟩
      exact ⟨q l,⟨l,rfl⟩,hperm l⟩
  have han : a ∈ normalizer (H : Set _) := by
    rw [hq]
    apply le_normalizer_map (plusMk K L T z v hL hz)
    obtain ⟨t,ht,rfl⟩ := ha
    refine ⟨t,?_,rfl⟩
    exact le_normalizer_comap (plusActor K L T v).subtype (hL ht)
  rw [←hq]
  exact AlternatingFiveProjection.le_component_of_supported_transposition H C hp hcard r hrange a han hat
    (fun h _ => BinaryPermutation.AlternatingFiveSupport.commutator_mem_component
      (wkRepresentation K L T z v hL hz) (wkRepresentation_faithful K L T z v hL hz)
      C I.toSubmodule e.linearEquiv e.groupEquiv r hr he hs a hasupport h)
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed
