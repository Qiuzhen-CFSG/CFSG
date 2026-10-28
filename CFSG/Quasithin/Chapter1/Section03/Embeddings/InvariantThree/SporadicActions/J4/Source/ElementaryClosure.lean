module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum

/-!
# The elementary closure in the original J₄ Sylow overgroup

A nontrivial two-core in any overgroup H of a full Sylow two-subgroup S
makes the H-normal closure of Z(S) elementary and minimal H-normal. Its
ambient image is therefore irreducible under its full normalizer. The checked
outside-kernel catalogue puts that image in the literal Mathieu kernel.

A kernel element in the second involution class puts the full normalizer in
max1. Otherwise the exhaustive pure-kernel catalogue leaves just four actual
subgroups, of orders two, four, eight and eight: the trivial row is impossible,
and the order-sixteen row has a proper normalizer-invariant subgroup.

No maximality of H or of its elementary subgroup's normalizer is assumed.
This is the pair-specific structural reduction for Aschbacher–Smith,
Proposition 1.3.4, printed p.511. The concrete catalogue and normalizer proofs
are the checked matrix calculations in the cited A.3.12 source modules.
-/

public section

open Subgroup
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
open Janko4 Janko4.OuterReduction.OddIndex
attribute [local irreducible] Janko4.modelGroup matrixA matrixB

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Source

@[expose] def elementaryClosure (S : Sylow 2 Model) (H : Subgroup Model) (hSH : S.toSubgroup ≤ H) :=
  (centralClosure S H hSH).map H.subtype

theorem overgroup_le_elementaryClosure_normalizer (S : Sylow 2 Model) (H : Subgroup Model)
    (hSH : S.toSubgroup ≤ H) : H ≤ normalizer (elementaryClosure S H hSH : Set Model) := by
  simpa only [elementaryClosure, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
    (centralClosure S H hSH).le_normalizer_map H.subtype

theorem elementaryClosure_normalizer_irreducible (S : Sylow 2 Model) (H : Subgroup Model)
    (hSH : S.toSubgroup ≤ H) (hcore : pCore 2 H ≠ ⊥) :
    ClosureNormalizerIrreducible (elementaryClosure S H hSH) := by
  let _ := centralClosure_elementary_of_twoCore_ne_bot S H hSH hcore
  intro B hBE hBN
  have hBH : B ≤ H := hBE.trans (map_subtype_le _)
  have hHN : H ≤ normalizer (B : Set Model) :=
    (overgroup_le_elementaryClosure_normalizer S H hSH).trans hBN
  have hBn : (B.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hBH).mpr hHN
  let _ := hBn
  have hle : B.subgroupOf H ≤ centralClosure S H hSH := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hBH]
    exact hBE
  rcases centralClosure_minimal S H hSH (B.subgroupOf H) hle with hb | he
  · left
    rw [← map_subgroupOf_eq_of_le hBH, hb, Subgroup.map_bot]
  · right
    rw [← map_subgroupOf_eq_of_le hBH, he]
    rfl

theorem elementaryClosure_ne_bot (S : Sylow 2 Model) (H : Subgroup Model)
    (hSH : S.toSubgroup ≤ H) : elementaryClosure S H hSH ≠ ⊥ := by
  intro he
  exact centralClosure_ne_bot S H hSH
    ((map_eq_bot_iff_of_injective _ H.subtype_injective).mp he)

theorem elementaryClosure_elementary (S : Sylow 2 Model) (H : Subgroup Model)
    (hSH : S.toSubgroup ≤ H) (hcore : pCore 2 H ≠ ⊥) :
    IsElementaryAbelian 2 (elementaryClosure S H hSH) := by
  let _ := centralClosure_elementary_of_twoCore_ne_bot S H hSH hcore
  exact IsElementaryAbelian.map H.subtype

theorem elementaryClosure_le_sylow (S : Sylow 2 Model) (H : Subgroup Model)
    (hSH : S.toSubgroup ≤ H) (hcore : pCore 2 H ≠ ⊥) :
    elementaryClosure S H hSH ≤ S.toSubgroup := by
  let _ := centralClosure_elementary_of_twoCore_ne_bot S H hSH hcore
  rintro x ⟨y, hy, rfl⟩
  exact centralClosure_le_restrictedSylow S H hSH hy

theorem elementaryClosure_le_kernel (S : Sylow 2 Model) (H : Subgroup Model)
    (hSH : S.toSubgroup ≤ H) (hS : S.toSubgroup = twoSubgroup)
    (hcore : pCore 2 H ≠ ⊥) : elementaryClosure S H hSH ≤ orderSpectrumKernel := by
  apply elementary_sylow_le_kernel_of_outside_certificates
    Janko4.LocalStructure.SylowNormalEights.MatrixWords.pcGenerator_relations
    Janko4.LocalStructure.SylowNormalEights.MatrixWords.pcGenerator_closure
    (OutsideKernelOrders.outsideCatalogue_of_card
      OutsideKernelOrders.MatrixCertificates.presentation_card)
    OutsideKernelOrders.matrixKernel_eq_orderSpectrumKernel
    OutsideKernelOrders.rankCertificates
    (elementaryClosure S H hSH)
  · exact (elementaryClosure_le_sylow S H hSH hcore).trans hS.le
  · exact hS ▸ hSH.trans (overgroup_le_elementaryClosure_normalizer S H hSH)
  · exact elementaryClosure_elementary S H hSH hcore
  · exact elementaryClosure_normalizer_irreducible S H hSH hcore

theorem elementaryClosure_catalogue (S : Sylow 2 Model) (H : Subgroup Model)
    (hSH : S.toSubgroup ≤ H) (hS : S.toSubgroup = twoSubgroup)
    (hcore : pCore 2 H ≠ ⊥) :
    H ≤ Janko4.Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four ∨
      elementaryClosure S H hSH = KernelOrders.candidate 1 ∨ elementaryClosure S H hSH = KernelOrders.candidate 2 ∨
      elementaryClosure S H hSH = KernelOrders.candidate 3 ∨ elementaryClosure S H hSH = KernelOrders.candidate 4 := by
  have hEK := elementaryClosure_le_kernel S H hSH hS hcore
  by_cases hp : ∀ u ∈ elementaryClosure S H hSH, ¬ IsConj u KernelOrders.classSeed
  · obtain ⟨i, hi⟩ := KernelOrders.pureKernelCatalogue.1 (elementaryClosure S H hSH) hEK
      (hS ▸ hSH.trans (overgroup_le_elementaryClosure_normalizer S H hSH)) hp
    fin_cases i
    · exact (elementaryClosure_ne_bot S H hSH (hi.trans KernelOrders.candidate_zero)).elim
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr (Or.inl hi))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hi)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hi)))
    · have hirr := elementaryClosure_normalizer_irreducible S H hSH hcore
      rw [hi] at hirr
      obtain ⟨B, hBlt, hBne, hBN⟩ := KernelOrders.PureNormalizers.candidate_five_obstruction
      rcases hirr B hBlt.le hBN with hb | he
      · exact (hBne hb).elim
      · exact (hBlt.ne he).elim
  · push Not at hp
    obtain ⟨u, hu, hc⟩ := hp
    exact Or.inl ((overgroup_le_elementaryClosure_normalizer S H hSH).trans
      (KernelOrders.normalizer_le_max1_of_seed_conjugate _ hEK u hu hc))

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Source
