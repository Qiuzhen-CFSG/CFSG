module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.Contracts
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.Elementary
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.NormalizerAction
public import Theory.SpecificGroups.AlternatingSix.ElementaryAbelian

/-!
# The elementary nine inside the normalizer of E

The actual A₆ complement supplies an elementary subgroup of order nine.
Its index in N(E), whose order is 16 · 360, is prime to three, so it is
Sylow in that normalizer. Conjugacy of these local Sylow subgroups gives
one containing the marked element c. This uses no ambient Sylow-three
conclusion or ambient order.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 3, printed p.7.
-/

open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- The A₆ normalizer complement gives an elementary nine containing c. -/
public theorem exists_elementary_nine_in_normalizer_E
    (hE : ∃ K : Subgroup (normalizer (CaseII.E D k : Set G)),
      ((CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G))).IsComplement' K ∧
        Nonempty (K ≃* alternatingGroup (Fin 6))) :
    ∃ P : Subgroup G, P ≤ normalizer (CaseII.E D k : Set G) ∧
      IsElementaryAbelian 3 P ∧ Nat.card P = 9 ∧ CaseII.into D k CaseII.c ∈ P := by
  let N := normalizer (CaseII.E D k : Set G)
  let B := (CaseII.E D k).subgroupOf N
  obtain ⟨K, hK, ⟨eK⟩⟩ := hE
  have hN : Nat.card N = 5760 := by
    have hcB : Nat.card B = 16 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe (CaseII.E D k).le_normalizer).toEquiv]
      exact CaseII.E_card D k
    have hcK : Nat.card K = 360 := by
      rw [Nat.card_congr eK.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    have hh := B.card_mul_index
    rw [hcB, hK.symm.index_eq_card, hcK] at hh
    exact hh.symm
  obtain ⟨A, hA, hcA⟩ := alternatingGroup.exists_elementaryAbelian_nine_of_equiv eK
  let := hA
  let R := A.map K.subtype
  have hR : IsElementaryAbelian 3 R := IsElementaryAbelian.map _
  have hcR : Nat.card R = 9 := (card_map_of_injective K.subtype_injective).trans hcA
  have hiR : ¬3 ∣ R.index := by
    have hi := R.index_mul_card
    rw [hcR, hN] at hi
    have : R.index = 640 := by omega
    rw [this]
    decide
  let := hR
  let T : Sylow 3 N := (IsElementaryAbelian.isPGroup 3 R).toSylow hiR
  let cN : N := ⟨CaseII.into D k CaseII.c,
    CaseII.centralizer_le_normalizer_E D k (k CaseII.c).property⟩
  have hcN : orderOf cN = 3 := by
    rw [← orderOf_coe cN]
    exact (orderOf_injective (CaseII.into D k) (CaseII.into_injective D k) CaseII.c).trans
      CaseII.actor_orders.2.2.1
  have hQ : IsPGroup 3 (zpowers cN) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hcN, pow_one])
  obtain ⟨S, hS⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N T S
  have he : (S : Subgroup N) = R.map (MulAut.conj g).toMonoidHom :=
    (congrArg Sylow.toSubgroup hg).symm
  have hSe : IsElementaryAbelian 3 (S : Subgroup N) := by
    rw [he]
    exact IsElementaryAbelian.map _
  have hSc : Nat.card (S : Subgroup N) = 9 := by
    rw [he, card_map_of_injective (MulAut.conj g).injective, hcR]
  let := hSe
  refine ⟨(S : Subgroup N).map N.subtype, ?_, IsElementaryAbelian.map _, ?_, ?_⟩
  · exact (map_le_range _ _).trans_eq N.range_subtype
  · exact (card_map_of_injective N.subtype_injective).trans hSc
  · exact mem_map_of_mem N.subtype (hS (mem_zpowers cN))
end Theory.GroupTheory.HeldM22A10.M22Identification
