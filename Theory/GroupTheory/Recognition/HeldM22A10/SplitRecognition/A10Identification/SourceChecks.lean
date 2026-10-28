module

public import Theory.GroupTheory.Recognition.HeldM22A10.Setup
public import Theory.GroupTheory.Recognition.HeldM22A10.LocalStructure
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.CentralizerModels
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Matching the hypotheses of Held's A10 characterization

Simplicity and the centralizer order exclude subgroups of index two. An
isomorphism of the specified centralizer with the concrete A10 centralizer
necessarily preserves the distinguished involution: each is the unique
involution in the center. We obtain an injective map of the concrete local
group into G, with range exactly the original centralizer.

The concrete element (01)(23)(45)(67) is central in a Sylow two-subgroup of
A10. Here its Sylow subgroup is transported from the supplied local data;
the order calculation uses |A10| = 10!/2 and the already proved local
Sylow order 128. Thus no choice of local-group isomorphism adds a marking
hypothesis to the recognition problem. The double transposition (01)(23)
specifies the representative of the other model class used by the remaining proof.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Theorem B and Section 1, pp.224--225.
This module proves the input checks, not the characterization theorem.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10
universe u
namespace A10Identification

@[expose] public def modelCentralInvolution : CentralizerModels.a10Centralizer :=
  ⟨CentralizerModels.a10Involution, mem_centralizer_singleton_iff.mpr rfl⟩

@[expose] public def doubleTransposition : alternatingGroup (Fin 10) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
    rw [Equiv.Perm.mem_alternatingGroup]
    simp [Equiv.Perm.sign_swap']⟩

public theorem doubleTransposition_order : orderOf doubleTransposition = 2 := by
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

public theorem doubleTransposition_mem_centralizer :
    doubleTransposition ∈ CentralizerModels.a10Centralizer := by
  apply mem_centralizer_singleton_iff.mpr
  decide +kernel

@[expose] public def modelNoncentralInvolution : CentralizerModels.a10Centralizer :=
  ⟨doubleTransposition, doubleTransposition_mem_centralizer⟩

public theorem modelCentralInvolution_mem_center :
    modelCentralInvolution ∈ center CentralizerModels.a10Centralizer := by
  apply mem_center_iff.mpr
  intro x
  exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property)

end A10Identification
namespace LocalData
open A10Identification
variable {G : Type u} [Group G] (D : LocalData G)

include D in
public theorem no_index_two [Finite G] [IsSimpleGroup G] (L : Subgroup G) : L.index ≠ 2 := by
  intro hL
  rcases (normal_of_index_eq_two hL).eq_bot_or_eq_top with hbot | htop
  · have hG : Nat.card G = 2 := by simpa [hbot] using hL
    have hcard := Subgroup.card_le_card_group D.centralizer
    rw [D.centralizer_card, hG] at hcard
    omega
  · simp [htop] at hL

public theorem a10Equiv_centralInvolution [Finite G]
    (e : D.centralizer ≃* CentralizerModels.a10Centralizer) :
    e D.centralInvolution = modelCentralInvolution := by
  have hcent : e.symm modelCentralInvolution ∈ center D.centralizer := by
    apply mem_center_iff.mpr
    intro x
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      mem_center_iff.mp modelCentralInvolution_mem_center (e x)
  let : IsCyclic (center D.centralizer) := by
    rw [D.center_eq_zpowers]
    infer_instance
  have hx : orderOf (⟨e.symm modelCentralInvolution, hcent⟩ : center D.centralizer) = 2 := by
    simp only [Subgroup.orderOf_mk, e.symm.orderOf_eq]
    simpa only [modelCentralInvolution, Subgroup.orderOf_mk] using
      CentralizerModels.a10Involution_order
  have hy : orderOf (⟨D.centralInvolution, D.centralInvolution_mem_center⟩ :
      center D.centralizer) = 2 := by
    simpa only [Subgroup.orderOf_mk, centralInvolution] using D.z_order
  have heq := IsCyclic.eq_of_orderOf_eq_two hx hy
  have heq' : e.symm modelCentralInvolution = D.centralInvolution :=
    congrArg Subtype.val heq
  exact (e.symm_apply_eq.mp heq').symm

@[expose] public noncomputable def a10ModelEmbedding
    (e : D.centralizer ≃* CentralizerModels.a10Centralizer) :
    CentralizerModels.a10Centralizer →* G := D.centralizer.subtype.comp e.symm.toMonoidHom

public theorem a10ModelEmbedding_injective
    (e : D.centralizer ≃* CentralizerModels.a10Centralizer) :
    Function.Injective (D.a10ModelEmbedding e) :=
  Subtype.val_injective.comp e.symm.injective

public theorem a10ModelEmbedding_central [Finite G]
    (e : D.centralizer ≃* CentralizerModels.a10Centralizer) :
    D.a10ModelEmbedding e modelCentralInvolution = D.z := by
  have h := e.symm_apply_eq.mpr (D.a10Equiv_centralInvolution e).symm
  exact congrArg Subtype.val h

public theorem a10ModelEmbedding_range
    (e : D.centralizer ≃* CentralizerModels.a10Centralizer) :
    (D.a10ModelEmbedding e).range = D.centralizer := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (e.symm y).property
  · intro hx
    exact ⟨e ⟨x, hx⟩, congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)⟩

@[expose] public noncomputable def a10NoncentralInvolution
    (e : D.centralizer ≃* CentralizerModels.a10Centralizer) : G :=
  D.a10ModelEmbedding e modelNoncentralInvolution

public theorem a10NoncentralInvolution_mem
    (e : D.centralizer ≃* CentralizerModels.a10Centralizer) :
    D.a10NoncentralInvolution e ∈ D.centralizer := (e.symm modelNoncentralInvolution).property

public theorem a10NoncentralInvolution_order
    (e : D.centralizer ≃* CentralizerModels.a10Centralizer) :
    orderOf (D.a10NoncentralInvolution e) = 2 := by
  rw [a10NoncentralInvolution, orderOf_injective (D.a10ModelEmbedding e) (D.a10ModelEmbedding_injective e)]
  simpa only [modelNoncentralInvolution, Subgroup.orderOf_mk] using doubleTransposition_order

public theorem a10_model_involution_central_in_sylow [Finite G]
    (e : D.centralizer ≃* CentralizerModels.a10Centralizer) :
    ∃ (S : Sylow 2 (alternatingGroup (Fin 10)))
      (hz : CentralizerModels.a10Involution ∈ S),
      (⟨CentralizerModels.a10Involution, hz⟩ : S) ∈ center S := by
  let f : D.centralizer →* alternatingGroup (Fin 10) :=
    CentralizerModels.a10Centralizer.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  let P : Subgroup (alternatingGroup (Fin 10)) := (D.localSylow : Subgroup D.centralizer).map f
  have hPcard : Nat.card P = 128 := by
    rw [Subgroup.card_map_of_injective hf, Sylow.card_eq_multiplicity, D.centralizer_card]
    decide +kernel
  have hAcard : Nat.card (alternatingGroup (Fin 10)) = 1814400 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide +kernel
  have hPsylow : Nat.card P = 2 ^ (Nat.card (alternatingGroup (Fin 10))).factorization 2 := by
    rw [hPcard, hAcard]
    decide +kernel
  let S : Sylow 2 (alternatingGroup (Fin 10)) := Sylow.ofCard P hPsylow
  have hz : CentralizerModels.a10Involution ∈ S := by
    change CentralizerModels.a10Involution ∈ P
    refine ⟨D.centralInvolution, ?_, ?_⟩
    · exact (D.involution : D.sylow).property
    · exact congrArg Subtype.val (D.a10Equiv_centralInvolution e)
  refine ⟨S, hz, mem_center_iff.mpr ?_⟩
  intro x
  apply Subtype.ext
  have hxP : (x : alternatingGroup (Fin 10)) ∈ P := x.property
  obtain ⟨y, _, hy⟩ := hxP
  change (x : alternatingGroup (Fin 10)) * CentralizerModels.a10Involution =
    CentralizerModels.a10Involution * (x : alternatingGroup (Fin 10))
  rw [← hy]
  exact mem_centralizer_singleton_iff.mp (e y).property

end LocalData

end Theory.GroupTheory.HeldM22A10
