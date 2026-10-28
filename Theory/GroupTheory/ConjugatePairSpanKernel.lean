module
public import Theory.GroupTheory.TwoLayerCentralizer
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupTheory.CharacteristicCentralizerFusion
/-!
# The two-core kernel of an actual two-conjugate module span

Fixing a two-group layer and its quotient forces the two-residual to
centralize the original self-centralizing core. Its image is a two-group,
so the full fixer is a two-group. Applied to D=⟨K,Kᵍ⟩ and
W=[O₂(G),K]+[O₂(G),K]ᵍ, this gives C_D(W)≤O₂(D). Normalization and the
commutator containment are derived from the original core identity.
Source: Aschbacher–Smith C.5.12, printed p.163.
-/
public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
theorem centralizer_le_twoCore_of_two_layer (Q W D : Subgroup G)
    (hQ : IsPGroup 2 Q) (hW : IsPGroup 2 W)
    (hcent : centralizer (Q : Set G) ≤ Q)
    (hDW : D ≤ normalizer (W : Set G)) (hcomm : ⁅D,Q⁆ ≤ W) :
    (centralizer (W : Set G)).subgroupOf D ≤ pCore 2 D := by
  let C := D ⊓ centralizer (W : Set G)
  have hr : (pResidual 2 C).map C.subtype ≤ Q :=
    (residual_centralizes_of_two_layer C Q W hW inf_le_right
      ((commutator_mono inf_le_left le_rfl).trans hcomm)).trans hcent
  have hp : IsPGroup 2 C := by
    intro c
    obtain ⟨n,hn⟩ := isPGroup_quotient_pResidual (G := C) 2
      (QuotientGroup.mk' (pResidual 2 C) c)
    have hm : c ^ 2 ^ n ∈ pResidual 2 C := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (pResidual 2 C) (c ^ 2 ^ n) = 1
      simpa only [map_pow] using hn
    have hq : ((c ^ 2 ^ n : C) : G) ∈ Q := hr (mem_map_of_mem _ hm)
    obtain ⟨m,hm⟩ := hQ ⟨_,hq⟩
    refine ⟨n+m,?_⟩
    apply C.subtype_injective
    change (c : G) ^ 2 ^ (n+m) = 1
    rw [pow_add,pow_mul]
    exact congrArg Q.subtype hm
  have hc : (centralizer (W : Set G)).subgroupOf D = C.subgroupOf D := by
    ext x
    exact (and_iff_right x.property).symm
  rw [hc]
  apply le_sSup
  constructor
  · apply (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
    apply (le_inf D.le_normalizer ?_).trans inf_normalizer_le_normalizer_inf
    exact hDW.trans (normalizer_le_normalizer_centralizer W)
  · exact hp.comap_subtype

theorem conjugate_pair_span_kernel (K U : Subgroup G) (g : G)
    (hcent : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hUK : ⁅pCore 2 G,K⁆ = U) :
    let W := U ⊔ U.conjBy g
    let D := K ⊔ K.conjBy g
    D ≤ normalizer (W : Set G) ∧ ⁅D,pCore 2 G⁆ ≤ W ∧
      (centralizer (W : Set G)).subgroupOf D ≤ pCore 2 D := by
  let W := U ⊔ U.conjBy g
  let D := K ⊔ K.conjBy g
  have hUg : ⁅pCore 2 G,K.conjBy g⁆ = U.conjBy g := by
    have he := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hUK
    rw [map_commutator,pCore_map_iso] at he
    exact he
  have hWQ : W ≤ pCore 2 G := by
    apply sup_le
    · rw [← hUK]; exact commutator_le_left _ _
    · rw [← hUg]; exact commutator_le_left _ _
  have hDW : D ≤ normalizer (W : Set G) := by
    apply sup_le
    · apply le_normalizer_iff_commutator_le_left.mpr
      calc
        ⁅W,K⁆ ≤ ⁅pCore 2 G,K⁆ := commutator_mono hWQ le_rfl
        _ = U := hUK
        _ ≤ W := le_sup_left
    · apply le_normalizer_iff_commutator_le_left.mpr
      calc
        ⁅W,K.conjBy g⁆ ≤ ⁅pCore 2 G,K.conjBy g⁆ := commutator_mono hWQ le_rfl
        _ = U.conjBy g := hUg
        _ ≤ W := le_sup_right
  have hKQ : ⁅K,pCore 2 G⁆ ≤ W := by rw [commutator_comm,hUK]; exact le_sup_left
  have hKgQ : ⁅K.conjBy g,pCore 2 G⁆ ≤ W := by rw [commutator_comm,hUg]; exact le_sup_right
  have hpre : D ≤ commutatorPreimage D (pCore 2 G) W :=
    sup_le (le_commutatorPreimage le_sup_left hKQ) (le_commutatorPreimage le_sup_right hKgQ)
  have hDQ : ⁅D,pCore 2 G⁆ ≤ W := by
    calc
      ⁅D,pCore 2 G⁆ ≤ ⁅commutatorPreimage D (pCore 2 G) W,pCore 2 G⁆ :=
        commutator_mono hpre le_rfl
      _ ≤ W := commutator_commutatorPreimage_le D (pCore 2 G) W hDW
  have hQtwo : IsPGroup 2 (pCore 2 G) := pCore_isPGroup
  have hWtwo : IsPGroup 2 W := hQtwo.to_le hWQ
  exact ⟨hDW,hDQ,centralizer_le_twoCore_of_two_layer (pCore 2 G) W D
    hQtwo hWtwo hcent hDW hDQ⟩
end Subgroup
