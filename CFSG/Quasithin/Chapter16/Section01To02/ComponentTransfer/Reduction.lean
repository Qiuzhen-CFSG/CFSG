module

public import CFSG.Quasithin.Chapter16.Section01To02.ComponentTransfer.Basic

/-!
# Component enlargement before the intrinsic case analysis

This module separates the elementary part of 16.1.7 from the intrinsic
classification of involutory automorphisms. Its balance premise is the
ordinary-component specialization of I.3.1–I.3.2 when O(H) = 1. It specifies
the actual layer closure, distinct conjugate components, and the isomorphism
of the quotients by O₂. It is not asserted as a theorem here.

From that premise we prove the geometric alternatives, including relative
component membership and K = [K,t] in the proper single-component case.
The swapped product is proved subnormal, so both proper branches support the
Sylow restriction needed in 16.1.8. The family list, fixed solvable residual,
and the strict lower bounds in the two proper branches remain separate work.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
I.3.1–I.3.2, pp.414–415, and 16.1.7–16.1.8, pp.1172–1173.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.ComponentTransfer

open Subgroup Theory.GroupTheory

universe u
variable {G : Type u} [Group G]
variable {L J H : Subgroup G} {t i : G}

/-- Conjugation by an element of H preserves relative component membership. -/
theorem IsComponentIn.conjugate (h : IsComponentIn L H) (ht : t ∈ H) :
    IsComponentIn (L.conjBy t) H := by
  have hc := h.2.map_conj (⟨t, ht⟩ : H)
  have hle : L.conjBy t ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem ht (h.1 hx)) (H.inv_mem ht)
  have he : (L.subgroupOf H).map (MulAut.conj (⟨t, ht⟩ : H)).toMonoidHom =
      (L.conjBy t).subgroupOf H := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      exact ⟨⟨y, h.1 hy⟩, hy, Subtype.ext hxy⟩
  exact ⟨hle, he ▸ hc⟩

/-- Distinct relative components commute in the original ambient group. -/
theorem IsComponentIn.commute_of_ne (hL : IsComponentIn L H)
    (hJ : IsComponentIn J H) (hne : L ≠ J) : ⁅L, J⁆ = ⊥ := by
  have hne' : L.subgroupOf H ≠ J.subgroupOf H := by
    intro he
    apply hne
    simpa only [map_subgroupOf_eq_of_le hL.1, map_subgroupOf_eq_of_le hJ.1] using
      congrArg (Subgroup.map H.subtype) he
  have hc := congrArg (Subgroup.map H.subtype) (hL.2.commutator_eq_bot_of_ne hJ.2 hne')
  simpa only [map_commutator, map_subgroupOf_eq_of_le hL.1,
    map_subgroupOf_eq_of_le hJ.1, Subgroup.map_bot] using hc

private theorem layer_normal : (componentLayer G).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [le_normalizer_iff]
  intro g _ x hx
  have hm : (componentLayer G).map (MulAut.conj g).toMonoidHom ≤ componentLayer G := by
    rw [componentLayer, sSup_eq_iSup', Subgroup.map_iSup]
    apply iSup_le
    intro J
    exact le_iSup_of_le ⟨_, J.property.map_conj g⟩ le_rfl
  exact hm (mem_map_of_mem _ hx)

private theorem layer_le_component_normalizer (hL : IsComponent G L) :
    componentLayer G ≤ normalizer L := by
  apply sSup_le
  intro J hJ
  by_cases he : J = L
  · exact he ▸ L.le_normalizer
  · exact (commutator_eq_bot_iff_le_centralizer.mp
      (hJ.commutator_eq_bot_of_ne hL he)).trans (centralizer_le_normalizer _)

private theorem component_join_subnormal (hL : IsComponent G L) (hJ : IsComponent G J) :
    (L ⊔ J).IsSubnormal := by
  have hle : L ⊔ J ≤ componentLayer G := sup_le (le_sSup hL) (le_sSup hJ)
  have hn : ((L ⊔ J).subgroupOf (componentLayer G)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hle).mpr
      ((le_inf (layer_le_component_normalizer hL) (layer_le_component_normalizer hJ)).trans
        (normalizer_inf_normalizer_le_normalizer_sup L J))
  exact .step _ _ hle layer_normal.isSubnormal hn

/-- A join of relative components is subnormal in their local overgroup. -/
theorem IsComponentIn.join_subnormal (hL : IsComponentIn L H) (hJ : IsComponentIn J H) :
    ((L ⊔ J).subgroupOf H).IsSubnormal := by
  rw [subgroupOf_sup hL.1 hJ.1]
  exact component_join_subnormal hL.2 hJ.2

/-- The ordinary swapped alternative of I.3.2. The product is represented by
its subgroup join; `SwappedComponents.commute` proves that its two factors commute.
The solvable-residual assertion of 16.1.7(2) is not part of this premise. -/
def SwappedComponents (H : Subgroup G) (t : G) (L K : Subgroup G) : Prop :=
  ∃ J : Subgroup G, IsComponentIn J H ∧ J ≠ J.conjBy t ∧
    K = J ⊔ J.conjBy t ∧ Nonempty ((J ⧸ pCore 2 J) ≃* (L ⧸ pCore 2 L))

/-- The concrete ordinary-component specialization of I.3.1–I.3.2 at H,t.
The source assembly must supply this from K-group balance and O(H)=1. -/
def OrdinaryBalanceAt (H : Subgroup G) (t : G) : Prop :=
  ∀ L : Subgroup G, IsComponentIn L (centralizerIn H t) →
    (IsComponentIn (layerClosure H L) H ∧ t ∈ normalizer (layerClosure H L)) ∨
      SwappedComponents H t L (layerClosure H L)

/-- The earlier balance result as a mathematical premise, with the K-group
and odd-core hypotheses made explicit. It asserts no transfer conclusion. -/
def OrdinaryBalanceInput (𝒦 : GroupClass.{u}) (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ H : Subgroup G, IsKGroup 𝒦 H → pPrimeCore 2 H = ⊥ →
    ∀ t : G, t ∈ H → orderOf t = 2 → OrdinaryBalanceAt H t

variable {K : Subgroup G}

/-- The two factors in the swapped alternative commute. -/
theorem SwappedComponents.commute (h : SwappedComponents H t L K) (ht : t ∈ H) :
    ∃ J : Subgroup G, IsComponentIn J H ∧ J ≠ J.conjBy t ∧
      K = J ⊔ J.conjBy t ∧ ⁅J, J.conjBy t⁆ = ⊥ ∧
      Nonempty ((J ⧸ pCore 2 J) ≃* (L ⧸ pCore 2 L)) := by
  obtain ⟨J, hJ, hne, he, e⟩ := h
  exact ⟨J, hJ, hne, he, hJ.commute_of_ne (hJ.conjugate ht) hne, e⟩

/-- The swapped enlargement lies in H and is subnormal there. -/
theorem SwappedComponents.subnormal (h : SwappedComponents H t L K) (ht : t ∈ H) :
    K ≤ H ∧ (K.subgroupOf H).IsSubnormal := by
  obtain ⟨J, hJ, _, rfl, _⟩ := h
  have hc := hJ.conjugate ht
  exact ⟨sup_le hJ.1 hc.1, hJ.join_subnormal hc⟩

/-- The group-theoretic alternatives before the family and automorphism sieve.
This is a conditional reduction, not the full numbered source theorem 16.1.7. -/
theorem enlargement_structure_of_balance (h : Setup t i L)
    (balance : OrdinaryBalanceAt (involutionCentralizer i) t) :
    let K := layerClosure (involutionCentralizer i) L
    (K = L ∧ IsCentralizerComponent i L) ∨
      SwappedComponents (involutionCentralizer i) t L K ∨
      (IsComponentIn K (involutionCentralizer i) ∧ ⁅K, zpowers t⁆ = K ∧
        IsComponentIn L (centralizerIn K t) ∧ L < K) := by
  let K := layerClosure (involutionCentralizer i) L
  have hLK : L ≤ K := le_layerClosure _ _
  rcases balance L h.component_in_jointCentralizer with ⟨hK, htK⟩ | hswap
  · by_cases he : K = L
    · exact Or.inl ⟨he, he ▸ hK⟩
    · have hproper : L < K := lt_of_le_of_ne hLK (Ne.symm he)
      let := hK.quasisimple
      exact Or.inr (Or.inr ⟨hK,
        commutator_eq_self_of_proper h.component K hproper htK,
        IsComponentIn.restrict h.component (le_inf hLK h.component.1) inf_le_right,
        hproper⟩)
  · exact Or.inr (Or.inl hswap)

/-- Supply the local balance premise from the global QTK/even-type hypotheses
and the explicitly stated earlier balance theorem. -/
theorem ordinaryBalanceAt_of_hypothesis [Finite G] {𝒦 : GroupClass.{u}}
    (hG : Hypothesis1611 𝒦 G) (balance : OrdinaryBalanceInput 𝒦 G)
    (h : Setup t i L) : OrdinaryBalanceAt (involutionCentralizer i) t :=
  balance _ (hG.involution_centralizer_sqtk h.involution_i).isKGroup
    (hG.evenType.oddCore i h.involution_i) t h.t_mem h.involution_t

/-- The actual enlargement is subnormal in C_G(i) in every balance branch. -/
theorem closure_subnormal_of_balance (h : Setup t i L)
    (balance : OrdinaryBalanceAt (involutionCentralizer i) t) :
    ((layerClosure (involutionCentralizer i) L).subgroupOf
      (involutionCentralizer i)).IsSubnormal := by
  rcases balance L h.component_in_jointCentralizer with ⟨hK, _⟩ | hswap
  · exact hK.2.1
  · exact (hswap.subnormal h.t_mem).2

/-- The two indices in 16.1.8 refer to the actual closure, and Sylow restriction
is derived from balance rather than included as a premise. -/
theorem closure_sylow_index_le [Finite G] (h : Setup t i L)
    (balance : OrdinaryBalanceAt (involutionCentralizer i) t)
    (S : Sylow 2 (involutionCentralizer i)) :
    let K := layerClosure (involutionCentralizer i) L
    ∃ R : Sylow 2 K,
      (R : Subgroup K).map K.subtype =
        ((S : Subgroup (involutionCentralizer i)).map (involutionCentralizer i).subtype) ⊓ K ∧
      (involutionCentralizer t).relIndex ((R : Subgroup K).map K.subtype) ≤
        (involutionCentralizer t).relIndex
          ((S : Subgroup (involutionCentralizer i)).map (involutionCentralizer i).subtype) :=
  exists_restricted_sylow_with_index_le h.closure_le_centralizer
    (closure_subnormal_of_balance h balance) S t

end CFSG.Quasithin.Chapter16.ComponentTransfer
