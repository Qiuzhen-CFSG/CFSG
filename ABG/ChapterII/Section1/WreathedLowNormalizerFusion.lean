module
public import ABG.ChapterII.Section1.WreathedFrameTransport
public import ABG.ChapterII.Section1.WreathedCentralProductLocal
public import ABG.ChapterII.Section1.WreathedCentralProductNormalizer
public import ABG.ChapterII.Section1.FocalGenerators
public import Theory.GroupTheory.SubgroupLocalStructureTransport
public import Theory.GroupTheory.NormalizerFusionIndexControl

/-!
# Low-index normalizer fusion in a wreathed group

For either representative U or V in an actual wreathed fusion frame,
outer automizer index two implies that every normalizer fusion step
already occurs inside the specified Sylow subgroup. Consequently its
local normalizer fusion subgroup lies in the Sylow derived subgroup.
For the abelian base U the outer index equals its ordinary automizer
index. These are the low-action cases in Alperin--Brauer--Gorenstein,
Chapter II Section 1 Proposition 2, article pp.12-13, in
`refs/latex/alperin-brauer-gorenstein-pages/page-013.tex` and `page-014.tex`.

The canonical base centralizes itself. Its centralizer is proper because
otherwise the base would lie in the smaller ambient center, so maximality
makes that centralizer exactly the base. Its normalizer is the whole
wreathed group and its index is two. For the quaternion central product,
centricity and normalizer index two are already proved. Transport through
the presentation comparison supplies the same facts for either frame
representative. These identify the internal outer index with the ambient
index; the general normalizer-index control theorem realizes each action
inside the Sylow subgroup. Such conjugacy differences are commutators.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

private theorem U_centralizer : Subgroup.centralizer (P.U : Set S) = P.U := by
  let : Finite S := Nat.finite_of_card_ne_zero (by rw [P.card]; positivity)
  have hle : P.U ≤ Subgroup.centralizer (P.U : Set S) := by
    intro a ha b hb
    exact (P.commute_of_mem_U hb ha).eq
  apply (P.U_isCoatom.le_iff_eq ?_).mp hle
  intro ht
  have hUC : P.U ≤ Subgroup.center S := Subgroup.centralizer_eq_top_iff_subset.mp ht
  have hc : Nat.card P.U ≤ Nat.card (Subgroup.center S) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hUC) (Subgroup.inclusion_injective hUC)
  rw [P.card_U, P.card_center] at hc
  have hp : 2 ^ n < 2 ^ (2*n) := Nat.pow_lt_pow_right (by decide) (by have := P.height; omega)
  omega

private theorem representative_local (X : Subgroup S)
    (hX : X = P.U ∨ ∃ s : S, P.V.map (MulAut.conj s).toMonoidHom = X) :
    Subgroup.centralizer (X : Set S) ≤ X ∧
      X.relIndex (Subgroup.normalizer (X : Set S)) = 2 := by
  rcases hX with rfl | ⟨s,rfl⟩
  · refine ⟨P.U_centralizer.le, ?_⟩
    let : P.U.Normal := Subgroup.normal_of_index_eq_two P.index_U
    rw [Subgroup.normalizer_eq_top, Subgroup.relIndex_top_right, P.index_U]
  · apply Subgroup.local_structure_map P.V (MulAut.conj s) ?_ P.V_normalizer_index
    rw [P.V_centralizer]
    exact le_sup_right
end ABG.Wreathed.Presentation

namespace ABG.Wreathed
variable {G : Type*} [Group G] [Finite G]

private theorem frame_local (S : Sylow 2 G) (n : ℕ) (U V W : Subgroup G)
    (hf : WreathedFusionFrame S n U V) (hW : W = U ∨ W = V) :
    W ≤ S ∧ Subgroup.centralizer (W.subgroupOf (S : Subgroup G) : Set S) ≤
      W.subgroupOf (S : Subgroup G) ∧
      (W.subgroupOf (S : Subgroup G)).relIndex
        (Subgroup.normalizer (W.subgroupOf (S : Subgroup G) : Set S)) = 2 := by
  obtain ⟨P⟩ := nonempty_presentation hf.1
  obtain ⟨hU,s,hs⟩ := hf.presentation_representatives P
  have hVS : V ≤ S := by
    obtain ⟨Q,hQS,_,rfl⟩ := hf.2.2.2.2.2
    exact sup_le hQS (Subgroup.map_subtype_le _)
  rcases hW with rfl | rfl
  · refine ⟨hf.2.1, P.representative_local _ (Or.inl ?_)⟩
    rw [hU]
    exact Subgroup.comap_map_eq_self_of_injective (S : Subgroup G).subtype_injective P.U
  · refine ⟨hVS, P.representative_local _ (Or.inr ⟨s, ?_⟩)⟩
    apply Subgroup.map_injective (S : Subgroup G).subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hVS]
    convert hs using 1
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1

/-- An outer automizer of order two introduces only Sylow conjugacy. -/
public theorem low_normalizer_fusion_control
    (S : Sylow 2 G) (n : ℕ) (U V W : Subgroup G)
    (hf : WreathedFusionFrame S n U V) (hW : W = U ∨ W = V)
    (houter : outerAutomizerIndex W = 2)
    (g : G) (hg : g ∈ Subgroup.normalizer (W : Set G))
    (x y : S) (hx : (x : G) ∈ W) (hxy : g⁻¹ * (x : G) * g = (y : G)) :
    IsConj x y := by
  obtain ⟨hWS,hc,hn⟩ := frame_local S n U V W hf hW
  have hCP : (Subgroup.centralizer (W : Set G)).subgroupOf (S : Subgroup G) ≤
      W.subgroupOf (S : Subgroup G) := by
    intro z hz
    apply hc
    intro t ht
    exact Subtype.ext (hz t ht)
  apply Subgroup.normalizer_fusion_control_of_outer_index_eq (S : Subgroup G) W hWS
    ?_ g hg x y hx hxy
  rw [Subgroup.sup_centralizer_subgroupOf_eq_of_centralizer_le _ _ hWS hCP,
    Subgroup.subgroupOf_normalizer_eq hWS]
  exact hn.trans houter.symm

/-- Low normalizer actions contribute only Sylow commutators to the focal subgroup. -/
public theorem low_normalizerFusionSubgroup_le_commutator
    (S : Sylow 2 G) (n : ℕ) (U V W : Subgroup G)
    (hf : WreathedFusionFrame S n U V) (hW : W = U ∨ W = V)
    (houter : outerAutomizerIndex W = 2) :
    normalizerFusionSubgroup (S : Subgroup G) W ≤ commutator S := by
  rw [normalizerFusionSubgroup, Subgroup.closure_le]
  rintro z ⟨x,y,g,hg,hx,hxy,rfl⟩
  obtain ⟨s,rfl⟩ := isConj_iff.mp
    (low_normalizer_fusion_control S n U V W hf hW houter g hg x y hx hxy)
  have h := Subgroup.commutator_mem_commutator (Subgroup.mem_top x⁻¹) (Subgroup.mem_top s)
  simpa only [SetLike.mem_coe, commutator_def, commutatorElement_def, inv_inv, mul_assoc] using h

end ABG.Wreathed
