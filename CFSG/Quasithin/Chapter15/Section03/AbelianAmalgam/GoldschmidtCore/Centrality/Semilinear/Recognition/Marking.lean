module

public import Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking
public import Mathlib.GroupTheory.Index

/-!
# Simultaneous local markings and the external index-seven subgroup

One quotient isomorphism carries the common Sylow subgroup to the upper
triangular subgroup, the first local group to the line parabolic, and the
second to the point parabolic. The first choice orients the marking; generation
forces the second local group to be the other parabolic.

Pulling back this actual line parabolic through a compatible external quotient
gives a maximal subgroup of index seven. The external quotient isomorphism and
its compatibility with the specified intersection remain explicit inputs.

Source: the local configuration on Aschbacher–Smith, combined manuscript of
1 March 2004, printed pp.1154–1155, used in the repair of 15.3.68(2).
-/

public section

open Matrix.PSL3Two Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

/-- One marking orients both specified local groups, rather than choosing
independent isomorphisms for them. -/
theorem mark_both_parabolics {H : Type*} [Group H] [Finite H]
    (e₀ : H ≃* PSL) (S : Sylow 2 H) (G₁ G₂ : Subgroup H)
    (hS₁ : (S : Subgroup H) ≤ G₁) (hS₂ : (S : Subgroup H) ≤ G₂)
    (h₁ : G₁ ≠ ⊤) (h₂ : G₂ ≠ ⊤)
    (hn₁ : ¬ IsPGroup 2 G₁) (hn₂ : ¬ IsPGroup 2 G₂)
    (hgen : G₁ ⊔ G₂ = ⊤) :
    ∃ e : H ≃* SL, (S : Subgroup H).map e.toMonoidHom = borelSL ∧
      G₁.map e.toMonoidHom = lineParabolicSL ∧
      G₂.map e.toMonoidHom = pointParabolicSL := by
  obtain ⟨e,hS,hG₁⟩ := exists_sylow_line_marking e₀ S G₁ hS₁ h₁ hn₁
  refine ⟨e,hS,hG₁,?_⟩
  have hB : borelSL ≤ G₂.map e.toMonoidHom := hS ▸ map_mono hS₂
  have ht : G₂.map e.toMonoidHom ≠ ⊤ := by
    intro h
    exact h₂ (e.mapSubgroup.injective (h.trans e.mapSubgroup.map_top.symm))
  have hn : ¬ IsPGroup 2 (G₂.map e.toMonoidHom) := fun h =>
    hn₂ (h.of_equiv (e.subgroupMap G₂).symm)
  rcases parabolic_of_borel_le_of_not_two _ hB ht hn with hp | hl
  · exact hp
  · have he : G₂ = G₁ := e.mapSubgroup.injective (hl.trans hG₁.symm)
    rw [he,sup_idem] at hgen
    exact (h₁ hgen).elim

private theorem line_index : lineParabolicSL.index = 7 := by
  have h := lineParabolicSL.index_mul_card
  rw [card_lineParabolicSL, card_SL] at h
  omega

private theorem maximal_of_index_seven {K : Type*} [Group K]
    (P : Subgroup K) (hi : P.index = 7) : IsCoatom P := by
  refine ⟨fun ht => by simp [ht] at hi, fun B hPB => ?_⟩
  have hm := relIndex_mul_index hPB.le
  rw [hi] at hm
  have hp : (P.relIndex B * B.index).Prime := hm ▸ (by decide : Nat.Prime 7)
  rcases Nat.prime_mul_iff.mp hp with ⟨_,hB⟩ | ⟨_,hrel⟩
  · exact index_eq_one.mp hB
  · exact (hPB.not_ge (relIndex_eq_one.mp hrel)).elim

/-- Pull the actual marked line parabolic back through a compatible external
quotient. In the application `P = G₁ ∩ K`; the displayed comap equality retains
precisely that quotient-map compatibility. -/
theorem external_intersection_maximal_index_seven
    {K H : Type*} [Group K] [Group H]
    (N : Subgroup K) [N.Normal] (Q : Subgroup H) [Q.Normal]
    (e : (K ⧸ N) ≃* (H ⧸ Q)) (m : (H ⧸ Q) ≃* SL)
    (G₁ : Subgroup H)
    (hmark : (G₁.map (QuotientGroup.mk' Q)).map m.toMonoidHom = lineParabolicSL)
    (P : Subgroup K)
    (hcompat : P = (G₁.map (QuotientGroup.mk' Q)).comap
      (e.toMonoidHom.comp (QuotientGroup.mk' N))) :
    IsCoatom P ∧ P.index = 7 := by
  have hi : P.index = 7 := by
    rw [hcompat, index_comap_of_surjective _
      (e.surjective.comp (QuotientGroup.mk'_surjective N))]
    rw [← index_map_equiv _ m]
    change ((G₁.map (QuotientGroup.mk' Q)).map m.toMonoidHom).index = 7
    rw [hmark, line_index]
  exact ⟨maximal_of_index_seven P hi,hi⟩

/-- The index-seven conclusion for the literal ambient intersection
`P = G₁ ∩ K`. Membership compatibility is supplied by the external quotient
branch, using the same quotient marking as the natural-module argument. -/
theorem actual_intersection_maximal_index_seven
    {A : Type*} [Group A] (H K G₁ : Subgroup A)
    (N : Subgroup K) [N.Normal] (Q : Subgroup H) [Q.Normal]
    (e : (K ⧸ N) ≃* (H ⧸ Q)) (m : (H ⧸ Q) ≃* SL)
    (hmark : ((G₁.subgroupOf H).map (QuotientGroup.mk' Q)).map
      m.toMonoidHom = lineParabolicSL)
    (hcompat : ∀ k : K,
      e (QuotientGroup.mk' N k) ∈ (G₁.subgroupOf H).map (QuotientGroup.mk' Q) ↔
        (k : A) ∈ G₁) :
    IsCoatom ((G₁ ⊓ K).subgroupOf K) ∧ (G₁ ⊓ K).relIndex K = 7 := by
  apply external_intersection_maximal_index_seven N Q e m
    (G₁.subgroupOf H) hmark ((G₁ ⊓ K).subgroupOf K)
  ext k
  change ((k : A) ∈ G₁ ∧ (k : A) ∈ K) ↔ _
  rw [and_iff_left k.property]
  exact (hcompat k).symm

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
