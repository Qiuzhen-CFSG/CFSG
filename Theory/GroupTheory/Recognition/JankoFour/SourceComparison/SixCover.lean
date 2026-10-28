module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.CubicCentralizer
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.CoverComparison

/-!
# Comparing the original six-covers with their markings

The centralizer C_H(A) is a perfect central cover of the actual M₂₂ of
kernel order six. Compare its universal lift with that of a second marked
type-J₄ group. Cyclicity of the genuine multiplier identifies the lift
kernels, yielding an isomorphism over the original M₂₂ quotient.

The cubic scalar subgroup and marked central involution are recovered as
the unique subgroups of orders three and two in the cyclic center. Thus
the isomorphism retains both attachments needed for extraspecial gluing.

This proves the six-cover comparison step of AS91 (8.3), p.606. Extending
it to H and aligning its point and edge subgroups remain separate steps.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
variable (X : Sylow 3 (CubicLift.subgroup e))

/-- The original marked involution, as an element of the six-cover. -/
noncomputable def cubicMarker : cubicCentralizerInH e X := by
  refine ⟨⟨z,mem_centralizer_singleton_iff.mpr rfl⟩,?_⟩
  apply center_le_centralizer
  exact mem_center_iff.mpr fun y => Subtype.ext (mem_centralizer_singleton_iff.mp y.property)

theorem cubicMarker_mem_center : cubicMarker e X ∈ center (cubicCentralizerInH e X) := by
  apply mem_center_iff.mpr
  intro c
  exact Subtype.ext (Subtype.ext (mem_centralizer_singleton_iff.mp c.val.property))

include h in
theorem cubicMarker_order : orderOf (cubicMarker e X) = 2 := by
  rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
  exact h.involution

variable (hp : Group.IsPerfect (cubicCentralizerInH e X))

theorem cubicCentralizerCover_kernel_card :
    Nat.card (cubicCentralizerCover h e X hp).toMonoidHom.ker = 6 := by
  change Nat.card (cubicCentralizerProjection h e X).ker = 6
  rw [cubicCentralizerProjection_ker h e X,
    Nat.card_congr (subgroupOfEquivOfLe (cubicCenterInH_le h e X)).toEquiv]
  exact cubicCenterInH_card h e X

include h hp in
theorem cubicCentralizer_center_isCyclic : IsCyclic (center (cubicCentralizerInH e X)) := by
  have hk : (cubicCentralizerCover h e X hp).toMonoidHom.ker =
      center (cubicCentralizerInH e X) :=
    (cubicCentralizerProjection_ker h e X).trans (cubicCentralizer_center h e X hp).symm
  rw [← hk]
  exact m22_cover_kernel_isCyclic (cubicCentralizerCover h e X hp)

include h hp in
theorem cubicScalar_le_center :
    (cubicSylowImage e X).subgroupOf (cubicCentralizerInH e X) ≤
      center (cubicCentralizerInH e X) := by
  rw [cubicCentralizer_center h e X hp]
  intro x hx
  exact (le_sup_left : cubicSylowImage e X ≤ cubicCenterInH e X) hx

variable {G' : Type*} [Group G'] [Finite G'] {z' : G'}
variable (h' : IsTypeJ4 z')
variable (e' : CubicAutomorphismQuotient (centralizer z' ⧸ core z'))
variable (X' : Sylow 3 (CubicLift.subgroup e'))
variable (hp' : Group.IsPerfect (cubicCentralizerInH e' X'))

include h hp h' hp' in
/-- Every isomorphism of these actual six-covers preserves the cubic scalar
subgroup; the scalar has not been omitted from the cover. -/
theorem cubicCentralizerEquiv_scalar
    (φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X') :
    ((cubicSylowImage e X).subgroupOf (cubicCentralizerInH e X)).map φ.toMonoidHom =
      (cubicSylowImage e' X').subgroupOf (cubicCentralizerInH e' X') := by
  let : IsCyclic (center (cubicCentralizerInH e' X')) :=
    cubicCentralizer_center_isCyclic h' e' X' hp'
  apply subgroups_eq_of_card_eq_in_cyclic _ _ (center (cubicCentralizerInH e' X'))
  · rintro _ ⟨x,hx,rfl⟩
    exact (Subgroup.centerCongr φ ⟨x,cubicScalar_le_center h e X hp hx⟩).property
  · exact cubicScalar_le_center h' e' X' hp'
  · rw [card_map_of_injective φ.injective,
      Nat.card_congr (subgroupOfEquivOfLe (cubicSylowImage_le_centralizer h e X)).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (cubicSylowImage_le_centralizer h' e' X')).toEquiv,
      cubicSylowImage_card h e X,cubicSylowImage_card h' e' X']

include h h' hp' in
/-- The marked involution is preserved as an element, not only modulo a kernel. -/
theorem cubicCentralizerEquiv_marker
    (φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X') :
    φ (cubicMarker e X) = cubicMarker e' X' := by
  classical
  let : IsCyclic (center (cubicCentralizerInH e' X')) :=
    cubicCentralizer_center_isCyclic h' e' X' hp'
  have heq : zpowers (φ (cubicMarker e X)) = zpowers (cubicMarker e' X') := by
    apply subgroups_eq_of_card_eq_in_cyclic _ _ (center (cubicCentralizerInH e' X'))
    · exact zpowers_le.mpr (Subgroup.centerCongr φ ⟨_,cubicMarker_mem_center e X⟩).property
    · exact zpowers_le.mpr (cubicMarker_mem_center e' X')
    · rw [Nat.card_zpowers, Nat.card_zpowers, φ.orderOf_eq,
        cubicMarker_order h e X, cubicMarker_order h' e' X']
  have hm : φ (cubicMarker e X) ∈ zpowers (cubicMarker e' X') :=
    heq ▸ mem_zpowers _
  have hfin : IsOfFinOrder (cubicMarker e' X') :=
    orderOf_pos_iff.mp (by rw [cubicMarker_order h' e' X']; decide)
  rw [hfin.mem_zpowers_iff_mem_range_orderOf,cubicMarker_order h' e' X'] at hm
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hm
  have hi2 := Finset.mem_range.mp hi
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · have hne : φ (cubicMarker e X) ≠ 1 := by
      intro h1
      have ho := cubicMarker_order h e X
      rw [φ.injective (h1.trans φ.map_one.symm),orderOf_one] at ho
      contradiction
    exact (hne (by simpa only [pow_zero] using he.symm)).elim
  · simpa only [pow_one] using he.symm

include hp hp' in
/-- Construct the comparison of the actual perfect six-covers, commuting with
both original projections and preserving the scalar and marked involution. -/
theorem exists_cubicCentralizer_equiv :
    ∃ φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X',
      (∀ x, cubicCentralizerProjection h' e' X' (φ x) = cubicCentralizerProjection h e X x) ∧
      ((cubicSylowImage e X).subgroupOf (cubicCentralizerInH e X)).map φ.toMonoidHom =
        (cubicSylowImage e' X').subgroupOf (cubicCentralizerInH e' X') ∧
      φ (cubicMarker e X) = cubicMarker e' X' := by
  obtain ⟨φ,hφ⟩ := exists_m22_cover_equiv_over (cubicCentralizerCover h e X hp)
    (cubicCentralizerCover h' e' X' hp')
    ((cubicCentralizerCover_kernel_card h e X hp).trans
      (cubicCentralizerCover_kernel_card h' e' X' hp').symm)
  exact ⟨φ,hφ,cubicCentralizerEquiv_scalar h e X hp h' e' X' hp' φ,
    cubicCentralizerEquiv_marker h e X h' e' X' hp' φ⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
