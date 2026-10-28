module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.Local
public import Theory.GroupTheory.QuaternionCentralProductTransport
public import Theory.GroupTheory.QuaternionCentralProductNineOrbit

/-!
# Involution fusion in the U₄(3) local core

The actual residual has a Sylow-three subgroup of order nine. Its action on
 the two marked quaternion factors gives the source order-nine orbit theorem,
 so all noncentral involutions of Q are conjugate in the actual residual. The
 fused source involution therefore represents this same noncentral class.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 45.2 and the argument
 preceding Lemma 45.3, printed pp.242–243.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z : G}
namespace CentralizerHypothesis
variable (h : CentralizerHypothesis z)

include h in
theorem core_involution_orbit (x y : G) (hx : x ∈ core z) (hy : y ∈ core z)
    (hx2 : orderOf x = 2) (hy2 : orderOf y = 2)
    (hxZ : x ∉ zpowers z) (hyZ : y ∉ zpowers z) :
    ∃ k ∈ residual z, k * x * k⁻¹ = y := by
  let R := residual z
  let Q := (core z).subgroupOf R
  have hQR : core z ≤ R := pCoreIn_le 2 R
  let e : Q ≃* core z := subgroupOfEquivOfLe hQR
  let d := h.coreData.map e.symm
  have hn : R ≤ normalizer (core z : Set G) :=
    (map_subtype_le _).trans centralizer_normalizes_core
  let : Q.Normal := (normal_subgroupOf_iff_le_normalizer hQR).mpr hn
  have hs : Subgroup.centralizer (Q : Set R) ≤ Q := by
    intro a ha
    have hG : (a : G) ∈ Subgroup.centralizer (core z : Set G) := by
      intro b hb
      exact congrArg Subtype.val (ha ⟨b,hQR hb⟩ hb)
    exact h.line_le_core (h.centralizer_core ▸ hG)
  let S : Sylow 3 R := Classical.choice inferInstance
  have hS : Nat.card (S : Subgroup R) = 9 := by
    rw [S.card_eq_multiplicity, h.residual_card]
    decide +kernel
  let xx : Q := ⟨⟨x,hQR hx⟩,hx⟩
  let yy : Q := ⟨⟨y,hQR hy⟩,hy⟩
  have hx' : xx ∉ center Q := by
    intro hh
    apply hxZ
    rw [← h.core_center]
    exact mem_map_of_mem (core z).subtype ((centerCongr e ⟨xx,hh⟩).property)
  have hy' : yy ∉ center Q := by
    intro hh
    apply hyZ
    rw [← h.core_center]
    exact mem_map_of_mem (core z).subtype ((centerCongr e ⟨yy,hh⟩).property)
  have hc := isConj_noncentral_involutions_of_order_nine Q hs d.left d.right
    d.left_model d.right_model d.span d.intersection_card d.commute S hS xx yy
    (by rw [← orderOf_injective Q.subtype Q.subtype_injective,
      ← orderOf_injective R.subtype R.subtype_injective]; exact hx2) hx'
    (by rw [← orderOf_injective Q.subtype Q.subtype_injective,
      ← orderOf_injective R.subtype R.subtype_injective]; exact hy2) hy'
  obtain ⟨k,hk⟩ := isConj_iff.mp hc
  exact ⟨k,k.property,congrArg Subtype.val hk⟩

include h in
theorem core_involution_fused (x : G) (hx : x ∈ core z)
    (hx2 : orderOf x = 2) (hxZ : x ∉ zpowers z) : IsConj z x := by
  obtain ⟨g,hg,hgz⟩ := h.fused
  have hu2 : orderOf (g⁻¹ * z * g) = 2 := by
    simpa only [MulAut.conj_apply,inv_inv] using
      ((MulAut.conj g⁻¹).orderOf_eq z).trans h.involution
  obtain ⟨k,_,hk⟩ := h.core_involution_orbit _ x hg hx hu2 hx2 hgz hxZ
  apply isConj_iff.mpr
  refine ⟨k*g⁻¹, ?_⟩
  calc
    (k*g⁻¹)*z*(k*g⁻¹)⁻¹ = k*(g⁻¹*z*g)*k⁻¹ := by group
    _ = x := hk

end CentralizerHypothesis
end Theory.GroupTheory.Recognition.UnitaryFourThree
