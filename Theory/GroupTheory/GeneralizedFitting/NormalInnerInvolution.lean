module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.GroupTheory.PGroup.OmegaCenterIn


/-!
# Normality from the component order and inner involutions in a Sylow center

Distinct conjugate components commute. If a component is centerless, their
product has the square of its order, so a missing square divisor forces
normality. For a normal centerless subgroup, an inner involution induced by
an element centralizing a Sylow subgroup has its unique implementing
involution in that Sylow's central omega subgroup.

These two observations preserve the actual subgroup and conjugation action.
They are used in the model inspection of Aschbacher--Smith 14.3.22,
printed p.999, in OppositeCentralizer.RecognitionComponentAction.
A complementary central line also bounds the central omega subgroup of a
half-order subgroup when the full Sylow central omega has order four.
-/

public section

open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem IsComponent.normal_of_square_not_dvd
    {D : Subgroup G} (hD : IsComponent G D) (hz : center D = ⊥)
    {n : ℕ} (hn : n ∣ Nat.card D) (hsmall : ¬n*n ∣ Nat.card G) : D.Normal := by
  apply normal_iff_map_conj_eq.mpr
  intro g
  by_contra hne
  let E := D.map (MulAut.conj g).toMonoidHom
  have hc : E ≤ centralizer (D : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp ((hD.map_conj g).commutator_eq_bot_of_ne hD hne)
  have hd : Disjoint D E := by
    apply disjoint_iff.mpr
    apply (eq_bot_iff_forall _).mpr
    intro x hx
    obtain ⟨hxD,hxE⟩ := hx
    have hxZ : (⟨x,hxD⟩ : D) ∈ center D :=
      mem_center_iff.mpr fun y => Subtype.ext (hc hxE y y.property)
    have hx1 : (⟨x,hxD⟩ : D) = 1 := mem_bot.mp (hz ▸ hxZ)
    exact congrArg (fun t : D => (t : G)) hx1
  have he : Nat.card E = Nat.card D := (Nat.card_congr ((MulAut.conj g).subgroupMap D).toEquiv).symm
  have hcard := (D ⊔ E).card_subgroup_dvd_card
  rw [card_sup_eq_mul_of_normalizes_of_disjoint D E
    (hc.trans (centralizer_le_normalizer _)) hd, he] at hcard
  exact hsmall ((Nat.mul_dvd_mul hn hn).trans hcard)

omit [Finite G] in
private theorem fix_inner_implementer_of_commute (hz : center G = ⊥) (β : MulAut G) (x : G)
    (hc : Commute β (MulAut.conj x)) : β x = x := by
  apply MulAut.conj_injective_of_center_eq_bot hz
  ext y
  have hh := DFunLike.congr_fun hc.eq (β.symm y)
  simpa only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
    β.apply_symm_apply] using hh

omit [Finite G] in
theorem normal_inner_involution_implementer_mem_omegaCenter
    {D : Subgroup G} [D.Normal] (hz : center D = ⊥) (z : G)
    (α : MulAut D) (ho : orderOf α = 2)
    (hi : α ∈ (MulAut.conj : D →* MulAut D).range)
    (ha : MulAut.conjNormal z = α) (S : Sylow 2 G)
    (hzc : z ∈ centralizer (S : Set G)) :
    ∃ x : D, orderOf x = 2 ∧ α = MulAut.conj x ∧
      (x : G) ∈ omegaCenterIn (S : Subgroup G) := by
  obtain ⟨x,hx,he,_⟩ := MulAut.inner_involution_representative hz α ho
    (by obtain ⟨x,hx⟩ := hi; exact ⟨x,hx.symm⟩)
  have hxc (t : G) (ht : t ∈ S) : Commute t (x : G) := by
    have hcz : Commute t z := (show Commute z t from (hzc t ht).symm).symm
    have hca := hcz.map (MulAut.conjNormal : G →* MulAut D)
    rw [ha,he] at hca
    have h := fix_inner_implementer_of_commute hz (MulAut.conjNormal t) x hca
    have hh := congrArg (fun y : D => (y : G)) h
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hx2 : (x : G)^2 = 1 := congrArg D.subtype (hx ▸ pow_orderOf_eq_one x)
  have hxS := (MulAut.involution_mem_sylow_of_centralizes S (x : G) hx2 (by
    intro t ht
    change (x : G) * t * (x : G)⁻¹ = t
    rw [←(hxc t ht).eq,mul_inv_cancel_right])).1
  exact ⟨x,hx,he,(mem_omegaCenterIn_iff _ _).mpr
    ⟨hxS,fun t ht => (hxc t ht).eq,hx2⟩⟩
variable {H : Type*} [Group H] [Finite H]

/-- A central line and a disjoint subgroup of half the Sylow order leave at most
one central involution in that subgroup when the Sylow omega-center has order four. -/
theorem omegaCenter_card_le_two_of_central_line
    (S : Subgroup H) (W P : Subgroup H)
    (hS : Nat.card S = 128) (hW : Nat.card W = 2) (hP : Nat.card P = 64)
    (hWS : W ≤ S) (hPS : P ≤ S) (hWZ : W ≤ center H)
    (hd : Disjoint P W) (hO : Nat.card (omegaCenterIn S) = 4) :
    Nat.card (omegaCenterIn P) ≤ 2 := by
  have hn : W ≤ normalizer (P : Set H) :=
    (hWZ.trans (center_le_centralizer _)).trans (Subgroup.centralizer_le_normalizer _)
  have hPW : P ⊔ W = S := eq_of_le_of_card_ge (sup_le hPS hWS) (by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint P W hn hd,hS,hP,hW])
  have hOZ : omegaCenterIn P ≤ centralizer (P : Set H) := fun x hx =>
    ((mem_omegaCenterIn_iff _ _).mp hx).2.1
  have hOP : omegaCenterIn P ≤ P := fun x hx => ((mem_omegaCenterIn_iff _ _).mp hx).1
  have hOlo : omegaCenterIn P ⊔ W ≤ omegaCenterIn S := by
    apply sup_le
    · intro x hx
      obtain ⟨hxP,hxc,hx2⟩ := (mem_omegaCenterIn_iff _ _).mp hx
      apply (mem_omegaCenterIn_iff _ _).mpr
      refine ⟨hPS hxP,?_,hx2⟩
      have hsx : S ≤ centralizer ({x} : Set H) := by
        rw [←hPW]
        apply sup_le
        · intro t ht
          exact mem_centralizer_singleton_iff.mpr (hxc t ht)
        · intro t ht
          exact mem_centralizer_singleton_iff.mpr ((mem_center_iff.mp (hWZ ht) x).symm)
      intro t ht
      exact mem_centralizer_singleton_iff.mp (hsx ht)
    · intro w hw
      have hw2 : w^2=1 := by
        have hh := pow_card_eq_one' (x := (⟨w,hw⟩ : W))
        rw [hW] at hh
        exact congrArg W.subtype hh
      exact (mem_omegaCenterIn_iff _ _).mpr
        ⟨hWS hw,(hWZ.trans (center_le_centralizer _)) hw,hw2⟩
  have hc := card_le_of_le hOlo
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ W
    ((hWZ.trans (center_le_centralizer _)).trans (Subgroup.centralizer_le_normalizer _))
    (hd.mono_left hOP),hW,hO] at hc
  omega

end Theory.GroupTheory
