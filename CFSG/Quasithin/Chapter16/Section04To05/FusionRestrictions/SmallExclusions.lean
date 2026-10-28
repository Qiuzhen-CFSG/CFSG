module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.Residual
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.TwoCentral
public import Theory.SpecificGroups.Frobenius21.Model
public import Theory.Quasithin.LocalRank
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# The small exclusions in §16.5

This file records the two finite endgames in Lemmas 16.5.3--4.  The
source-specific local calculations are represented by named predicates in
`A6Input` and `L3FourInput`; those predicates contain the actual model
isomorphisms and local hypotheses used by the printed proof, rather than an
assertion of either exclusion.  The assembly owner discharges them from the
Chapter 16 setup.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), printed
pp.1195--1197; the order-21 alternative is the action in GLS96 Proposition
14.2.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.SmallExclusions

abbrev DihedralEight := DihedralGroup 4
abbrev QuaternionEight := QuaternionGroup 2

variable {G : Type*} [Group G]

/-- The ambient action quotient (N_G(L)/C_{N_G(L)}(L)). -/
abbrev componentActionKernel (L : Subgroup G) :=
  (centralizer (L : Set G)).subgroupOf (normalizer (L : Set G))

abbrev componentActionQuotient (L : Subgroup G) :=
  normalizer (L : Set G) ⧸ componentActionKernel L

/-- The faithful image of the component action in the ambient quotient. -/
def componentAction (L : Subgroup G) :
    L →* componentActionQuotient L :=
  (QuotientGroup.mk' (componentActionKernel L)).comp (inclusion L.le_normalizer)

def faithfulImage (L : Subgroup G) : Subgroup (componentActionQuotient L) :=
  (componentAction L).range

/-- The kernel of the action on the component is its center. -/
theorem componentAction_ker (L : Subgroup G) :
    (componentAction L).ker = center L := by
  ext x
  change ((⟨x.val, L.le_normalizer x.property⟩ : normalizer (L : Set G)) :
    componentActionQuotient L) = 1 ↔ x ∈ center L
  rw [QuotientGroup.eq_one_iff]
  change x.val ∈ centralizer (L : Set G) ↔ x ∈ center L
  rw [mem_centralizer_iff, mem_center_iff]
  constructor
  · intro h y
    exact Subtype.ext (h y.val y.property)
  · intro h y hy
    exact congrArg Subtype.val (h ⟨y, hy⟩)

/-- The faithful image is the actual central quotient (L/Z(L)). -/
noncomputable def quotientCenterEquivFaithfulImage (L : Subgroup G) :
    (L ⧸ center L) ≃* faithfulImage L :=
  (QuotientGroup.quotientMulEquivOfEq (componentAction_ker L).symm).trans
    (QuotientGroup.quotientKerEquivRange (componentAction L))


private noncomputable def squareFiberCard {A : Type*} [Group A] (x : A) : ℕ :=
  Nat.card {a : A // a ^ 2 = x}

private theorem squareFiberCard_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (x : A) : squareFiberCard x = squareFiberCard (e x) := by
  exact Nat.card_congr (e.toEquiv.subtypeEquiv (p := fun a => a ^ 2 = x)
    (q := fun b => b ^ 2 = e x) (by
      intro a
      change a ^ 2 = x ↔ (e a) ^ 2 = e x
      rw [← map_pow, e.injective.eq_iff]))

private abbrev D8 := DihedralEight
private abbrev Q8 := QuaternionEight
private def d8rot : D8 := DihedralGroup.r 2
private def q8central : Q8 := QuaternionGroup.a 2

private theorem dd_center₁ : (d8rot, (1 : D8)) ∈ center (D8 × D8) := by decide +kernel
private theorem dd_center₂ : (d8rot, d8rot) ∈ center (D8 × D8) := by decide +kernel
private theorem qd_center₁ : (q8central, (1 : D8)) ∈ center (Q8 × D8) := by decide +kernel
private theorem qd_center₂ : (q8central, d8rot) ∈ center (Q8 × D8) := by decide +kernel
private theorem dd_count₁ : squareFiberCard (d8rot, (1 : D8)) = 12 := by
  rw [squareFiberCard, Nat.card_eq_fintype_card]
  decide +kernel
private theorem dd_count₂ : squareFiberCard (d8rot, d8rot) = 4 := by
  rw [squareFiberCard, Nat.card_eq_fintype_card]
  decide +kernel
private theorem qd_count₁ : squareFiberCard (q8central, (1 : D8)) = 36 := by
  rw [squareFiberCard, Nat.card_eq_fintype_card]
  decide +kernel
private theorem qd_count₂ : squareFiberCard (q8central, d8rot) = 12 := by
  rw [squareFiberCard, Nat.card_eq_fintype_card]
  decide +kernel

/-- The two terminal products in the A6 branch cannot fuse all nonidentity
central involutions. -/
theorem not_fused_product_center
    {P : Type*} [Group P]
    (hmodel : Nonempty (P ≃* (DihedralEight × DihedralEight)) ∨
      Nonempty (P ≃* (QuaternionEight × DihedralEight)))
    (hfusion : ∀ x : P, x ≠ 1 → ∀ y : P, y ≠ 1 → ∃ a : MulAut P, a x = y) : False := by
  rcases hmodel with he | he
  · obtain ⟨e⟩ := he
    obtain ⟨a, ha⟩ := hfusion (e.symm (d8rot, (1 : D8))) (by
        intro h
        have hh := congrArg e h
        have hh' : (d8rot, (1 : D8)) = 1 := by
          simpa only [e.apply_symm_apply, e.map_one] using hh
        exact (by decide : (d8rot, (1 : D8)) ≠ 1) hh')
      (e.symm (d8rot, d8rot)) (by
        intro h
        have hh := congrArg e h
        have hh' : (d8rot, d8rot) = 1 := by
          simpa only [e.apply_symm_apply, e.map_one] using hh
        exact (by decide : (d8rot, d8rot) ≠ 1) hh')
    let b := (e.symm.trans a).trans e
    have hb : b (d8rot, (1 : D8)) = (d8rot, d8rot) := by
      simpa [b] using congrArg e ha
    have hc := squareFiberCard_equiv b (d8rot, (1 : D8))
    rw [hb, dd_count₁, dd_count₂] at hc
    contradiction
  · obtain ⟨e⟩ := he
    obtain ⟨a, ha⟩ := hfusion (e.symm (q8central, (1 : D8))) (by
        intro h
        have hh := congrArg e h
        have hh' : (q8central, (1 : D8)) = 1 := by
          simpa only [e.apply_symm_apply, e.map_one] using hh
        exact (by decide : (q8central, (1 : D8)) ≠ 1) hh')
      (e.symm (q8central, d8rot)) (by
        intro h
        have hh := congrArg e h
        have hh' : (q8central, d8rot) = 1 := by
          simpa only [e.apply_symm_apply, e.map_one] using hh
        exact (by decide : (q8central, d8rot) ≠ 1) hh')
    let b := (e.symm.trans a).trans e
    have hb : b (q8central, (1 : D8)) = (q8central, d8rot) := by
      simpa [b] using congrArg e ha
    have hc := squareFiberCard_equiv b (q8central, (1 : D8))
    rw [hb, qd_count₁, qd_count₂] at hc
    contradiction

/-- An invariant subgroup in a finite group action gives factorial divisibility.
This is the counting step in the central (L_3(4)) branch. -/
theorem invariant_card_dvd {V : Type*} [Group V] [Finite V]
    (A : Subgroup (MulAut V)) (W : Subgroup V)
    (hW : ∀ a : A, ∀ v : V, (a : MulAut V) v ∈ W ↔ v ∈ W) :
    Nat.card A ∣ (Nat.card W).factorial * (Nat.card V - Nat.card W).factorial := by
  classical
  let f : A →* (Equiv.Perm W × Equiv.Perm {v : V // v ∉ W}) := {
    toFun a := (Equiv.Perm.subtypePerm (a : MulAut V).toEquiv (hW a),
      Equiv.Perm.subtypePerm (a : MulAut V).toEquiv (fun v => not_congr (hW a v)))
    map_one' := by ext <;> rfl
    map_mul' a b := by ext <;> rfl }
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    by_cases hv : v ∈ W
    · exact congrArg (fun e => ((e.1 : Equiv.Perm W) ⟨v, hv⟩ : V)) hab
    · exact congrArg (fun e => ((e.2 : Equiv.Perm {v : V // v ∉ W}) ⟨v, hv⟩ : V)) hab
  have hd := Subgroup.card_dvd_of_injective f hf
  rw [Nat.card_prod, Nat.card_perm, Nat.card_perm] at hd
  have hc : Nat.card {v : V // v ∉ W} = Nat.card V - Nat.card W := by
    let := Fintype.ofFinite V
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  rwa [hc] at hd

/-- The final GLS96 alternative is incompatible with a nonzero proper
invariant Frattini subgroup of an eight-element binary space. -/
theorem frobenius21_frattini_obstruction {V : Type*} [Group V] [Finite V]
    (A : Subgroup (MulAut V)) (W : Subgroup V)
    (hA : Nonempty (A ≃* Frobenius21.Model))
    (hV : Nat.card V = 8) (hW : Nat.card W = 4)
    (hWinv : ∀ a : A, ∀ v : V, (a : MulAut V) v ∈ W ↔ v ∈ W) : False := by
  have hd := invariant_card_dvd A W hWinv
  obtain ⟨e⟩ := hA
  have hcardW : Nat.card W = 4 := hW
  rw [(Nat.card_congr e.toEquiv).trans Frobenius21.card_model, hcardW, hV] at hd
  norm_num at hd

/-- The (U^* simeq D_8) branch supplies both the inclusion of the
component in the conjugate local group and the earlier noncontainment. -/
def A6D8Branch {G : Type*} [Group G] (L H' : Subgroup G) : Prop :=
  L ≤ H' ∧ ¬ L ≤ H'

/-- In the (E_4) branch the local rank calculation and quasithin bound are
kept as separate source hypotheses. -/
def A6E4Branch {G : Type*} [Group G] (H' : Subgroup G) : Prop :=
  3 ≤ twoLocalPrimeRank 3 H' ∧ twoLocalPrimeRank 3 H' ≤ 2

/-- The rank-one (C_2) branch retains the actual terminal product model and
its fusion statement. -/
def A6C2Branch {G : Type*} [Group G] (L : Subgroup G) : Prop :=
  (Nonempty (L ≃* (DihedralEight × DihedralEight)) ∨
    Nonempty (L ≃* (QuaternionEight × DihedralEight))) ∧
  (∀ x : L, x ≠ 1 → ∀ y : L, y ≠ 1 → ∃ a : MulAut L, a x = y)

structure A6Input {G : Type*} [Group G] (L H' : Subgroup G) : Prop where
  branch : A6D8Branch L H' ∨ A6E4Branch H' ∨ A6C2Branch L

/-- The assembly theorem for Lemma 16.5.3. -/
theorem not_isomorphic_a6 {G : Type*} [Group G] {L H' : Subgroup G}
    (h : A6Input L H') : False := by
  rcases h.branch with hd | he | hc
  · exact hd.2 hd.1
  · change 3 ≤ twoLocalPrimeRank 3 H' ∧ twoLocalPrimeRank 3 H' ≤ 2 at he
    exact (by omega)
  · exact not_fused_product_center hc.1 hc.2

/-- The noncentral (U^*) branch retains the actual parabolic and the
faithful centralizer calculation. -/
structure L3FourParabolicInput (K : Type*) [Group K] where
  U : Subgroup K
  P : Subgroup K
  U_ne_bot : U ≠ ⊥
  U_le_P : U ≤ P
  P_le_centralizer_U : P ≤ centralizer (U : Set K)
  parabolic_centralizer : P ⊓ centralizer (P : Set K) = ⊥

/-- The maximal-parabolic branch is impossible in the faithful image. -/
theorem l3Four_parabolic_obstruction {K : Type*} [Group K]
    (h : L3FourParabolicInput K) : False := by
  apply h.U_ne_bot
  apply h.U.eq_bot_iff_forall.mpr
  intro u hu
  have huC : u ∈ centralizer (h.P : Set K) := by
    rw [mem_centralizer_iff]
    intro p hp
    exact (mem_centralizer_iff.mp (h.P_le_centralizer_U hp) u hu).symm
  have huI : u ∈ h.P ⊓ centralizer (h.P : Set K) :=
    ⟨h.U_le_P hu, huC⟩
  rw [h.parabolic_centralizer] at huI
  exact mem_bot.mp huI

/-- The central branch uses the actual order-21 image and nonzero proper
Frattini subgroup of the binary center. -/
structure L3FourCentralInput (V : Type*) [Group V] [Finite V] where
  actor : Subgroup (MulAut V)
  W : Subgroup V
  actor_equiv : Nonempty (actor ≃* Frobenius21.Model)
  center_card : Nat.card V = 8
  frattini_card : Nat.card W = 4
  invariant : ∀ a : actor, ∀ v : V,
    (a : MulAut V) v ∈ W ↔ v ∈ W

/-- The two branches of Lemma 16.5.4 retain the faithful parabolic data or the
actual Thompson/Frobenius--21 Frattini data. -/
structure L3FourInput (V : Type*) [Group V] [Finite V] where
  branch : Sum (L3FourParabolicInput V) (L3FourCentralInput V)

/-- Lemma 16.5.4: the faithful image cannot be (L_3(4)), once its two source
branches have been constructed. -/
theorem faithful_image_not_l3_four {V : Type*} [Group V] [Finite V]
    (h : L3FourInput V) : False := by
  rcases h.branch with hp | hc
  · exact l3Four_parabolic_obstruction hp
  · exact frobenius21_frattini_obstruction hc.actor hc.W hc.actor_equiv
      hc.center_card hc.frattini_card hc.invariant

end CFSG.Quasithin.Chapter16.SmallExclusions
