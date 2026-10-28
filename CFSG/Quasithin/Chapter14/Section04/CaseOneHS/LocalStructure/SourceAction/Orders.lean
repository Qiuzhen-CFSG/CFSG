module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.Geometry
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Transvections.Quotients

/-!
# Orders before selecting the HS natural action

Centerlessness identifies E ∩ Z(U) with the marked point. The symplectic
isotropic bound therefore gives |E| ≤ 2^(d/2+1). In dimension four this
forces E = V, independently of natural coordinates. Counting the literal
map X → X-dot through its kernel E and using [U : W] = 2 gives
2 |E| |X-dot| = |U/Z(U)| |Z(U)|.

The nontrivial conjugate-center image bounds |Z(U)| below by four. Combining
these facts with the actor bounds in the four- and six-dimensional source
rows gives their exact orders. SmallCenter applies these orders to the
original action kernel and the solvable-row exclusion; Center applies the
intersection result to the existing natural-action consumer.

Source: Aschbacher--Smith, 14.3.23(1) and the opening of 14.3.32,
printed pp.999--1000,1003. Centerlessness remains the preceding premise
owned by qt-d-hs-local-structure; selection of the action rows remains with
qt-d-hs-action-source.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The source isotropic intersection has at most twice the order of a maximal isotropic quotient subspace. -/
theorem source_intersection_card_le (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (r : ℕ) (hc : Nat.card F.Uhat = 2 ^ (2 * r))
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) : Nat.card (F.E g) ≤ 2 ^ (r + 1) := by
  let := chosen.elementary
  obtain ⟨htwo, hphi, hVZ⟩ := source_closure d earlier hq chosen structural alternatives F hne
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  let B := F.uhatBilinearForm (by decide) htwo hphi
  have hpU : F.Vi 1 ≤ F.U := (F.le_seed 1).trans (le_conjugateSpanBy V F.H)
  have hPhi : (frattini F.U).map F.U.subtype = F.Vi 1 := by
    rw [hphi, map_subgroupOf_eq_of_le hpU]
  have hgV := F.P_le_seed_normalizer L chosen.normalizes hgP
  have hdis := disjoint_iff.mpr (F.conjugate_point_inf_ZU (by decide) hVZ g hgV hgH)
  let : IsElementaryAbelian 2 (F.E g) := F.E_elementary (by decide) g htwo hPhi hdis
  have hi : ∀ x ∈ hatSpace F (F.E g), ∀ y ∈ hatSpace F (F.E g), B x y = 0 := by
    intro x hx y hy
    obtain ⟨a, ha, hea⟩ := (show x.toMul ∈ hatImage F (F.E g) from hx)
    obtain ⟨b, hb, heb⟩ := (show y.toMul ∈ hatImage F (F.E g) from hy)
    have hab : Commute a b := by
      apply Subtype.ext
      exact congrArg (fun v : F.E g => (v : G))
        (mul_comm (⟨a, ha⟩ : F.E g) ⟨b, hb⟩)
    have hz : F.uhatCommutator htwo (QuotientGroup.mk' (center F.U) a)
        (QuotientGroup.mk' (center F.U) b) = 1 := by
      apply Subtype.ext
      rw [F.uhatCommutator_apply_mk]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hab.eq
    change B (Additive.ofMul x.toMul) (Additive.ofMul y.toMul) = 0
    rw [← hea, ← heb, F.uhatBilinearForm_apply, hz]
    simp only [map_one]
    rfl
  have hb := B.twice_finrank_le_of_isotropic
    (F.uhatBilinearForm_nondegenerate (by decide) htwo hphi) (hatSpace F (F.E g)) hi
  have hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * r := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
    rw [Nat.card_zmod] at hh
    have hh' : 2 ^ (2 * r) = 2 ^ Module.finrank (ZMod 2) (Additive F.Uhat) :=
      hc.symm.trans hh
    exact (Nat.pow_right_injective (by decide) hh').symm
  rw [hd] at hb
  have hVE := F.seed_le_E_of_normalizes g hgV
  have hEU : F.E g ≤ F.U := inf_le_left.trans inf_le_left
  have hEH := (hatMap F (F.E g) hEU).ker.card_mul_index
  rw [index_ker, MonoidHom.range_eq_top.mpr (hatMap_surjective F (F.E g) hEU), card_top] at hEH
  have hk : (hatMap F (F.E g) hEU).ker =
      (F.Vi 1).subgroupOf (F.E g) := by
    rw [hatMap_ker]
    ext x
    change (x : G) ∈ F.ZU ↔ (x : G) ∈ F.Vi 1
    constructor
    · intro hz
      have hzu := (source_center_intersections d earlier hq chosen structural alternatives F hne g hgP hgH).2.1
      rw [hI, bot_sup_eq] at hzu
      rw [← hzu]
      exact ⟨hz, (map_mono (show F.W ≤ F.U from inf_le_left)) x.property.2⟩
    · intro hv
      exact (show F.Vi 1 ≤ F.ZU from hVZ ▸ inf_le_right) hv
  have hkc : Nat.card (hatMap F (F.E g) hEU).ker = 2 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe ((F.le_seed 1).trans hVE)).toEquiv]
    simpa using F.card 1 (by decide)
  rw [hkc] at hEH
  have himg : Nat.card (hatImage F (F.E g)) ≤ 2 ^ r := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := hatSpace F (F.E g))
    rw [Nat.card_zmod] at hh
    change Nat.card (hatSpace F (F.E g)) ≤ 2 ^ r
    rw [hh]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  rw [pow_succ]
  omega

/-- In dimension four, the literal intersection E is V, without any natural-action coordinates. -/
theorem source_intersection_eq_seed_of_card_sixteen (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (hc : Nat.card F.Uhat = 16)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) : F.E g = V := by
  let := chosen.elementary
  have hb := source_intersection_card_le d earlier hq chosen structural alternatives F hne hI
    2 hc g hgP hgH
  have hVE := F.seed_le_E_of_normalizes g (F.P_le_seed_normalizer L chosen.normalizes hgP)
  have hvc : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
  exact (eq_of_le_of_card_ge hVE (by simpa [hvc] using hb)).symm

/-- Count the literal actor through its kernel E and the index-two subgroup W. -/
theorem source_actor_order_identity (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    2 * Nat.card (F.E g) * Nat.card (dotImage F F.uhatAction (F.X g)) =
      Nat.card F.Uhat * Nat.card (center F.U) := by
  let := chosen.elementary
  have ha := source_parabolic_action d earlier hq chosen structural alternatives F hne g hgP hgH
  have hXH := F.X_le_H g (F.P_le_G₂ (by decide) L chosen.normalizes hgP)
  have hk : (dotMap F F.uhatAction (F.X g) hXH).ker = (F.E g).subgroupOf (F.X g) := by
    rw [dotMap_ker]
    change (F.xHatAction g (F.P_le_G₂ (by decide) L chosen.normalizes hgP)).ker = _
    rw [← ha.2.1]
    exact (comap_map_eq_self_of_injective (F.X g).subtype_injective _).symm
  have hXc := (dotMap F F.uhatAction (F.X g) hXH).ker.card_mul_index
  rw [index_ker, MonoidHom.range_eq_top.mpr (dotMap_surjective F F.uhatAction (F.X g) hXH),
    card_top, hk, Nat.card_congr (subgroupOfEquivOfLe (show F.E g ≤ F.X g from inf_le_right)).toEquiv] at hXc
  have hWc := (F.W.subgroupOf F.U).index_mul_card
  rw [show (F.W.subgroupOf F.U).index = F.W.relIndex F.U from rfl,
    ha.2.2.2, Nat.card_congr (subgroupOfEquivOfLe (show F.W ≤ F.U from inf_le_left)).toEquiv] at hWc
  have hXW : Nat.card (F.X g) = Nat.card F.W :=
    card_map_of_injective (MulAut.conj g⁻¹).injective
  rw [mul_assoc, hXc, hXW, hWc]
  exact (center F.U).card_eq_card_quotient_mul_card_subgroup

/-- Centerlessness and the nonextraspecial hypothesis force a center of order at least four. -/
theorem source_center_card_ge_four (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU ≠ F.Vi 1) (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) : 4 ≤ Nat.card (center F.U) := by
  have hn := source_conjugate_center_image_nontrivial d earlier hq chosen structural alternatives
    F hne hZ hI g hgP hgH
  have ho := source_conjugate_center_image_order d earlier hq chosen structural alternatives
    F hne hI g hgP hgH
  have hcard := Nat.card_pos (α := (F.uhatAction.comp
    (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)).range)
  have hneone : Nat.card (F.uhatAction.comp
      (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)).range ≠ 1 := by
    intro he
    exact hn ((Subgroup.card_eq_one).mp he)
  omega

/-- In dimension four, the actor and the intrinsic center have the same order. -/
theorem source_actor_order_eq_center_of_card_sixteen (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (hc : Nat.card F.Uhat = 16)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    Nat.card (dotImage F F.uhatAction (F.X g)) = Nat.card (center F.U) := by
  have he := source_intersection_eq_seed_of_card_sixteen d earlier hq chosen structural alternatives
    F hne hI hc g hgP hgH
  have hi := source_actor_order_identity d earlier hq chosen structural alternatives F hne g hgP hgH
  have hvc : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
  rw [he, hvc, hc] at hi
  omega

/-- The six-dimensional row has the exact source orders once its actor has order at most eight. -/
theorem source_six_dimensional_orders (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU ≠ F.Vi 1) (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (hc : Nat.card F.Uhat = 64)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hX : Nat.card (dotImage F F.uhatAction (F.X g)) ≤ 8) :
    Nat.card (F.E g) = 16 ∧ Nat.card (center F.U) = 4 ∧
      Nat.card (dotImage F F.uhatAction (F.X g)) = 8 := by
  have he := source_intersection_card_le d earlier hq chosen structural alternatives F hne hI
    3 hc g hgP hgH
  have hz := source_center_card_ge_four d earlier hq chosen structural alternatives F hne hZ hI g hgP hgH
  have hi := source_actor_order_identity d earlier hq chosen structural alternatives F hne g hgP hgH
  rw [hc] at hi
  norm_num at he
  have hb := Nat.mul_le_mul he hX
  have hzc : Nat.card (center F.U) = 4 := by nlinarith
  have hec : Nat.card (F.E g) = 16 := by
    have hb := Nat.mul_le_mul_left (Nat.card (F.E g)) hX
    nlinarith
  exact ⟨hec, hzc, by rw [hec, hzc] at hi; omega⟩

/-- The source parabolic quotient makes the literal dotted actor elementary abelian. -/
theorem source_actor_elementary (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    IsElementaryAbelian 2 (dotImage F F.uhatAction (F.X g)) := by
  let := chosen.elementary
  obtain ⟨htwo, hphi, _⟩ := source_closure d earlier hq chosen structural alternatives F hne
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  obtain ⟨⟨hn, he⟩, _⟩ := source_parabolic_action d earlier hq chosen structural alternatives F hne g hgP hgH
  let := hn
  let := he
  exact Xdot_uhatAction_elementary F g (F.P_le_G₂ (by decide) L chosen.normalizes hgP)

/-- The four-dimensional, two-rank-two rows have center order four and tilded center order two. -/
theorem source_four_dimensional_orders (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU ≠ F.Vi 1) (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (hc : Nat.card F.Uhat = 16)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hX : Nat.card (dotImage F F.uhatAction (F.X g)) ≤ 4) :
    F.E g = V ∧ Nat.card (center F.U) = 4 ∧
      Nat.card (dotImage F F.uhatAction (F.X g)) = 4 ∧ Nat.card (F.tilde F.ZU) = 2 := by
  have he := source_intersection_eq_seed_of_card_sixteen d earlier hq chosen structural alternatives
    F hne hI hc g hgP hgH
  have hxc := source_actor_order_eq_center_of_card_sixteen d earlier hq chosen structural alternatives
    F hne hI hc g hgP hgH
  have hz := source_center_card_ge_four d earlier hq chosen structural alternatives F hne hZ hI g hgP hgH
  have hzc : Nat.card (center F.U) = 4 := by omega
  obtain ⟨e⟩ := source_conjugate_center_image_equiv d earlier hq chosen structural alternatives F hne hI g hgP hgH
  have ho := source_conjugate_center_image_order d earlier hq chosen structural alternatives F hne hI g hgP hgH
  rw [Nat.card_congr e.toEquiv, hzc] at ho
  exact ⟨he, hzc, by omega, by omega⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
