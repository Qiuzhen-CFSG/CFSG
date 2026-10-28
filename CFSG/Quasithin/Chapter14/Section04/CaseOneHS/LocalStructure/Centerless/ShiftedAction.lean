module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.ShiftedAmalgam
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.Geometry
public import Theory.LinearAlgebra.BinaryTwoTransitivity

/-!
# Faithfulness of the shifted center on the original hat module

The action-kernel calculation for the original plane bounds its intersection
with Z(U)^g by Z(U)V₁^g. Two-point transitivity of the full binary L-action
provides an element of H carrying V₁^g to any other seed point V₁^l. Since
both Z(U) and the action kernel are H-invariant, this gives the second bound
without changing the point normalizer or its action on U/Z(U).

When V = V₂V₁^l, the two displaced points are independent modulo V₁ = V∩Z(U).
Their joins with Z(U) therefore intersect in Z(U). The shifted-center identity
and the preceding seed exclusion now prove that Z(I₂^l) acts faithfully.
Applying this to the actual shifted-amalgam witness shows that its involution
has nontrivial image in the original hat action.

This proves the faithfulness step in 14.3.30 and its literal 14.3.31 application.
The explicit seed exclusion is 14.3.25, still owned by qt-d-hs-centerless-source,
as are the order bound, type-a₂ calculation, and subsequent contradictions.
The earlier action alternatives are produced independently, without
centerlessness, by qt-d-hs-action-source. Final LocalStructure assembly remains
with qt-d-hs-local-structure. No conclusion of 14.3.32 is used.

Source: Aschbacher--Smith, 12.8.10(6), 14.3.30--31, printed pp.854,1002--1003.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem conjugate_mul' (A : Subgroup G) (a b : G) :
    conjugate A (a * b) = conjugate (conjugate A a) b := by
  simp only [conjugate, map_map]
  congr 1
  ext x
  simp [mul_assoc]

omit [Finite G] in
private theorem centers_eq_of_points (F : InvariantFlag T V 3) (g l : G)
    (hp : conjugate (F.Vi 1) g = conjugate (F.Vi 1) l) :
    conjugate F.ZU g = conjugate F.ZU l := by
  have hh : g * l⁻¹ ∈ F.H := by
    apply (conjugate_eq_iff _ _).mp
    rw [conjugate_mul', hp]
    simpa only [inv_inv] using conjugate_conjugate_inv (F.Vi 1) l⁻¹
  have hz := (conjugate_eq_iff F.ZU (g * l⁻¹)).mpr (F.H_normalizes_ZU hh)
  have he := congrArg (fun A : Subgroup G => conjugate A l) hz
  simpa only [conjugate_mul', conjugate_conjugate_inv] using he

/-- Full binary action transports the second point while fixing the first. -/
theorem source_point_fixer (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (F : InvariantFlag T V 3) (g l : G)
    (hgV : g ∈ normalizer (V : Set G)) (hlV : l ∈ normalizer (V : Set G))
    (hgH : g ∉ F.H) (hlH : l ∉ F.H) :
    ∃ k ∈ L, k ∈ F.H ∧
      conjugate (conjugate (F.Vi 1) g) k = conjugate (F.Vi 1) l ∧
      conjugate (conjugate F.ZU g) k = conjugate F.ZU l := by
  let := chosen.elementary
  obtain ⟨z, _, hp⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hzV : z ∈ V := F.le_seed 1 (hp ▸ mem_zpowers z)
  have hz : z ≠ 1 := by
    intro he
    have hc := F.card 1 (by decide)
    rw [hp, he, zpowers_one_eq_bot, card_bot] at hc
    norm_num at hc
  let y := g⁻¹ * z * g
  let w := l⁻¹ * z * l
  have hyV : y ∈ V := by
    simpa only [y, inv_inv] using (mem_normalizer_iff.mp ((normalizer (V : Set G)).inv_mem hgV) z).mp hzV
  have hwV : w ∈ V := by
    simpa only [w, inv_inv] using (mem_normalizer_iff.mp ((normalizer (V : Set G)).inv_mem hlV) z).mp hzV
  have hy : y ≠ 1 := by
    intro he
    apply hz
    simpa [y, mul_assoc] using congrArg (fun a : G => g * a * g⁻¹) he
  have hw : w ≠ 1 := by
    intro he
    apply hz
    simpa [w, mul_assoc] using congrArg (fun a : G => l * a * l⁻¹) he
  have hyz : z ≠ y := by
    intro he
    apply hgH
    apply (conjugate_eq_iff _ _).mp
    rw [hp, conjugate, MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    change zpowers y = zpowers z
    rw [← he]
  have hwz : z ≠ w := by
    intro he
    apply hlH
    apply (conjugate_eq_iff _ _).mp
    rw [hp, conjugate, MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    change zpowers w = zpowers z
    rw [← he]
  let z' : Additive V := Additive.ofMul ⟨z, hzV⟩
  let y' : Additive V := Additive.ofMul ⟨y, hyV⟩
  let w' : Additive V := Additive.ofMul ⟨w, hwV⟩
  have hz' : z' ≠ 0 := fun he => hz (congrArg (fun v : Additive V => (v.toMul : G)) he)
  have hy' : y' ≠ 0 := fun he => hy (congrArg (fun v : Additive V => (v.toMul : G)) he)
  have hw' : w' ≠ 0 := fun he => hw (congrArg (fun v : Additive V => (v.toMul : G)) he)
  obtain ⟨f, hfz, hfy⟩ := BinaryLinear.exists_linearEquiv_pair z' y' z' w'
    hz' hy' hz' hw'
    (fun he => hyz (congrArg (fun v : Additive V => (v.toMul : G)) he))
    (fun he => hwz (congrArg (fun v : Additive V => (v.toMul : G)) he))
  let a : MulAut V := MulEquiv.toAdditive.symm f.toAddEquiv
  obtain ⟨x, hx, he⟩ := (higherRankHypothesis d earlier hq chosen).full_L_action a
  have hxz : x * z * x⁻¹ = z := (he ⟨z, hzV⟩).trans
    (congrArg (fun v : Additive V => (v.toMul : G)) hfz)
  have hxy : x * y * x⁻¹ = w := (he ⟨y, hyV⟩).trans
    (congrArg (fun v : Additive V => (v.toMul : G)) hfy)
  have hkH : x⁻¹ ∈ F.H := by
    apply (conjugate_eq_iff _ _).mp
    rw [hp, conjugate, MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hxz]
  have hkP : conjugate (conjugate (F.Vi 1) g) x⁻¹ = conjugate (F.Vi 1) l := by
    rw [hp]
    simp only [conjugate, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv]
    exact congrArg zpowers hxy
  refine ⟨x⁻¹, L.inv_mem hx, hkH, hkP, ?_⟩
  rw [← conjugate_mul']
  exact centers_eq_of_points F _ _ ((conjugate_mul' _ _ _).trans hkP)

/-- The original parabolic calculation bounds the action kernel without
assuming centerlessness. -/
theorem source_conjugate_center_kernel_bound (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    conjugate F.ZU g ⊓ F.uhatAction.ker.map F.H.subtype ≤
      F.ZU ⊔ conjugate (F.Vi 1) g := by
  let := chosen.elementary
  have hk := (source_parabolic_action d earlier hq chosen structural alternatives F hne g hgP hgH).2.1
  have hi := (source_center_intersections d earlier hq chosen structural alternatives F hne g hgP hgH).2.2
  intro x hx
  have hxE : x ∈ F.E g := by
    rw [← hk, F.mem_xHatKernel]
    obtain ⟨y, hy, rfl⟩ := hx.2
    exact ⟨F.conjugate_ZU_le_X g hx.1, (F.mem_uhatAction_ker_iff _).mp hy⟩
  have hxi : x ∈ Chapter12.Section08.centerIn (F.I₂ L) ⊔ conjugate (F.Vi 1) g :=
    hi ▸ (show x ∈ conjugate F.ZU g ⊓ F.U from ⟨hx.1, hxE.1.1⟩)
  apply (sup_le_sup (b := F.ZU) ?_ le_rfl) hxi
  rw [← (source_center_intersections d earlier hq chosen structural alternatives F hne g hgP hgH).1]
  exact inf_le_left

/-- Transport the same action kernel to any second point of the original seed. -/
theorem source_second_center_kernel_bound (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (l : G) (hlV : l ∈ normalizer (V : Set G)) (hlH : l ∉ F.H) :
    conjugate F.ZU l ⊓ F.uhatAction.ker.map F.H.subtype ≤
      F.ZU ⊔ conjugate (F.Vi 1) l := by
  obtain ⟨g, hgP, hgH⟩ := source_conjugator d earlier hq chosen structural F
  obtain ⟨k, _, hkH, hkp, hkz⟩ := source_point_fixer d earlier hq chosen F g l
    (F.P_le_seed_normalizer L chosen.normalizes hgP) hlV hgH hlH
  have hKN : F.H ≤ normalizer (F.uhatAction.ker.map F.H.subtype : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      F.uhatAction.ker.le_normalizer_map F.H.subtype
  have hh := map_mono (f := (MulAut.conj k⁻¹).toMonoidHom)
    (source_conjugate_center_kernel_bound d earlier hq chosen structural alternatives F hne g hgP hgH)
  change conjugate (conjugate F.ZU g ⊓ F.uhatAction.ker.map F.H.subtype) k ≤
    conjugate (F.ZU ⊔ conjugate (F.Vi 1) g) k at hh
  rw [conjugate_inf, hkz, (conjugate_eq_iff _ _).mpr (hKN hkH)] at hh
  have hs : conjugate (F.ZU ⊔ conjugate (F.Vi 1) g) k =
      conjugate F.ZU k ⊔ conjugate (conjugate (F.Vi 1) g) k :=
    Subgroup.map_sup _ _ _
  rw [hs, (conjugate_eq_iff _ _).mpr (F.H_normalizes_ZU hkH), hkp] at hh
  exact hh

omit [Finite G] in
private theorem inf_sup_points (Z A B P W : Subgroup G)
    (hZW : W ⊓ Z = P) (hAW : A ≤ W) (hBW : B ≤ W)
    (hBN : B ≤ normalizer (Z : Set G)) (hAN : A ≤ normalizer (Z : Set G))
    (hdis : (P ⊔ A) ⊓ B = ⊥) :
    (Z ⊔ A) ⊓ (Z ⊔ B) = Z := by
  apply le_antisymm _ (le_inf le_sup_left le_sup_left)
  rintro x ⟨hxA, hxB⟩
  have hxB' : x ∈ (Z : Set G) * (B : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left Z B hBN]
    exact hxB
  obtain ⟨z, hz, b, hb, rfl⟩ := hxB'
  have hbA : b ∈ Z ⊔ A := by
    have hh := (Z ⊔ A).mul_mem ((Z ⊔ A).inv_mem (mem_sup_left hz)) hxA
    simpa only [inv_mul_cancel_left] using hh
  have hbA' : b ∈ (Z : Set G) * (A : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left Z A hAN]
    exact hbA
  obtain ⟨z', hz', a, ha, he⟩ := hbA'
  have hzW : z' ∈ W := by
    have hh := W.mul_mem (hBW hb) (W.inv_mem (hAW ha))
    rw [← he, mul_inv_cancel_right] at hh
    exact hh
  have hzP : z' ∈ P := hZW ▸ (show z' ∈ W ⊓ Z from ⟨hzW, hz'⟩)
  have hbP : b ∈ P ⊔ A := he ▸ (P ⊔ A).mul_mem (mem_sup_left hzP) (mem_sup_right ha)
  have hb1 : b = 1 := by
    have hh : b ∈ (P ⊔ A) ⊓ B := ⟨hbP, hb⟩
    rwa [hdis, mem_bot] at hh
  change z * b ∈ Z
  rw [hb1, mul_one]
  exact hz

/-- Two independent displaced points give independent lines modulo Z(U). -/
theorem source_two_point_intersection (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g l : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hlV : l ∈ normalizer (V : Set G))
    (hspace : V = F.Vi 2 ⊔ conjugate (F.Vi 1) l) :
    (F.ZU ⊔ conjugate (F.Vi 1) g) ⊓
      (F.ZU ⊔ conjugate (F.Vi 1) l) = F.ZU := by
  let := chosen.elementary
  have hPg : conjugate (F.Vi 1) g ≤ V := conjugate_le_of_normalizes
    (F.le_seed 1) g (F.P_le_seed_normalizer L chosen.normalizes hgP)
  have hPl : conjugate (F.Vi 1) l ≤ V := conjugate_le_of_normalizes (F.le_seed 1) l hlV
  have hVN : V ≤ normalizer (F.ZU : Set G) :=
    ((le_conjugateSpanBy V F.H).trans F.U_le_H).trans F.H_normalizes_ZU
  have hdis : F.Vi 2 ⊓ conjugate (F.Vi 1) l = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    change x = 1
    by_contra hx1
    have hx2 : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian x (hPl hx.2)
    have he : zpowers x = conjugate (F.Vi 1) l := eq_of_le_of_card_ge
      (zpowers_le.mpr hx.2) (by
        rw [Nat.card_zpowers, orderOf_eq_prime_iff.mpr ⟨hx2, hx1⟩,
          conjugate, card_map_of_injective (MulAut.conj l⁻¹).injective]
        simpa using (F.card 1 (by decide)).le)
    have hle : conjugate (F.Vi 1) l ≤ F.Vi 2 := he ▸ zpowers_le.mpr hx.1
    have hc : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
    rw [hspace, sup_eq_left.mpr hle, F.card 2 (by decide)] at hc
    norm_num at hc
  apply inf_sup_points _ _ _ (F.Vi 1) V
    (CaseOneGeometry.source_closure d earlier hq chosen structural alternatives F hne).2.2
    hPg hPl (hPl.trans hVN) (hPg.trans hVN)
  rw [← F.plane_eq_point_join_conjugate (by decide) L chosen.normalizes g hgP hgH]
  exact hdis

/-- Faithfulness in source 14.3.30: the shifted center has trivial kernel on
U/Z(U), assuming the preceding seed exclusion, not centerlessness. -/
theorem source_shifted_action_faithful (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (l : G) (hlL : l ∈ L)
    (hl : l ∈ centralizer (conjugate (F.Vi 1) g : Set G))
    (hgen : L = F.orderedResidual L 1 ⊔ conjugate (F.orderedResidual L 1) l)
    (hspace : V = F.Vi 2 ⊔ conjugate (F.Vi 1) l) :
    Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) ⊓
      F.uhatAction.ker.map F.H.subtype = ⊥ := by
  have hlH : l ∉ F.H := by
    intro hh
    have hc : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
    rw [hspace, (conjugate_eq_iff _ _).mpr hh,
      sup_eq_left.mpr (F.monotone (by decide)), F.card 2 (by decide)] at hc
    norm_num at hc
  have hi := source_shifted_center_intersection d earlier hq chosen structural alternatives
    F hne g hgP hgH l hl
  have hd := source_shifted_disjoint_of_residual_pair d earlier hq chosen structural alternatives
    F hne hseed g hgP hgH l hl hgen
  have hg := source_conjugate_center_kernel_bound d earlier hq chosen structural alternatives
    F hne g hgP hgH
  have hl' := source_second_center_kernel_bound d earlier hq chosen structural alternatives
    F hne l (chosen.normalizes hlL) hlH
  have hm := source_two_point_intersection d earlier hq chosen structural alternatives
    F hne g l hgP hgH (chosen.normalizes hlL) hspace
  apply le_bot_iff.mp
  intro x hx
  have hxI := hx.1
  rw [hi] at hxI
  have hxZ : x ∈ F.ZU := hm ▸
    (show x ∈ (F.ZU ⊔ conjugate (F.Vi 1) g) ⊓
      (F.ZU ⊔ conjugate (F.Vi 1) l) from ⟨hg ⟨hxI.1, hx.2⟩, hl' ⟨hxI.2, hx.2⟩⟩)
  exact hd ▸ (show x ∈ F.ZU ⊓ Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) from
    ⟨hxZ, hx.1⟩)

/-- Apply the faithful shifted action to the literal involution and amalgam
from source 14.3.31. In particular the involution survives on U/Z(U). -/
theorem source_shifted_amalgam_faithful (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ g l e : G, g ∈ L ∧ g ∈ F.P L ∧ g ∉ F.H ∧ l ∈ L ∧
      l ∈ centralizer (conjugate (F.Vi 1) g : Set G) ∧
      V = F.Vi 2 ⊔ conjugate (F.Vi 1) l ∧
      L = F.orderedResidual L 1 ⊔ conjugate (F.orderedResidual L 1) l ∧
      orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧ e ∈ F.ZU ∧ e ∉ F.Vi 1 ∧
      let a := l⁻¹ * e * l
      let K := conjugateSpanBy (zpowers a) F.H
      ∃ haH : a ∈ F.H,
        orderOf a = 2 ∧ F.uhatAction ⟨a, haH⟩ ≠ 1 ∧
        Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) ⊓
          F.uhatAction.ker.map F.H.subtype = ⊥ ∧
        K ≤ centralizer (F.ZU : Set G) ∧
        amalgamGroup F L K ≤ centralizer ({e} : Set G) ∧
        IsPReduced 2 ((amalgamModule F L K).subgroupOf (amalgamGroup F L K)) ∧
        pCore 2 (AmalgamQuotient F L K) = ⊥ := by
  obtain ⟨g, l, e, hgL, hgP, hgH, hlL, hl, hspace, hgen, hi, _,
    he, heI, heT, heU, heV, ha, haI, hK, hKe, hr, hcore⟩ :=
    source_shifted_amalgam_of_seed d earlier hq chosen structural alternatives F hne hseed hI
  have hf := source_shifted_action_faithful d earlier hq chosen structural alternatives
    F hne hseed g hgP hgH l hlL hl hgen hspace
  have haH : l⁻¹ * e * l ∈ F.H := by
    have hh := haI
    rw [hi] at hh
    exact F.X_le_H g (F.P_le_G₂ (by decide) L chosen.normalizes hgP)
      (F.conjugate_ZU_le_X g hh.1)
  refine ⟨g, l, e, hgL, hgP, hgH, hlL, hl, hspace, hgen, he, heI,
    heT, heU, heV, haH, ha, ?_, hf, hK, hKe, hr, hcore⟩
  intro hk
  have hx : l⁻¹ * e * l ∈ Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) ⊓
      F.uhatAction.ker.map F.H.subtype :=
    ⟨haI, ⟨⟨l⁻¹ * e * l, haH⟩, hk, rfl⟩⟩
  rw [hf, mem_bot] at hx
  rw [hx, orderOf_one] at ha
  norm_num at ha

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
