module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.SuzukiRecognition.Nonnormality
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.OddPrimes
public import Theory.SpecificGroups.Suzuki.BorelPointwiseRigidity
public import Theory.SpecificGroups.Suzuki.EightOddTori
public import Theory.SpecificGroups.Suzuki.SmallInvolutionPair
public import Theory.GroupTheory.OddCentralizerProduct
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.SuzukiRecognition.ModelConsequences.CubicProduct
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.SuzukiRecognition.ModelConsequences.CubicProduct.OddTori
public import Theory.GroupTheory.FullAutomizerNormalizerControl.Embedding

/-!
# Concrete Suzuki consequences for J.2.9–10

Pointwise Borel rigidity shows that the chosen S₀ centralizes L_s once an
actual Sz(8) isomorphism has been constructed. Intrinsic torus calculations
then give the Sylow orders, the intersections with the parent's involution
centralizers, and the odd-subgroup containment needed by J.2.10.
The actual Sz(2) matrix pair supplies the non-core witness when the parent
provides fusion for involutions in the embedded Suzuki factor.

The cubic-product adapter retains the literal inclusions into N_G(S₀) and
its outer action. Its order, centralizer and
full-automorphism torus calculations feed the final conditional odd-prime
theorem. The strengthened adapter discharges the local automizer premise
and proves the corrected intersection C_G(Y) ∩ N_G(S₀) = YS₀.
The source recognition and odd-complement construction remain with the
parent; the older interface with an explicit local action is preserved.

Source: Aschbacher–Smith, J.2.9–10, printed p.438 (PDF p.449),
refs/quasithin.pdf. Final source assembly belongs to SuzukiRecognition.
-/

@[expose] public section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G]
variable {d : LocalSetup G} (c : Choices d)

/-- Restrict the actual source subgroups and their actions to N_G(S₀). -/
noncomputable def normalizerCubicProduct
    [IsElementaryAbelian 2 c.S0]
    (e : c.Ls ≃* SuzukiMatrixGroup 1)
    (hE : Nat.card c.S0 = 4) (hB : Nat.card c.B = 3)
    (hcentral : c.S0 ≤ centralizer (c.Ls : Set G))
    (hd : Disjoint c.S0 c.Ls)
    (hL : normalizer (c.S0 : Set G) ≤ normalizer (c.Ls : Set G))
    (hBN : c.B ≤ normalizer (c.S0 : Set G))
    (hgen : (c.S0 ⊔ c.Ls) ⊔ c.B = normalizer (c.S0 : Set G))
    (hfree : ∀ b ∈ c.B, b ≠ 1 → ∀ s ∈ c.S0, s ≠ 1 → b * s * b⁻¹ ≠ s)
    (houter : ∀ b ∈ c.B, b ≠ 1 →
      ¬ ∃ l ∈ c.Ls, ∀ x ∈ c.Ls, b * x * b⁻¹ = l * x * l⁻¹) :
    SuzukiRecognition.CubicProduct (normalizer (c.S0 : Set G)) := by
  let N := normalizer (c.S0 : Set G)
  have hLN : c.Ls ≤ N :=
    (le_centralizer_iff.mp hcentral).trans (Subgroup.centralizer_le_normalizer _)
  refine
    { E := c.S0.subgroupOf N
      L := c.Ls.subgroupOf N
      B := c.B.subgroupOf N
      normal_E := normal_subgroupOf_of_le_normalizer le_rfl
      normal_L := normal_subgroupOf_of_le_normalizer hL
      elementary_E := IsElementaryAbelian.subgroupOf le_normalizer
      card_E := (Nat.card_congr (subgroupOfEquivOfLe le_normalizer).toEquiv).trans hE
      model := (subgroupOfEquivOfLe hLN).trans e
      central := ?_
      disjoint := ?_
      card_B := (Nat.card_congr (subgroupOfEquivOfLe hBN).toEquiv).trans hB
      generate := ?_
      fixedPointFree := ?_
      outer := ?_ }
  · intro a ha x hx
    exact Subtype.ext (hcentral ha x hx)
  · apply disjoint_def.mpr
    intro x hxE hxL
    exact Subtype.ext (disjoint_def.mp hd hxE hxL)
  · rw [← subgroupOf_sup le_normalizer hLN,
      ← subgroupOf_sup (sup_le le_normalizer hLN) hBN, hgen]
    exact subgroupOf_self _
  · intro b hb hb1 s hs hs1 he
    exact hfree b hb (fun h => hb1 (Subtype.ext h)) s hs
      (fun h => hs1 (Subtype.ext h)) (congrArg Subtype.val he)
  · rintro b hb hb1 ⟨l, hl, he⟩
    apply houter b hb (fun h => hb1 (Subtype.ext h))
    exact ⟨l, hl, fun x hx => congrArg Subtype.val (he ⟨x, hLN hx⟩ hx)⟩

/-- Discharge the pointwise Borel centralization step of J.2.9 on the original Choices. -/
theorem S0_centralizes_Ls_of_suzuki_model
    (e : c.Ls ≃* SuzukiMatrixGroup 1)
    (P : Sylow 2 c.Ls) (hP : (P : Subgroup c.Ls) = c.S1.subgroupOf c.Ls)
    (hcentral : c.S0 ≤ centralizer (c.Ts : Set G)) :
    c.S0 ≤ centralizer (c.Ls : Set G) := by
  intro a ha
  have hsTs : c.s ∈ c.Ts := ⟨c.s_mem.1, mem_centralizer_singleton_iff.mpr rfl⟩
  have haGs : a ∈ c.Gs :=
    mem_centralizer_singleton_iff.mpr (hcentral ha c.s hsTs).symm
  let n : normalizer (c.Ls : Set G) := ⟨a, c.Gs_normalizes_Ls haGs⟩
  let α := c.Ls.normalizerMonoidHom n
  have hfixP : ∀ x ∈ P, α x = x := by
    intro x hx
    have hxS : (x : G) ∈ c.S1 := by
      change x ∈ c.S1.subgroupOf c.Ls
      rw [← hP]
      exact hx
    apply Subtype.ext
    change a * (x : G) * a⁻¹ = x
    rw [← hcentral ha x (c.S1_le_Ts hxS), mul_inv_cancel_right]
  have hD : Nat.card (c.B7.subgroupOf c.Ls) = 7 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe c.B7_le_Ls).toEquiv]
    exact c.B7_card
  have hfixD : ∀ x ∈ c.B7.subgroupOf c.Ls, α x = x := by
    intro x hx
    apply Subtype.ext
    change a * (x : G) * a⁻¹ = x
    rw [← ha.2 x hx, mul_inv_cancel_right]
  have hα := suzuki_eight_aut_eq_one_of_fixing_sylow_and_seven e P
    (c.B7.subgroupOf c.Ls) hD α hfixP hfixD
  intro x hx
  have he := congrArg (fun f : MulAut c.Ls => ((f ⟨x, hx⟩ : c.Ls) : G)) hα
  change a * x * a⁻¹ = x at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The source Sylow image has prime order and the required involution-centralizer intersection. -/
theorem oddPrime_model_card_and_intersection
    (e : c.Ls ≃* SuzukiMatrixGroup 1)
    (hcentral : c.S0 ≤ centralizer (c.Ls : Set G))
    {p : ℕ} [Fact p.Prime] (hp : p = 7 ∨ p = 13) (Y : Sylow p c.Ls)
    {s0 : G} (hC : centralizer ({s0} : Set G) = c.S0 ⊔ c.Ls) :
    Nat.card Y = p ∧
      Nat.card ((Y : Subgroup c.Ls).map c.Ls.subtype) = p ∧
      centralizer ((Y : Subgroup c.Ls).map c.Ls.subtype : Set G) ⊓
        centralizer ({s0} : Set G) = (Y : Subgroup c.Ls).map c.Ls.subtype ⊔ c.S0 := by
  obtain ⟨hcard, hY⟩ := suzuki_eight_sylow_odd_model e hp Y
  refine ⟨hcard, ?_, ?_⟩
  · rwa [card_map_of_injective c.Ls.subtype_injective]
  · rw [hC]
    exact centralizer_inf_commuting_product c.S0 c.Ls (Y : Subgroup c.Ls) hcentral hY

/-- Supply the centralizer containment for any actual odd subgroup of C_G(Y). -/
theorem oddPrime_odd_subgroup_centralizer_le
    [IsElementaryAbelian 2 c.S0]
    (e : c.Ls ≃* SuzukiMatrixGroup 1)
    (hcentral : c.S0 ≤ centralizer (c.Ls : Set G))
    {p : ℕ} [Fact p.Prime] (hp : p = 7 ∨ p = 13) (Y : Sylow p c.Ls)
    (P : Subgroup G) (hodd : Odd (Nat.card P))
    (hP : P ≤ centralizer ((Y : Subgroup c.Ls).map c.Ls.subtype : Set G))
    {s0 : G} (hC : centralizer ({s0} : Set G) = c.S0 ⊔ c.Ls) :
    P ⊓ centralizer ({s0} : Set G) ≤ (Y : Subgroup c.Ls).map c.Ls.subtype := by
  apply odd_centralizer_le_of_commuting_product _ c.S0 P hodd
    (hcentral.trans (centralizer_le (map_subtype_le _))) ?_ hP
    (c.oddPrime_model_card_and_intersection e hcentral hp Y hC).2.2
  intro a ha
  exact congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 c.S0) (⟨a, ha⟩ : c.S0))

/-- The actual Suzuki pair and its source fusion exclude z from the centralizer two-core. -/
theorem z_not_mem_twoCore_of_suzukiZero_embedding
    {A : Type*} [Group A]
    (hH : centralizer ({c.z} : Set G) = d.toTypeRuSetup.H)
    (hsfusion : ∀ t ∈ d.toTypeRuSetup.H, IsConj c.s t →
      ∃ h ∈ d.toTypeRuSetup.H, h * c.s * h⁻¹ = t)
    {t : G} (hst : IsConj c.s t)
    (f : A × SuzukiMatrixGroup 0 →* centralizer ({t} : Set G))
    (hf : Function.Injective f)
    (hzfusion : ∀ u : A × SuzukiMatrixGroup 0, u.1 = 1 → orderOf u = 2 →
      IsConj c.z (f u : G)) :
    c.z ∉ c.Gs.pCoreIn 2 := by
  obtain ⟨u, v, hu1, hv1, hu, hv, huv⟩ := suzukiZero_pair_in_product (A := A)
  let C := centralizer ({t} : Set G)
  let fG := C.subtype.comp f
  have hfG : Function.Injective fG := C.subtype_injective.comp hf
  have hnot : fG u ∉ C.pCoreIn 2 ∨ fG v ∉ C.pCoreIn 2 := by
    by_contra hn
    push Not at hn
    have hm : fG (u * v) ∈ C.pCoreIn 2 := by
      rw [map_mul]
      exact (C.pCoreIn 2).mul_mem hn.1 hn.2
    have ho : orderOf (⟨fG (u * v), hm⟩ : C.pCoreIn 2) = 5 := by
      rw [← Subgroup.orderOf_coe, orderOf_injective fG hfG, huv]
    have hne : (⟨fG (u * v), hm⟩ : C.pCoreIn 2) ≠ 1 := by
      intro he
      rw [he, orderOf_one] at ho
      norm_num at ho
    have hd := (isPGroup_pCoreIn 2 C).dvd_orderOf hne
    rw [ho] at hd
    norm_num at hd
  rcases hnot with hn | hn
  · exact c.z_not_mem_twoCore_of_local_witness hH hsfusion hst
      (f u).property (hzfusion u hu1 hu) hn
  · exact c.z_not_mem_twoCore_of_local_witness hH hsfusion hst
      (f v).property (hzfusion v hv1 hv) hn

/-- Apply the model calculations to the existing J.2.10 consumer; the local automizer remains explicit. -/
theorem oddPrime_conclusions_of_model_and_local_action
    [IsElementaryAbelian 2 c.S0]
    (e : c.Ls ≃* SuzukiMatrixGroup 1)
    (k : SuzukiRecognition.CubicProduct (normalizer (c.S0 : Set G)))
    (hcentral : c.S0 ≤ centralizer (c.Ls : Set G))
    {p : ℕ} [Fact p.Prime] (hp : p = 7 ∨ p = 13) (Y : Sylow p c.Ls)
    (P : Subgroup G) (hodd : Odd (Nat.card P))
    (a b : normalizer (P : Set G))
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : Commute a b)
    (hdecomp : centralizer ((Y : Subgroup c.Ls).map c.Ls.subtype : Set G) = P ⊔ c.S0)
    (hC : ∀ t ∈ ({(a : G), (b : G), ((a * b : normalizer (P : Set G)) : G)} : Set G),
      centralizer ({t} : Set G) = c.S0 ⊔ c.Ls)
    (haction : ∀ α : MulAut ((Y : Subgroup c.Ls).map c.Ls.subtype),
      ∃ n : normalizer ((Y : Subgroup c.Ls).map c.Ls.subtype : Set G),
        (n : G) ∈ normalizer (c.S0 : Set G) ∧
        ((Y : Subgroup c.Ls).map c.Ls.subtype).normalizerMonoidHom n = α) :
    let YG := (Y : Subgroup c.Ls).map c.Ls.subtype
    Nat.card YG = p ∧
      (∃ S : Sylow p G, (S : Subgroup G) = YG) ∧
      normalizer (YG : Set G) ≤ normalizer (c.S0 : Set G) ∧
      centralizer (YG : Set G) = YG ⊔ c.S0 ∧
      IsCyclic YG.normalizerMonoidHom.range ∧
      Nat.card YG.normalizerMonoidHom.range = p - 1 := by
  apply c.oddPrime_conclusions_of_odd_complement hp Y
    (suzuki_eight_sylow_odd_model e hp Y).1 P hodd a b ha hb hab hdecomp
    (fun t ht => c.oddPrime_odd_subgroup_centralizer_le e hcentral hp Y P hodd
      (by rw [hdecomp]; exact le_sup_left) (hC t ht)) k.card haction

/-- The corrected normalizer intersection and full local automizer, on the literal source images. -/
theorem oddPrime_normalizer_model
    (k : SuzukiRecognition.CubicProduct (normalizer (c.S0 : Set G)))
    (hE : k.E = c.S0.subgroupOf (normalizer (c.S0 : Set G)))
    (hL : k.L = c.Ls.subgroupOf (normalizer (c.S0 : Set G)))
    (hcentral : c.S0 ≤ centralizer (c.Ls : Set G))
    {p : ℕ} [Fact p.Prime] (hp : p = 7 ∨ p = 13) (Y : Sylow p c.Ls) :
    let YG := (Y : Subgroup c.Ls).map c.Ls.subtype
    centralizer (YG : Set G) ⊓ normalizer (c.S0 : Set G) = YG ⊔ c.S0 ∧
      ∀ α : MulAut YG, ∃ n : normalizer (YG : Set G),
        (n : G) ∈ normalizer (c.S0 : Set G) ∧ YG.normalizerMonoidHom n = α := by
  let N := normalizer (c.S0 : Set G)
  have hLN : c.Ls ≤ N :=
    (le_centralizer_iff.mp hcentral).trans (Subgroup.centralizer_le_normalizer _)
  let e : c.Ls ≃* k.L := (subgroupOfEquivOfLe hLN).symm.trans (MulEquiv.subgroupCongr hL.symm)
  let Q := Y.mapSurjective (f := e.toMonoidHom) e.surjective
  let U := (Q : Subgroup k.L).map k.L.subtype
  have hU : U.map N.subtype = (Y : Subgroup c.Ls).map c.Ls.subtype := by
    change (((Y : Subgroup c.Ls).map e.toMonoidHom).map k.L.subtype).map N.subtype = _
    rw [map_map, map_map]
    congr 1
  have hEmap : k.E.map N.subtype = c.S0 := by
    rw [hE, subgroupOf_map_subtype, inf_eq_left.mpr le_normalizer]
  constructor
  · have he := congrArg (Subgroup.map N.subtype) (k.odd_sylow_centralizer hp Q)
    rw [map_centralizer_subtype, Subgroup.map_sup, hU, hEmap] at he
    exact (inf_comm _ N).trans he
  · have h := full_action_on_map_subtype N U (k.odd_sylow_normalizer_surjective hp Q)
    rwa [hU] at h

/-- J.2.10 after the source identification and odd complement; no local automizer premise remains. -/
theorem oddPrime_conclusions_of_model
    [IsElementaryAbelian 2 c.S0]
    (e : c.Ls ≃* SuzukiMatrixGroup 1)
    (k : SuzukiRecognition.CubicProduct (normalizer (c.S0 : Set G)))
    (hE : k.E = c.S0.subgroupOf (normalizer (c.S0 : Set G)))
    (hL : k.L = c.Ls.subgroupOf (normalizer (c.S0 : Set G)))
    (hcentral : c.S0 ≤ centralizer (c.Ls : Set G))
    {p : ℕ} [Fact p.Prime] (hp : p = 7 ∨ p = 13) (Y : Sylow p c.Ls)
    (P : Subgroup G) (hodd : Odd (Nat.card P))
    (a b : normalizer (P : Set G))
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : Commute a b)
    (hdecomp : centralizer ((Y : Subgroup c.Ls).map c.Ls.subtype : Set G) = P ⊔ c.S0)
    (hC : ∀ t ∈ ({(a : G), (b : G), ((a * b : normalizer (P : Set G)) : G)} : Set G),
      centralizer ({t} : Set G) = c.S0 ⊔ c.Ls) :
    let YG := (Y : Subgroup c.Ls).map c.Ls.subtype
    Nat.card YG = p ∧
      (∃ S : Sylow p G, (S : Subgroup G) = YG) ∧
      normalizer (YG : Set G) ≤ normalizer (c.S0 : Set G) ∧
      centralizer (YG : Set G) = YG ⊔ c.S0 ∧
      IsCyclic YG.normalizerMonoidHom.range ∧
      Nat.card YG.normalizerMonoidHom.range = p - 1 := by
  exact c.oddPrime_conclusions_of_model_and_local_action e k hcentral hp Y
    P hodd a b ha hb hab hdecomp hC
    (c.oddPrime_normalizer_model k hE hL hcentral hp Y).2

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
