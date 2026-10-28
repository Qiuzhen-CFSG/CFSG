module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.ResidualAction
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.PrimeToAction
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The nontrivial residual-image two-core in 14.7.56

Suppose Y is two-perfect, fixes a four-subgroup D pointwise in an elementary
abelian group W of order sixteen, and generates W/Z by commutators, where
Z ≤ D has order two. Then O₂(Aut_Y(W)) is nontrivial.

If that two-core vanished, the action on W/D would be faithful: its kernel
fixes D and W/D and has exponent two. The automorphism group of W/D is S₃,
and a two-perfect subgroup of S₃ lies in A₃. Thus the action has odd order.
Coprime splitting makes the fixed subgroup disjoint from [W,Y]. But
[W,Y]Z=W and D is fixed, forcing D ≤ Z, contrary to their orders.

The application below uses the literal conjugation image and the original
quotient map U → U/V₁. The two-perfectness of the actual
Y=O²(C_H(V₂)) is derived, not assumed as an extra source premise.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 14.7.55(6)
and the last sentence of the proof of 14.7.56(2), printed p.1066.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.SpanSourceActions

open Subgroup
open scoped IsMulCommutative

private theorem odd_of_twoPerfect_embedding_three {J : Type*} [Group J] [Finite J]
    (hp : IsPPerfect 2 J) (f : J →* Equiv.Perm (Fin 3)) (hf : Function.Injective f) :
    Nat.Coprime 2 (Nat.card J) := by
  have hres : pResidual 2 (Equiv.Perm (Fin 3)) ≤ alternatingGroup (Fin 3) := by
    apply sInf_le
    refine ⟨inferInstance, IsPGroup.of_card (n := 1) ?_⟩
    change (alternatingGroup (Fin 3)).index = 2 ^ 1
    rw [alternatingGroup.index_eq_two]
    rfl
  have hr : f.range ≤ alternatingGroup (Fin 3) := by
    have hm := map_pResidual_le 2 f
    rw [(pResidual_eq_top_iff 2 J).mpr hp, ← MonoidHom.range_eq_map] at hm
    exact hm.trans hres
  have hd : Nat.card J ∣ 3 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    have hh := card_dvd_of_le hr
    rwa [hc] at hh
  exact (by decide : Nat.Coprime 2 3).of_dvd_right hd

private noncomputable def fixedQuotientAction {A : Type*} [Group A] (D : Subgroup A) [D.Normal]
    (J : Subgroup (MulAut A)) (hfix : ∀ j ∈ J, ∀ d ∈ D, j d = d) :
    J →* MulAut (A ⧸ D) where
  toFun j := QuotientGroup.congr D D j.val (by
    ext x
    constructor
    · rintro ⟨d, hd, rfl⟩
      change j.val d ∈ D
      rwa [hfix j j.property d hd]
    · intro hx
      exact ⟨x, hx, hfix j j.property x hx⟩)
  map_one' := by
    ext x
    induction x using Quotient.inductionOn with
    | h x => rfl
  map_mul' j k := by
    ext x
    induction x using Quotient.inductionOn with
    | h x => rfl

private theorem fixedQuotientAction_kernel_two {A : Type*} [Group A]
    [IsElementaryAbelian 2 A] (D : Subgroup A) [D.Normal]
    (J : Subgroup (MulAut A)) (hfix : ∀ j ∈ J, ∀ d ∈ D, j d = d) :
    IsPGroup 2 (fixedQuotientAction D J hfix).ker := by
  intro j
  refine ⟨1, ?_⟩
  have hj (a : A) : a⁻¹ * (j.val.val a) ∈ D := by
    have he := MulEquiv.congr_fun (MonoidHom.mem_ker.mp j.property)
      (QuotientGroup.mk' D a)
    exact QuotientGroup.eq.mp he.symm
  have hinv (a : A) : a⁻¹ = a := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) a
  apply Subtype.ext
  apply Subtype.ext
  ext a
  have he := hfix j.val j.val.property _ (hj a)
  simp only [map_mul, hinv] at he
  change j.val.val (j.val.val a) = a
  exact mul_left_cancel (he.trans (mul_comm _ _))

private theorem odd_of_fixed_four_and_corefree {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (D : Subgroup A) (hD : Nat.card D = 4)
    (J : Subgroup (MulAut A)) (hp : IsPPerfect 2 J)
    (hfix : ∀ j ∈ J, ∀ d ∈ D, j d = d) (hcore : J.pCoreIn 2 = ⊥) :
    Nat.Coprime 2 (Nat.card J) := by
  let : Finite (MulAut A) := Finite.of_injective
    (fun a : MulAut A => (a : A → A)) DFunLike.coe_injective
  have hc : pCore 2 J = ⊥ :=
    (map_eq_bot_iff_of_injective _ J.subtype_injective).mp hcore
  let : D.Normal := normal_of_isMulCommutative D
  let f := fixedQuotientAction D J hfix
  have hk : f.ker = ⊥ := by
    apply bot_unique
    rw [← hc]
    exact le_sSup ⟨inferInstance, fixedQuotientAction_kernel_two D J hfix⟩
  have hquot : Nat.card (A ⧸ D) = 4 := by
    have he := D.card_mul_index
    rw [hD, hA] at he
    change D.index = 4
    omega
  let : Nontrivial (A ⧸ D) := Finite.one_lt_card_iff_nontrivial.mp (by rw [hquot]; decide)
  let : IsKleinFour (A ⧸ D) := ⟨hquot, IsElementaryAbelian.exponent_eq_prime⟩
  let e := IsKleinFour.autEquivPermThree (A ⧸ D)
  exact odd_of_twoPerfect_embedding_three hp (e.toMonoidHom.comp f)
    (e.injective.comp ((MonoidHom.ker_eq_bot_iff f).mp hk))

open CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics

/-- The fixed four-group and full quotient commutator span force a nontrivial
two-core in the literal automorphism image. -/
theorem residual_image_core_ne_bot {G : Type*} [Group G] [Finite G]
    (W D Z Y : Subgroup G) [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 16) (hD : Nat.card D = 4) (hZ : Nat.card Z = 2)
    (hDW : D ≤ W) (hZD : Z ≤ D) (hYW : Y ≤ normalizer (W : Set G))
    (hYC : Y ≤ centralizer (D : Set G)) (hp : IsPPerfect 2 Y)
    (hgen : ⁅W,Y⁆ ⊔ Z = W) : (ambientAction Y W hYW).range.pCoreIn 2 ≠ ⊥ := by
  intro hcore
  let f := ambientAction Y W hYW
  have hfix : ∀ j ∈ f.range, ∀ d ∈ D.subgroupOf W, j d = d := by
    rintro _ ⟨y,rfl⟩ d hd
    apply Subtype.ext
    change (y : G) * (d : G) * (y : G)⁻¹ = d
    rw [← (hYC y.property) d hd, mul_inv_cancel_right]
  have hcardD : Nat.card (D.subgroupOf W) = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDW).toEquiv, hD]
  have hcop := odd_of_fixed_four_and_corefree hW (D.subgroupOf W) hcardD f.range
    (hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective) hfix hcore
  have hsplit := (commutator_centralizer_decomposition_of_coprime_image W Y hYW
    (by rw [hW]; exact (hcop.pow_left 4).symm)).2
  have hDC : D ≤ W ⊓ centralizer (Y : Set G) :=
    le_inf hDW ((le_centralizer_iff).mp hYC)
  have hDZ : D ≤ Z := by
    intro d hd

    have hcommW : ⁅W,Y⁆ ≤ W :=
      (le_normalizer_iff_commutator_le_left.mp hYW)
    let M := ⁅W,Y⁆.subgroupOf W
    let ZW := Z.subgroupOf W
    let : M.Normal := normal_of_isMulCommutative M
    have heq : M ⊔ ZW = ⊤ := by
      apply (map_injective W.subtype_injective)
      rw [Subgroup.map_sup, subgroupOf_map_subtype, inf_eq_left.mpr hcommW,
        subgroupOf_map_subtype, inf_eq_left.mpr (hZD.trans hDW), ← MonoidHom.range_eq_map,
        range_subtype, hgen]
    have hdm : (⟨d,hDW hd⟩ : W) ∈ M ⊔ ZW := by rw [heq]; trivial
    obtain ⟨m,hm,z,hz,he⟩ := mem_sup_of_normal_left.mp hdm
    have hmD : (m : G) ∈ D := by
      have hmEq : (m : G) = d * (z : G)⁻¹ := by
        have hv := congrArg Subtype.val he
        exact eq_mul_inv_of_mul_eq hv
      rw [hmEq]
      exact D.mul_mem hd (D.inv_mem (hZD hz))
    have hm1 : (m : G) = 1 := by
      have hi : (m : G) ∈ ⁅W,Y⁆ ⊓ (W ⊓ centralizer (Y : Set G)) := ⟨hm,hDC hmD⟩
      rw [hsplit] at hi
      exact hi
    have heG := congrArg Subtype.val he
    change (m : G) * (z : G) = d at heG
    rw [hm1, one_mul] at heG
    exact heG ▸ hz
  have hc := card_le_of_le hDZ
  rw [hD,hZ] at hc
  omega

/-- Lift commutator generation through the actual quotient U → U/Z. -/
theorem commutator_sup_eq_of_quotient_generation {G : Type*} [Group G]
    (U W Z Y : Subgroup G) [(Z.subgroupOf U).Normal]
    (hWU : W ≤ U) (hZW : Z ≤ W)
    (hYW : Y ≤ normalizer (W : Set G))
    (hquot : ((⁅W,Y⁆).subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) =
      (W.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U))) :
    ⁅W,Y⁆ ⊔ Z = W := by
  have hm : ⁅W,Y⁆ ≤ W := le_normalizer_iff_commutator_le_left.mp hYW
  apply le_antisymm (sup_le hm hZW)
  intro w hw
  have hwq := mem_map_of_mem (QuotientGroup.mk' (Z.subgroupOf U))
    (show (⟨w,hWU hw⟩ : U) ∈ W.subgroupOf U from hw)
  rw [← hquot] at hwq
  obtain ⟨m,hm',he⟩ := hwq
  have hzU : m⁻¹ * (⟨w,hWU hw⟩ : U) ∈ Z.subgroupOf U := QuotientGroup.eq.mp he
  have hz : (m : G)⁻¹ * w ∈ Z := hzU
  have hprod := (⁅W,Y⁆ ⊔ Z).mul_mem (mem_sup_left hm') (mem_sup_right hz)
  change (m : G) * ((m : G)⁻¹ * w) ∈ ⁅W,Y⁆ ⊔ Z at hprod
  simpa only [mul_inv_cancel_left] using hprod

open CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry

/-- Discharge the residual-image seed of the actual span consumer from
14.7.55(6), expressed using the literal quotient map on U. -/
theorem source_residual_image_core_ne_bot {G : Type*} [Group G] [Finite G]
    (H U V V₁ V₂ Y : Subgroup G) [(V₁.subgroupOf U).Normal]
    [IsElementaryAbelian 2 (generatedLineFamily V Y)]
    (hY : Y = localResidual H V₂)
    (hV₂ : V₂ ≤ V) (hV₁ : V₁ ≤ V₂)
    (hWU : generatedLineFamily V Y ≤ U)
    (hW : Nat.card (generatedLineFamily V Y) = 16)
    (hD : Nat.card V₂ = 4) (hZ : Nat.card V₁ = 2)
    (hspan : normalizer (V₂ : Set G) ≤ normalizer (generatedLineFamily V Y : Set G))
    (hYV : Y ≤ normalizer (V₂ : Set G))
    (hquot : ((⁅generatedLineFamily V Y,Y⁆).subgroupOf U).map
        (QuotientGroup.mk' (V₁.subgroupOf U)) =
      ((generatedLineFamily V Y).subgroupOf U).map
        (QuotientGroup.mk' (V₁.subgroupOf U))) :
    (ambientAction Y (generatedLineFamily V Y) (hYV.trans hspan)).range.pCoreIn 2 ≠ ⊥ := by
  have hDW := hV₂.trans (original_le_generated V Y)
  have hp : IsPPerfect 2 Y := by
    rw [hY, localResidual]
    exact isPPerfect_embedded_pResidual 2 _
  refine residual_image_core_ne_bot _ V₂ V₁ Y hW hD hZ hDW hV₁
    (hYV.trans hspan) ?_ hp ?_
  · rw [hY]
    exact localResidual_le_centralizer H V₂
  · exact commutator_sup_eq_of_quotient_generation U _ V₁ Y hWU
      (hV₁.trans hDW) (hYV.trans hspan) hquot

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.SpanSourceActions
