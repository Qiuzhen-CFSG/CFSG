module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlockSpecializationProductsReduction
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.MovingResidualConstructionCubic
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.NormalizerAction
public import Theory.SpecificGroups.PSL3Two.InvolutionResidual
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The literal plane residual and the second MS centralizer product

The marked image of C_L(E) has order twelve. Its two-residual image still
has order divisible by three, giving an element of the original embedded
L₁ whose action on V is cubic. A nontrivial cubic action on sixteen vectors
fixes at most four: the fixed subgroup has two-power order and its order is
congruent to sixteen modulo three. Thus C_V(L₁) is exactly E.

An element of C_R(L₁) induces a two-element of the marked SL₃(2) action,
by the common-normalizer theorem. It commutes with the cubic just constructed.
If it were nontrivial, a power would be an involution whose two-group
centralizer contained that cubic. Consequently C_R(L₁) centralizes V.
This route does not require V ≤ L₁ or identify the residual's action image
with its quotient by its own two-core.

The final consumer assumes the independently produced first centralizer
product and applies both action facts to obtain C_R(L₁) = E C_T(L).
The earlier Structural1222 and SLThreeAlternative1222 premises remain with
the Section 12.2 source producers and the parent centralizer-products assembly.
No fifth-MS model premise beyond the original marked extension is needed.

Source: Aschbacher--Smith, proof of 12.4.6, printed pp.813--814;
the four-dimensional extension in B.4.8, pp.91--92, and C.1.34(5), pp.136--137.
-/

public section


open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

private theorem two_element_centralizing_cubic
    (a b : BinaryLinearThree.Group) (ha : ∃ n : ℕ, a ^ (2 ^ n) = 1)
    (hb : orderOf b = 3) (hab : Commute a b) : a = 1 := by
  have hp : IsPGroup 2 (zpowers a) := by
    obtain ⟨n, hn⟩ := ha
    apply IsPGroup.of_card_dvd_pow (n := n)
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hn
  by_contra hn
  have hne : zpowers a ≠ ⊥ := by
    intro he
    exact hn (mem_bot.mp (he ▸ mem_zpowers a))
  let : Nontrivial (zpowers a) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := zpowers a) 2
    (hp.card_eq_or_dvd.resolve_left (by have : 1 < Nat.card (zpowers a) := Finite.one_lt_card; omega))
  have ht' : orderOf (t : BinaryLinearThree.Group) = 2 :=
    (Subgroup.orderOf_coe t).trans ht
  have hbt : b ∈ centralizer ({(t : BinaryLinearThree.Group)} : Set BinaryLinearThree.Group) := by
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp t.property
    apply mem_centralizer_singleton_iff.mpr
    rw [← hn]
    exact (hab.symm.zpow_right n).eq
  obtain ⟨n, hn⟩ := (Matrix.PSL3Two.InvolutionResidual.sl_centralizer_two t ht')
    ⟨b, hbt⟩
  have hbpow : b ^ (2 ^ n) = 1 := congrArg Subtype.val hn
  have hd : 3 ∣ 2 ^ n := hb ▸ orderOf_dvd_of_pow_eq_one hbpow
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

/-- A nontrivial cubic action on the original four-space fixes at most four
vectors. The fixed-point congruence excludes a binary hyperplane. -/
theorem cubic_fixed_card_le_four (ext : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥) (b : BinaryLinearThree.Group)
    (hb : orderOf b = 3) : letI := D.elementary
    Nat.card (BinaryOffender.fixedSpace ext.action (zpowers b)) ≤ 4 := by
  let _ := D.elementary
  let F := BinaryOffender.fixedSpace ext.action (zpowers b)
  let : MulAction (zpowers b) (Additive V) := {
    smul := fun g v => ext.action g v
    one_smul := by intro v; change ext.action 1 v = v; rw [map_one]; rfl
    mul_smul := by
      intro g k v
      change ext.action ((g : BinaryLinearThree.Group) * k) v =
        ext.action g (ext.action k v)
      rw [map_mul, Module.End.mul_apply] }
  let e : F ≃ MulAction.fixedPoints (zpowers b) (Additive V) := {
    toFun := fun v => ⟨v, v.property⟩
    invFun := fun v => ⟨v, v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hp : IsPGroup 3 (zpowers b) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, hb]; rfl)
  have hm := hp.card_modEq_card_fixedPoints (Additive V)
  rw [← Nat.card_congr e] at hm
  have hcard : Nat.card (Additive V) = 16 := module_card_sixteen ext hne
  have hd := SLThreeCommutatorSource.module_finrank_four ext hne
  have hlt : Module.finrank (ZMod 2) F < 4 := by
    have hle := F.finrank_le
    rw [hd] at hle
    by_contra hnot
    have hdim : Module.finrank (ZMod 2) F = Module.finrank (ZMod 2) (Additive V) := by omega
    have ht : F = ⊤ := Submodule.eq_top_of_finrank_eq hdim
    have he : ext.action b = 1 := by
      apply LinearMap.ext
      intro v
      exact (show v ∈ F from ht ▸ Submodule.mem_top) ⟨b, mem_zpowers b⟩
    have hb1 := SLThreeCommutatorSource.action_injective ext (he.trans (map_one ext.action).symm)
    simp only [hb1, orderOf_one] at hb
    omega
  rw [hcard, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hm
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  change 16 % 3 = (2 ^ Module.finrank (ZMod 2) F) % 3 at hm
  interval_cases n : Module.finrank (ZMod 2) F <;> norm_num [n] at *

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}
namespace LocalGeometry
variable (d : LocalGeometry D)

/-- The image of the literal plane centralizer under the marked core quotient. -/
theorem planeCentralizer_action_card (ext : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥) (hFE : fixedSubgroup L V ≤ d.E) :
    Nat.card (((centralizer (d.E : Set G)).subgroupOf L).map
      (ext.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) = 12 := by
  let q := ext.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let C := (centralizer (d.E : Set G)).subgroupOf L
  have hq : Function.Surjective q := ext.quotientEquiv.surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hkC : q.ker ≤ C := by
    intro l hl v hv
    have he := ext.conjugation l (Additive.ofMul ⟨v, d.le_module hv⟩)
    have hq1 : ext.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) = 1 := hl
    rw [hq1, map_one] at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  have hi : C.index = 14 := by
    change (centralizer (d.E : Set G)).relIndex L = 14
    rw [← inf_relIndex_left L (centralizer (d.E : Set G)),
      d.component_plane_centralizer_eq_point ext hne hFE, inf_relIndex_left]
    exact component_point_centralizer_index ext hne d.v
      (d.le_module d.mem_plane) d.nonfixed
  have hiq : (C.map q).index = 14 := (C.index_map_eq hq hkC).trans hi
  have hc := (C.map q).index_mul_card
  rw [hiq, Matrix.PSL3Two.card_SL] at hc
  change Nat.card (C.map q) = 12
  omega

/-- The original residual contains an element whose actual marked action has
order three. Its image is retained, rather than identified with L₁/O₂(L₁). -/
theorem exists_lineResidual_cubic_actor (ext : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥) (hFE : fixedSubgroup L V ≤ d.E) :
    ∃ l : L, (l : G) ∈ d.L₁ ∧
      orderOf (ext.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)) = 3 := by
  let q := ext.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let C := (centralizer (d.E : Set G)).subgroupOf L
  let B := C.map q
  have hc : Nat.card B = 12 := d.planeCentralizer_action_card ext hne hFE
  have h3 : 3 ∣ Nat.card (pResidual 2 B) := by
    have hd : 3 ∣ Nat.card B := by rw [hc]; decide
    rw [← (pResidual 2 B).card_mul_index] at hd
    apply (Nat.prime_three.dvd_mul.mp hd).resolve_right
    obtain ⟨n, hn⟩ := (isPGroup_quotient_pResidual (G := B) 2).exists_card_eq
    rw [index_eq_card, hn]
    exact fun hd => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := pResidual 2 B) 3 h3
  have hm := map_pResidual_of_surjective 2 (q.subgroupMap C) (q.subgroupMap_surjective C)
  obtain ⟨c, hc, hcb⟩ := (hm.ge b.property : (b : B) ∈
    (pResidual 2 C).map (q.subgroupMap C))
  let j : C →* (L ⊓ centralizer (d.E : Set G) : Subgroup G) := {
    toFun := fun x => ⟨x.val, x.val.property, x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  refine ⟨c.val, ?_, ?_⟩
  · exact ⟨j c, map_pResidual_le 2 j (mem_map_of_mem j hc), rfl⟩
  · have he : q c.val = (b.val : BinaryLinearThree.Group) := congrArg Subtype.val hcb
    change orderOf (q c.val) = 3
    rw [he, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hb]

end LocalGeometry
end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Subgroup Theory.GroupTheory Representation Section02
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}
namespace LocalGeometry
variable (d : LocalGeometry D)

/-- The literal residual fixes exactly the original plane in V. -/
theorem module_inf_lineResidual_centralizer (ext : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥) (hFE : fixedSubgroup L V ≤ d.E) :
    V ⊓ centralizer (d.L₁ : Set G) = d.E := by
  let _ := D.elementary
  obtain ⟨x, hx, hx3⟩ := d.exists_lineResidual_cubic_actor ext hne hFE
  let b := ext.quotientEquiv (QuotientGroup.mk' (pCore 2 L) x)
  let C := V ⊓ centralizer ({(x : G)} : Set G)
  let F := BinaryOffender.fixedSpace ext.action (zpowers b)
  have hf (v : Additive V) : v ∈ F ↔
      (v.toMul : G) ∈ centralizer ({(x : G)} : Set G) := by
    rw [BinaryOffender.mem_fixedSpace_zpowers_iff, mem_centralizer_singleton_iff]
    constructor
    · intro hv
      have he := ext.conjugation x v
      change ((ext.action b v).toMul : G) = _ at he
      rw [hv] at he
      exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
    · intro hv
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [ext.conjugation, hv.symm, mul_inv_cancel_right]
  let e : C ≃ F := {
    toFun := fun v => ⟨Additive.ofMul ⟨v, v.property.1⟩, (hf _).mpr v.property.2⟩
    invFun := fun v => ⟨v.val.toMul, v.val.toMul.property, (hf _).mp v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hC : Nat.card C ≤ 4 := (Nat.card_congr e).le.trans
    (cubic_fixed_card_le_four ext hne b hx3)
  have hle : d.E ≤ V ⊓ centralizer (d.L₁ : Set G) :=
    le_inf d.le_module (le_centralizer_iff.mpr (d.lineResidual_le.trans inf_le_right))
  apply (eq_of_le_of_card_ge hle ?_).symm
  rw [d.card_plane]
  exact (card_le_of_le (inf_le_inf_left V
    (centralizer_le (Set.singleton_subset_iff.mpr hx)))).trans hC

/-- A two-element centralizing the literal residual acts trivially on V.
The action image contains a cubic element; involution centralizers in SL₃(2)
are two-groups. -/
theorem residual_centralizer_le_module_centralizer (ext : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥) (hFE : fixedSubgroup L V ≤ d.E)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    d.R ⊓ centralizer (d.L₁ : Set G) ≤ centralizer (V : Set G) := by
  let _ := D.elementary
  obtain ⟨x, hx, hx3⟩ := d.exists_lineResidual_cubic_actor ext hne hFE
  intro r hr
  obtain ⟨l, hl, hsame⟩ := SLThreeCommutatorSource.same_action_of_common_normalizer ext
    r (hTV hr.1.1) (hTL hr.1.1)
  let a := ext.quotientEquiv (QuotientGroup.mk' (pCore 2 L) ⟨l, hl⟩)
  let b := ext.quotientEquiv (QuotientGroup.mk' (pCore 2 L) x)
  have ha (v : Additive V) : ((ext.action a v).toMul : G) =
      r * (v.toMul : G) * r⁻¹ :=
    (ext.conjugation ⟨l, hl⟩ v).trans (hsame v.toMul v.toMul.property).symm
  have hab : Commute a b := by
    apply SLThreeCommutatorSource.action_injective ext
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      ha, ext.conjugation, ext.conjugation, ha]
    have hc : Commute r (x : G) := (hr.2 x hx).symm
    exact congrArg (fun f : MulAut G => f (v.toMul : G))
      (hc.map (MulAut.conj : G →* MulAut G)).eq
  have hpow (n : ℕ) (v : Additive V) :
      ((ext.action (a ^ n) v).toMul : G) = r ^ n * (v.toMul : G) * (r ^ n)⁻¹ := by
    induction n generalizing v with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, map_mul, Module.End.mul_apply, ih, ha, pow_succ]
      group
  have hp : ∃ n : ℕ, a ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := T.isPGroup' ⟨r, hr.1.1⟩
    have hrpow : r ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    refine ⟨n, SLThreeCommutatorSource.action_injective ext ?_⟩
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hpow, hrpow, map_one]
    simp
  have ha1 : a = 1 := two_element_centralizing_cubic a b hp hx3 hab
  intro v hv
  have he := ha (Additive.ofMul ⟨v, hv⟩)
  rw [ha1, map_one] at he
  exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm

end LocalGeometry
end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Subgroup Theory.GroupTheory Representation Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}
namespace LocalGeometry
variable (d : LocalGeometry D)

/-- Both residual-action premises of the original second centralizer product,
from the source geometry. The earlier 12.2 inputs remain with the source assembly. -/
theorem ms_residual_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    d.R ⊓ centralizer (d.L₁ : Set G) ≤ centralizer (V : Set G) ∧
      V ⊓ centralizer (d.L₁ : Set G) = d.E := by
  obtain ⟨ext⟩ := marked G T L V h D hmodel hne
  have hFE := d.fixed_le_plane h structural marked hmodel hne hescape
  exact ⟨d.residual_centralizer_le_module_centralizer ext hne hFE
    ((structural G T L h).2.2 V D).1 (structural G T L h).1,
    d.module_inf_lineResidual_centralizer ext hne hFE⟩

/-- Apply the residual action to the literal second product. The independent
first product is assumed only here; its discharge belongs to the parent
centralizer-products assembly. -/
theorem ms_residual_centralizer_product
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hproduct : (T : Subgroup G) ⊓ centralizer (V : Set G) =
      V ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G))) :
    d.R ⊓ centralizer (d.L₁ : Set G) =
      d.E ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  obtain ⟨himage, hfixed⟩ := d.ms_residual_action h structural marked hmodel hne hescape
  exact d.ms_residual_centralizer_of_geometry hproduct himage hfixed

end LocalGeometry
end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
