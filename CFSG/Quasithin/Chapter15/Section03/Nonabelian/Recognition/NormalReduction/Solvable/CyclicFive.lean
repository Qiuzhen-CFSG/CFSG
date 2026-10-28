module

public import CFSG.Quasithin.ChapterD.Section02.SmallSupportOrders
public import Theory.GroupAction.IndependentCoprimeSupports
public import Theory.GroupTheory.OddInvolutionEndpointModels
public import Mathlib.FieldTheory.Finiteness

/-!
# The cyclic-five commutator in 15.3.58

Let a finite group act faithfully on a finite-dimensional binary vector space.
If a normal elementary abelian subgroup has prime exponent greater than three,
and an involution has displacement rank two, its nontrivial commutator with
that subgroup is isomorphic to the cyclic group of order five.

Abelianness makes the involution invert the literal subgroup commutator.
D.2.11 forces its prime exponent to be five and bounds its support by dimension
four. Coprime splitting makes its action on that support faithful; the five-part
of the order of GL₄(2) is five. No irreducibility or offender hypothesis is needed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, 15.3.58,
printed p.1149; compare D.2.11–13, printed pp.183–185.
-/

open scoped IsMulCommutative
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction

private theorem commutator_inverted {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal] [IsMulCommutative K]
    (v : G) (hv : IsInvolution v) :
    ∀ r ∈ ⁅K, Subgroup.zpowers v⁆, v * r * v⁻¹ = r⁻¹ := by
  let : MulDistribMulAction G K := MulDistribMulAction.compHom K (MulAut.conjNormal : G →* MulAut K)
  have hm : (commutatorAction (Subgroup.zpowers v) K).map K.subtype = ⁅K, Subgroup.zpowers v⁆ :=
    commutatorAction_subgroup_conj_map_eq_commutator K (Subgroup.zpowers v) Subgroup.le_normalizer_of_normal
  intro r hr
  rw [← hm] at hr
  obtain ⟨r, hr, rfl⟩ := hr
  exact congrArg Subtype.val (Theory.GroupTheory.involution_inverts_abelian_action_commutator v hv r hr)

private theorem support_card_dvd_gl4 {G V : Type*} [Group G] [Finite G]
    [Group V] [Finite V] [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (R : Subgroup G) (hodd : Odd (Nat.card R))
    (hf : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (hU : Nat.card (commutatorAction R V) = 16) : Nat.card R ∣ 20160 := by
  let U := commutatorAction R V
  let : IsInvariant R V U := commutatorAction_isInvariant
  let : IsElementaryAbelian 2 U := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 V) (x : V)) }
  have hinj : Function.Injective (MulDistribMulAction.toMulAut G V) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← fixingSubgroup_univ_eq_ker_toMulAut]
    exact hf
  let : FaithfulSMul G V := ⟨fun {a b} h => hinj (by ext x; exact h x)⟩
  have hcop : Nat.Coprime (Nat.card R) (Nat.card V) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hn]
    exact hodd.coprime_two_right.pow_right n
  let ρ := Representation.ofElementaryAbelianAction (A := R) (G := U) (p := 2)
  have hρ : Function.Injective ρ.asGroupHom := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply bot_unique
    intro r hr
    apply Subtype.ext
    apply ActionSupport.eq_one_of_fixes_support R hcop r
    intro w hw
    have he : ρ r = 1 := congrArg Units.val (MonoidHom.mem_ker.mp hr)
    exact congrArg (fun x : Additive U => (x.toMul : V))
      (LinearMap.congr_fun he (Additive.ofMul ⟨w, hw⟩))
  have hn : Module.finrank (ZMod 2) (Additive U) = 4 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U)
    change Nat.card U = Nat.card (ZMod 2) ^ _ at hc
    rw [hU, Nat.card_zmod] at hc
    exact Nat.pow_right_injective (by decide : 1 < 2) hc.symm
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive U) hn
  let φ : R →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2) :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp ρ.asGroupHom
  have hd := Subgroup.card_dvd_of_injective φ
    ((Matrix.GeneralLinearGroup.toLin' b).symm.injective.comp hρ)
  have hgl : Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ]
  rwa [hgl] at hd

private theorem action_cyclic_five {G V : Type*} [Group G] [Finite G]
    [Group V] [Finite V] [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (hf : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (K : Subgroup G) [K.Normal] {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p K]
    (hp : 3 < p) (v : G) (hv : IsInvolution v)
    (hsmall : Nat.card (commutatorAction (Subgroup.zpowers v) V) ≤ 4)
    (hne : ⁅K, Subgroup.zpowers v⁆ ≠ ⊥) :
    p = 5 ∧ Nonempty ((⁅K, Subgroup.zpowers v⁆ : Subgroup G) ≃* Multiplicative (ZMod 5)) := by
  let R := ⁅K, Subgroup.zpowers v⁆
  have hRK : R ≤ K := Subgroup.commutator_le_left _ _
  have hRp : IsPGroup p R := (IsElementaryAbelian.isPGroup p K).to_le hRK
  have hinv := commutator_inverted K v hv
  obtain ⟨x, hxR, hx⟩ := (Subgroup.bot_or_exists_ne_one R).resolve_left hne
  have hxp : orderOf x = p := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian x (hRK hxR)) hx
  have hxpodd : Odd (orderOf x) := by
    rw [hxp]
    exact (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hp5 : p = 5 := by
    have hh := CFSG.Quasithin.ChapterD.invertedOddElement_order_three_or_five_of_small_involution_support
      (V := V) x v hx hxpodd hv (hinv x hxR) hsmall hf
    rw [hxp] at hh
    omega
  rcases hp5 with rfl
  have hodd : Odd (Nat.card R) := by
    obtain ⟨n, hn⟩ := hRp.exists_card_eq
    rw [hn]
    exact (by decide : Odd 5).pow
  have hUsmall : Nat.card (commutatorAction R V) ≤ 16 := by
    obtain ⟨hs, _, hle⟩ := invertedOddSubgroup_support_card_data (W := V) R hodd v hv hinv
    rw [hs]
    exact (Nat.pow_le_pow_left ((Subgroup.card_le_of_le hle).trans hsmall) 2).trans_eq (by decide)
  have hUx : Nat.card (commutatorAction (Subgroup.zpowers x) V) = 16 := by
    rcases CFSG.Quasithin.ChapterD.invertedOddElement_support_card_four_or_sixteen
      x v hx hxpodd hv (hinv x hxR) hsmall hf with h4 | h16
    · have h3 := CFSG.Quasithin.ChapterD.invertedOddElement_order_three_of_support_card_four
        x v hx hxpodd hv (hinv x hxR) h4 hf
      omega
    · exact h16
  have hsub : commutatorAction (Subgroup.zpowers x) V ≤ commutatorAction R V := by
    rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨a, w, rfl⟩
    exact ⟨⟨a, (Subgroup.zpowers_le.mpr hxR) a.property⟩, w, rfl⟩
  have hU : Nat.card (commutatorAction R V) = 16 :=
    le_antisymm hUsmall (hUx ▸ Subgroup.card_le_of_le hsub)
  have hd := support_card_dvd_gl4 R hodd hf hU
  obtain ⟨n, hn⟩ := hRp.exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra hh
    have h25 : 25 ∣ 20160 := (Nat.pow_dvd_pow 5 (by omega : 2 ≤ n)).trans (hn ▸ hd)
    norm_num at h25
  have hcard : Nat.card R = 5 := by
    have hnot : Nat.card R ≠ 1 := fun hh => hne (Subgroup.card_eq_one.mp hh)
    interval_cases n <;> simp_all
  exact ⟨rfl, ⟨mulEquivOfPrimeCardEq hcard (by simp : Nat.card (Multiplicative (ZMod 5)) = 5)⟩⟩
@[instance_reducible] private def linearAction {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) : MulDistribMulAction G (Multiplicative W) where
  smul g w := Multiplicative.ofAdd (ρ g w.toAdd)
  one_smul w := congrArg Multiplicative.ofAdd (LinearMap.congr_fun ρ.map_one w.toAdd)
  mul_smul g h w := congrArg Multiplicative.ofAdd (LinearMap.congr_fun (ρ.map_mul g h) w.toAdd)
  smul_one g := congrArg Multiplicative.ofAdd (map_zero (ρ g))
  smul_mul g w z := congrArg Multiplicative.ofAdd (map_add (ρ g) w.toAdd z.toAdd)

/-- The nontrivial commutator of a normal elementary subgroup of odd prime
exponent greater than three with a rank-two binary involution is an actual C₅. -/
public theorem elementary_normal_commutator_cyclic_five_of_rank_two
    {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (hf : Function.Injective ρ)
    (K : Subgroup G) [K.Normal] {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p K]
    (hp : 3 < p) (v : G) (hv : IsInvolution v)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (ρ v - LinearMap.id)) = 2)
    (hne : ⁅K, Subgroup.zpowers v⁆ ≠ ⊥) :
    p = 5 ∧ Nonempty ((⁅K, Subgroup.zpowers v⁆ : Subgroup G) ≃* Multiplicative (ZMod 5)) := by
  let : Finite W := Finite.of_injective (Module.finBasis (ZMod 2) W).repr
    (Module.finBasis (ZMod 2) W).repr.injective
  let : IsElementaryAbelian 2 (Multiplicative W) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      change (2 : ℕ) • x.toAdd = 0
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
      exact zero_smul (ZMod 2) x.toAdd) }
  let : MulDistribMulAction G (Multiplicative W) := linearAction ρ
  have hfaith : fixingSubgroup G (Set.univ : Set (Multiplicative W)) = ⊥ := by
    apply bot_unique
    intro g hg
    apply hf
    ext w
    have he := (mem_fixingSubgroup_iff (M := G)).mp hg (Multiplicative.ofAdd w) trivial
    change ρ g w = ρ 1 w
    rw [map_one]
    exact congrArg Multiplicative.toAdd he
  let D := (LinearMap.range (ρ v - LinearMap.id)).toAddSubgroup.toSubgroup
  have hle : commutatorAction (Subgroup.zpowers v) (Multiplicative W) ≤ D := by
    rw [commutatorAction_eq_closure, Subgroup.closure_le]
    rintro _ ⟨a, w, rfl⟩
    have ha : (a : G) = 1 ∨ (a : G) = v := by
      obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp a.property
      have hred : v ^ z = v ^ (z % 2) := by
        simpa only [orderOf_eq_prime hv.2 hv.1, Nat.cast_ofNat] using (zpow_mod_orderOf v z).symm
      rcases Int.emod_two_eq_zero_or_one z with h | h
      · left; rw [← hz, hred, h]; simp
      · right; rw [← hz, hred, h]; simp
    change -w.toAdd + ρ a w.toAdd ∈ LinearMap.range (ρ v - LinearMap.id)
    rcases ha with ha | ha
    · simp only [ha, map_one, Module.End.one_apply, neg_add_cancel]
      exact Submodule.zero_mem _
    · rw [ha]
      exact ⟨w.toAdd, by change ρ v w.toAdd - w.toAdd = -w.toAdd + ρ v w.toAdd; abel⟩
  have hcardD : Nat.card D = 4 := by
    let e : D ≃ LinearMap.range (ρ v - LinearMap.id) := {
      toFun x := ⟨x.val.toAdd, x.property⟩
      invFun x := ⟨Multiplicative.ofAdd x.val, x.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := ZMod 2), hrank, Nat.card_zmod]
    rfl
  exact action_cyclic_five hfaith K hp v hv
    ((Subgroup.card_le_of_le hle).trans_eq hcardD) hne
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction
