module

public import CFSG.Quasithin.ChapterA.Section01.Coprime
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Module
public import Theory.GroupAction.ThompsonFixedNormalizer
public import Theory.GroupAction.SubgroupConjugation
public import Theory.PPrimeCore
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# E.3.40: fixed-space offenders centralize the odd core

For a faithful finite binary representation, every member of the actual
`fixedSpaceFamily ρ 2` centralizes every odd-order subgroup it normalizes.
In particular it centralizes `pPrimeCore 2 X`, the largest normal odd-order
subgroup of X.

A.1.17 generates the odd subgroup by fixed subgroups of actor subgroups
with cyclic quotient. In an elementary abelian two-group those quotients
have order at most two, so the defining fixed-space equality applies.
Thompson's faithful-restriction theorem makes each odd centralizer faithful
on that fixed space. The full actor fixes the space and normalizes the odd
centralizer, hence centralizes it. Applying faithful restriction to the whole
odd centralizer gives the source contradiction directly, without needing
to replace it by its iterated coprime commutator. All normalizations used
here are relative; only the final specialization uses ambient normality.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.3.40,
printed p.240 (PDF p.251), using A.1.17 and A.1.18(2).
-/

public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE

variable {X W : Type*} [Group X] [Finite X]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

private theorem twoCore_eq_bot_of_odd {H : Type*} [Group H] [Finite H]
    (hcop : Nat.Coprime 2 (Nat.card H)) : pCore 2 H = ⊥ := by
  apply bot_unique
  intro x hx
  apply mem_bot.mpr
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)) (⟨x, hx⟩ : pCore 2 H)
  have hp : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hn)
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (hcop.pow_left n) hp (orderOf_dvd_natCard x))

private theorem odd_fixed_centralizer
    (ρ : Representation (ZMod 2) X W) (hρ : Function.Injective ρ)
    (C B A : Subgroup X) (hC : Odd (Nat.card C)) (hB : IsPGroup 2 B)
    (hCB : C ≤ centralizer (B : Set X))
    (hAC : A ≤ normalizer (C : Set X))
    (hfix : fixedSpace ρ B ≤ fixedSpace ρ A) :
    A ≤ centralizer (C : Set X) := by
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative W) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      change (2 : ℕ) • x.toAdd = 0
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
      exact zero_smul (ZMod 2) x.toAdd) }
  let f : X →* MulAut (Multiplicative W) := {
    toFun g := (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)).toAddEquiv.toMultiplicative
    map_one' := by ext v; exact congrArg Multiplicative.ofAdd (LinearMap.congr_fun ρ.map_one v.toAdd)
    map_mul' g h := by ext v; exact congrArg Multiplicative.ofAdd (LinearMap.congr_fun (ρ.map_mul g h) v.toAdd) }
  let : MulDistribMulAction X (Multiplicative W) := MulDistribMulAction.compHom _ f
  let : FaithfulSMul X (Multiplicative W) := ⟨by
    intro x y he
    apply hρ
    ext w
    exact congrArg Multiplicative.toAdd (he (Multiplicative.ofAdd w))⟩
  apply le_centralizer_of_fixes_fixedPoints (V := Multiplicative W) C B A
    (IsElementaryAbelian.isPGroup 2 _) hB
    (commutator_eq_bot_iff_le_centralizer.mpr hCB) (twoCore_eq_bot_of_odd hC.coprime_two_left) hAC
  intro a ha
  rw [mem_fixingSubgroup_iff]
  intro w hw
  apply Multiplicative.toAdd.injective
  change ρ a w.toAdd = w.toAdd
  apply (hfix ?_) (⟨a, ha⟩ : A)
  intro b
  exact congrArg Multiplicative.toAdd (hw b)

/-- The normalized odd-subgroup form of E.3.40. The fixed-space family is
exactly E.3.8, and no commutator or centralization premise is imposed. -/
theorem centralizes_odd_of_mem_fixedSpaceFamily
    (ρ : Representation (ZMod 2) X W) (hρ : Function.Injective ρ)
    {A : Subgroup X} (hA : A ∈ fixedSpaceFamily ρ 2)
    (R : Subgroup X) (hR : Odd (Nat.card R))
    (hAR : A ≤ normalizer (R : Set X)) : A ≤ centralizer (R : Set X) := by
  let : IsElementaryAbelian 2 A := hA.2.1.2
  let : Fact (IsPGroup 2 A) := ⟨IsElementaryAbelian.isPGroup 2 A⟩
  let : MulDistribMulAction A R := conjMulDistribMulActionOfLeNormalizer A R hAR
  have hgen := ChapterA.lemma_A_1_17 (G := R) (A := A) 2 hR.coprime_two_left
  have hle : (⊤ : Subgroup R) ≤ (centralizer (A : Set X)).comap R.subtype := by
    rw [← hgen]
    refine iSup_le fun B => iSup_le fun hB => iSup_le fun _ => ?_
    let D := B.map A.subtype
    have hDA : D ≤ A := by rintro _ ⟨b, _, rfl⟩; exact b.property
    have hidx : D.relIndex A ∣ 2 := by
      have hdiv : B.index ∣ 2 := by
        rw [index_eq_card, ← hB.exponent_eq_card]
        exact (Group.exponent_quotient_dvd B).trans
          (IsElementaryAbelian.exponent_dvd_p 2 A)
      simpa only [D, relIndex, subgroupOf, comap_map_eq, A.ker_subtype, sup_bot_eq] using hdiv
    have hlog : Nat.log 2 (D.relIndex A) < 2 :=
      lt_of_le_of_lt (Nat.log_mono_right (Nat.le_of_dvd (by decide) hidx)) (by decide)
    have hfixed := hA.2.2 D hDA hlog
    let C := R ⊓ centralizer (D : Set X)
    have hAD : A ≤ centralizer (D : Set X) := by
      intro a ha d hd
      exact congrArg Subtype.val (mul_comm (⟨d, hDA hd⟩ : A) (⟨a, ha⟩ : A))
    have hAC : A ≤ normalizer (C : Set X) :=
      (le_inf hAR (hAD.trans (centralizer (D : Set X)).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
    have hC : Odd (Nat.card C) := hR.of_dvd_nat (card_dvd_of_le (show C ≤ R from inf_le_left))
    have hDp : IsPGroup 2 D := ((IsElementaryAbelian.isPGroup 2 A).to_subgroup B).map A.subtype
    have hcent : C ≤ centralizer (A : Set X) := le_centralizer_iff.mp
      (odd_fixed_centralizer ρ hρ C D A hC hDp inf_le_right hAC hfixed.ge)
    intro r hr
    apply hcent
    refine ⟨r.property, ?_⟩
    rintro d ⟨b, hb, rfl⟩
    have hfixedr := congrArg Subtype.val (hr (⟨b, hb⟩ : B))
    change (b : X) * (r : X) * (b : X)⁻¹ = (r : X) at hfixedr
    exact mul_inv_eq_iff_eq_mul.mp hfixedr
  apply le_centralizer_iff.mpr
  intro r hr
  exact hle (mem_top (⟨r, hr⟩ : R))

/-- Aschbacher–Smith E.3.40: a member of A₂(X,W), for a faithful finite
binary X-module W, centralizes the largest normal odd-order subgroup O(X). -/
theorem lemma_E_3_40
    (ρ : Representation (ZMod 2) X W) (hρ : Function.Injective ρ)
    {A : Subgroup X} (hA : A ∈ fixedSpaceFamily ρ 2) :
    A ≤ centralizer (pPrimeCore 2 X : Set X) :=
  centralizes_odd_of_mem_fixedSpaceFamily ρ hρ hA (pPrimeCore 2 X)
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card) le_normalizer_of_normal

end CFSG.Quasithin.ChapterE
