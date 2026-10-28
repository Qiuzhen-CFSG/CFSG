module
public import Theory.Representation.ExtraspecialBinarySix
public import Theory.Representation.CyclicFixedRank
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.GroupTheory.CyclicSubgroupNormalizer
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.Representation.BinaryGroupAction

/-!
# Cyclic three-subgroups centralizing a small binary displacement

A nonidentity involution in a faithful binary action moves a nonzero space.
If its displacement has dimension at most two, any cyclic three-subgroup
of its centralizer whose cubic subgroup acts fixed-point freely has order
at most three. The restriction to the displacement is faithful, since a
nontrivial kernel contains that unique cubic subgroup; its automorphism
order then divides six.

This is the representation input excluding a larger odd residual above the
extraspecial endpoint in Aschbacher--Smith 15.1.2, printed p.1086.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.ExtraspecialBinarySix
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem cyclic_three_centralizer_card_le
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (t : G) (ht : orderOf t = 2) (hr : fixedCodim ρ (zpowers t) ≤ 2)
    (Z R : Subgroup G) (hZ : Nat.card Z = 3) (hZR : Z ≤ R)
    (hfix : fixedSpace ρ Z = ⊥) (hR : IsPGroup 3 R) [IsCyclic R]
    (hRt : R ≤ centralizer ({t} : Set G)) : Nat.card R ≤ 3 := by
  let W := subspaceCommutator ρ ⊤ (zpowers t)
  have hd : Module.finrank (ZMod 2) W ≤ 2 := by
    rw [fixedCodim_zpowers_eq_displacement_rank] at hr
    have he := congrArg (fun X : Submodule (ZMod 2) V => Module.finrank (ZMod 2) X)
      (CyclicFixedRank.commutator_eq_range ρ t)
    exact he.le.trans hr
  have hW : W ≠ ⊥ := by
    intro hw
    have he : ρ t = ρ 1 := by
      rw [map_one]
      ext v
      have hv : ρ t v - v ∈ W :=
        Submodule.subset_span ⟨t,mem_zpowers t,v,Submodule.mem_top,rfl⟩
      rw [hw,Submodule.mem_bot] at hv
      exact sub_eq_zero.mp hv
    have := hf he
    rw [this,orderOf_one] at ht
    omega
  have hs : R ≤ subspaceStabilizer ρ W := by
    apply subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by simp))
    intro r hrm
    apply centralizer_le_normalizer
    intro x hx
    obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hx
    exact (show Commute t r from (mem_centralizer_singleton_iff.mp (hRt hrm)).symm).zpow_left n
  let σ := (stabilizerRepresentation ρ W).comp (inclusion hs)
  have hσ : Function.Injective σ := by
    apply σ.ker_eq_bot_iff.mp
    by_contra hk
    have hk3 : IsPGroup 3 σ.ker := hR.to_subgroup σ.ker
    have hkcard : 3 ∣ Nat.card σ.ker := hk3.card_eq_or_dvd.resolve_left
      (fun hc => hk (card_eq_one.mp hc))
    obtain ⟨y,hy⟩ := exists_prime_orderOf_dvd_card' (G := σ.ker) 3 hkcard
    let a : R := y
    have ha : orderOf a = 3 := (orderOf_injective σ.ker.subtype σ.ker.subtype_injective y).trans hy
    have hac : Nat.card (zpowers a) = 3 := by rw [Nat.card_zpowers,ha]
    have hay : zpowers a ≤ σ.ker := zpowers_le.mpr y.property
    have hzker : ∀ z : Z, (⟨z,hZR z.property⟩ : R) ∈ σ.ker := by
      intro z
      apply hay
      apply mem_of_pow_card_eq_one_in_cyclic
      rw [hac]
      apply Subtype.ext
      change (z : G) ^ 3 = 1
      exact congrArg Subtype.val (show z ^ 3 = 1 by rw [← hZ]; exact pow_card_eq_one')
    have hWfix : W ≤ fixedSpace ρ Z := by
      intro w hw z
      have he := LinearMap.congr_fun (MonoidHom.mem_ker.mp (hzker z)) (⟨w,hw⟩ : W)
      exact congrArg Subtype.val he
    exact hW (bot_unique (hWfix.trans hfix.le))
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let := BinaryGroupAction.action σ
  let : IsElementaryAbelian 2 (Multiplicative W) := BinaryGroupAction.elementary
  let a := MulDistribMulAction.toMulAut R (Multiplicative W)
  have ha : Function.Injective a := by
    intro x y he
    apply hσ
    ext w
    exact congrArg (fun z : Multiplicative W => ((z.toAdd : W) : V))
      (MulEquiv.congr_fun he (Multiplicative.ofAdd w))
  have hvcard : Nat.card (Multiplicative W) = 2 ^ Module.finrank (ZMod 2) W := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative W ≃ W)]
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
  have hdiv := card_dvd_of_injective a ha
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ _ hvcard] at hdiv
  obtain ⟨n,hn⟩ := hR.exists_card_eq
  have hbound : Nat.card R ∣ 6 := by
    apply hdiv.trans
    interval_cases hdim : Module.finrank (ZMod 2) W <;>
      norm_num [hdim,Fin.prod_univ_succ]
  have hcop : Nat.Coprime (Nat.card R) 2 := by
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_left n
  have hthree : Nat.card R ∣ 3 := hcop.dvd_of_dvd_mul_right hbound
  exact Nat.le_of_dvd (by decide) hthree
end Representation.ExtraspecialBinarySix
