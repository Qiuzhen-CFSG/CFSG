module

public import Theory.SpecificGroups.PSL2.PairedOuterThree
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Group.Subgroup.Actions

/-!
# Prime-to-p field images of a pair of binary PSL₂ components

A subgroup of Aut(S) × Aut(S) containing both inner factors also contains
its pure field sections. A field pair of prime order p fixes an element
of order p in each component whenever p divides |S|: this is the p-group
fixed-point congruence followed by Cauchy's theorem. Their independent
inner actors, together with the outer field pair, form an elementary
abelian group of rank three. Thus rank at most two forces p-prime field
image and p-prime index of the literal inner preimage.

Source: Aschbacher--Smith 1.2.2(a), printed p.504, as used in 10.1.3 and
the automorphism decomposition of 10.2.3, printed pp.742,745. This extends
the prime-three calculation without assuming that the full outer group
has p-prime order. The actual component-pair index consumer is in
`Theory.GroupTheory.TwoOrbitOddPrime.BinaryIndex`.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.PSL2.PairedOuterPrime
variable (F : Type*) [Field F] [CharP F 2] [Finite F]
variable (p : ℕ) [Fact p.Prime]

private theorem exists_fixed_prime {S : Type*} [_root_.Group S] [Finite S]
    (α : MulAut S) (hα : α ^ p = 1) (hd : p ∣ Nat.card S) :
    ∃ x : S, orderOf x = p ∧ α x = x := by
  let P := zpowers α
  have hP : IsPGroup p P := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [P,Nat.card_zpowers,pow_one] using orderOf_dvd_of_pow_eq_one hα)
  have hc := hP.card_modEq_card_fixedPoints S
  have hd' : p ∣ Nat.card (FixedPoints.subgroup P S) :=
    Nat.modEq_zero_iff_dvd.mp (hc.symm.trans hd.modEq_zero_nat)
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' p hd'
  exact ⟨x,(orderOf_injective (FixedPoints.subgroup P S).subtype
    Subtype.val_injective x).trans hx,x.property ⟨α,mem_zpowers α⟩⟩

/-- A prime-order field pair adds a third independent prime-order actor to
fixed inner actors in the two factors. -/
theorem image_coprime
    (A : Subgroup (MulAut (Group F) × MulAut (Group F)))
    (hI : (inner F).prod (inner F) ≤ A) (hr : primeRank p A ≤ 2)
    (hd : p ∣ Nat.card (Group F)) :
    Nat.Coprime p (Nat.card (A.map (PairedOuterThree.projection F))) := by
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
  intro hdiv
  let : Finite (F ≃+* F) := Finite.of_injective (fun σ : F ≃+* F => (σ : F → F)) DFunLike.coe_injective
  let π := PairedOuterThree.projection F
  let s := PairedOuterThree.sectionMap F
  obtain ⟨σ,hσ⟩ := exists_prime_orderOf_dvd_card' p hdiv
  let x : A := ⟨s σ,PairedOuterThree.section_mem_of_full_inner F A hI σ σ.property⟩
  have hx : orderOf x = p := by
    rw [←orderOf_injective A.subtype A.subtype_injective x]
    change orderOf (s σ.val) = p
    rw [orderOf_injective _ (PairedOuterThree.section_injective F)]
    exact (orderOf_injective (A.map π).subtype Subtype.val_injective σ).trans hσ
  have hσpow : (σ.val) ^ p = 1 := by
    have hh := congrArg Subtype.val (hσ ▸ pow_orderOf_eq_one σ)
    exact hh
  have ha : (fieldAut σ.val.1) ^ p = 1 := by
    change fieldAutHom σ.val.1 ^ p = 1
    rw [←map_pow,show σ.val.1 ^ p = 1 from congrArg Prod.fst hσpow,map_one]
  have hb : (fieldAut σ.val.2) ^ p = 1 := by
    change fieldAutHom σ.val.2 ^ p = 1
    rw [←map_pow,show σ.val.2 ^ p = 1 from congrArg Prod.snd hσpow,map_one]
  obtain ⟨a,ha,hfa⟩ := exists_fixed_prime p (fieldAut σ.val.1) ha hd
  obtain ⟨b,hb,hfb⟩ := exists_fixed_prime p (fieldAut σ.val.2) hb hd
  have hinj : Function.Injective (MulAut.conj : Group F →* MulAut (Group F)) := by
    rw [←MonoidHom.ker_eq_bot_iff]
    apply bot_unique
    intro z hz
    exact psl2_conj_eq_one_implies z hz
  let a' := MulAut.conj a
  let b' := MulAut.conj b
  have ha' : orderOf a' = p := (orderOf_injective _ hinj a).trans ha
  have hb' : orderOf b' = p := (orderOf_injective _ hinj b).trans hb
  let E₀ := (zpowers a').prod (zpowers b')
  let : IsElementaryAbelian p (zpowers a') :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (ha' ▸ pow_orderOf_eq_one a')
  let : IsElementaryAbelian p (zpowers b') :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hb' ▸ pow_orderOf_eq_one b')
  let eE : E₀ ≃* (zpowers a' × zpowers b') := Subgroup.prodEquiv _ _
  let : IsElementaryAbelian p E₀ := {
    toIsMulCommutative := ⟨⟨fun a b => eE.injective (by rw [map_mul,map_mul]; exact mul_comm _ _)⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun y => by
      apply Subtype.ext
      exact Prod.ext (elemPow_eq_one_of_isElementaryAbelian y.val.1 y.property.1)
        (elemPow_eq_one_of_isElementaryAbelian y.val.2 y.property.2)) }
  have hEI : E₀ ≤ (inner F).prod (inner F) := by
    rintro y ⟨hy₁,hy₂⟩
    exact ⟨zpowers_le.mpr (show a' ∈ inner F from ⟨a,rfl⟩) hy₁,
      zpowers_le.mpr (show b' ∈ inner F from ⟨b,rfl⟩) hy₂⟩
  have hEA := hEI.trans hI
  let E := E₀.subgroupOf A
  let : IsElementaryAbelian p E := IsElementaryAbelian.subgroupOf hEA
  have hc : Nat.card E = p ^ 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEA).toEquiv,
      Nat.card_congr eE.toEquiv,Nat.card_prod,Nat.card_zpowers,Nat.card_zpowers,ha',hb',pow_two]
  have hxE : x ∉ E := by
    intro he
    have hi : s σ.val ∈ π.ker := (PairedOuterThree.projection_ker F).symm ▸ hEI he
    have hs : σ.val = 1 := (PairedOuterThree.projection_section F σ).symm.trans hi
    have hs' : σ = 1 := Subtype.ext hs
    rw [hs',orderOf_one] at hσ
    exact (Fact.out : p.Prime).ne_one hσ.symm
  have hcomm (β : MulAut (Group F)) (y : Group F) (hy : β y = y) :
      Commute β (MulAut.conj y) := by
    apply MulEquiv.ext
    intro z
    change β (y*z*y⁻¹) = y*β z*y⁻¹
    rw [map_mul,map_mul,map_inv,hy]
  have hfix : E ≤ centralizer ({x} : Set A) := by
    intro y hy
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    apply Prod.ext
    · exact mem_centralizer_singleton_iff.mp
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hcomm _ a hfa).eq.symm) hy.1)
    · exact mem_centralizer_singleton_iff.mp
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hcomm _ b hfb).eq.symm) hy.2)
  have hl := IsElementaryAbelian.primeRank_ge_of_fixed_join E x hx hxE hfix hc
  omega

/-- The literal preimage of the inner product has prime-to-p index. -/
theorem quotient_by_inner_preimage_coprime
    {D : Type*} [_root_.Group D] [Finite D]
    (a : D →* MulAut (Group F) × MulAut (Group F))
    (hI : (inner F).prod (inner F) ≤ a.range) (hr : primeRank p a.range ≤ 2)
    (hd : p ∣ Nat.card (Group F)) :
    Nat.Coprime p (Nat.card (D ⧸ ((inner F).prod (inner F)).comap a)) := by
  let f := (PairedOuterThree.projection F).comp a
  have hk : f.ker = ((inner F).prod (inner F)).comap a := by
    change ((PairedOuterThree.projection F).comp a).ker = _
    rw [←MonoidHom.comap_ker,PairedOuterThree.projection_ker]
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange f)
  rw [Nat.card_congr e.toEquiv,MonoidHom.range_comp]
  exact image_coprime F p a.range hI hr hd
end Theory.PSL2.PairedOuterPrime
