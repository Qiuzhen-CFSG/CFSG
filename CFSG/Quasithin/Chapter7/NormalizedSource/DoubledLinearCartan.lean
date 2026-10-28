module

public import Theory.SpecificGroups.PSL3.LinearThreeSylow.SolvableOvergroups
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.StandardRank
public import Theory.FieldTheory.FiniteAutomorphismOrder
public import Theory.GroupTheory.SolvableSylowControl.AbelianProduct
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.NumberTheory.BinarySemilinearTorusPowers
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.Parameter

/-!
# Cartan bounds for the nonbinary linear-three row

The actual solvable overgroups of a Sylow two-subgroup in PSL₃(2ⁿ), n>1,
normalize that Sylow. Its odd normalizer orders divide (2ⁿ−1)². The outer
quotient has order dividing 2n(2ⁿ−1), retaining the possible diagonal factor.
Thus an actual cyclic Cartan witness of order 2ᶜ−1 divides n(2ⁿ−1)³.
The split-torus Mersenne bound gives c≤n. Faithful descent through the full
central quotient of a perfect group transports the bound without deleting
its scalar center.

Source: Aschbacher–Smith 7.3.4 and A.3.15, printed pp.699 and 50–51,
refs/quasithin.pdf; the linear–field–graph automorphism decomposition in
GLS3, Theorem2.5.12. The original source Hall and module arguments are
separate consumers of this native group calculation.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open ChapterE.Section06.FixedPointBounds
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions Matrix.PSL3.OuterSolvable
variable {F : Type*} [Field F] [Finite F]

private theorem linear_solvable_sylow_control {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1<n) : SolvableSylowControl 2 PSL(3,F) := by
  intro S A hsol hSA
  exact SolvableOvergroups.solvable_overgroup_le_normalizer_of_two_le
    F (by omega) hF S A hsol hSA

private theorem linear_odd_normalizer_order_dvd {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1≤n)
    (Q : Sylow 2 PSL(3,F)) (b : PSL(3,F))
    (hb : b ∈ normalizer (Q : Set PSL(3,F)))
    (ho : Odd (orderOf b)) : orderOf b ∣ (2^n-1)^2 := by
  have hd := orderOf_dvd_natCard (⟨b,hb⟩ : normalizer (Q : Set PSL(3,F)))
  rw [Subgroup.orderOf_mk,
    Nat.card_congr (BorelQuotient.sylowNormalizerEquiv F (by omega) hF Q).toEquiv] at hd
  have hc : Nat.card (borel F) ∣ Nat.card (borelSL F) :=
    card_map_dvd (borelSL F) (Matrix.PSL3.projection F)
  have hd' := hd.trans hc
  rw [DefiningSylow.card_borelSL,hF,←pow_mul] at hd'
  exact (ho.coprime_two_right.pow_right (n*3)).dvd_of_dvd_mul_left hd'

private theorem linear_outer_card_dvd {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 0<n) :
    Nat.card (MulAut.Outer PSL(3,F)) ∣ 2*n*(2^n-1) := by
  have hcover := standard_eq_top_of_two_power_card F hn hF
  have hfull : standardOuter F = ⊤ := by
    rw [standardOuter,hcover,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hfield : Nat.card (F ≃+* F) = n :=
    FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two hF
  have hquot : Nat.card (StandardOuterQuotient F) ∣ n*2 := by
    let f := fieldStandardQuotient F
    let g := graphStandardQuotient F
    have hc : ∀ σ (z : zpowers g), Commute (f σ) ((zpowers g).subtype z) := by
      intro σ ⟨z,hz⟩
      obtain ⟨m,rfl⟩ := hz
      exact (fieldStandardQuotient_commute_graph F σ).zpow_right m
    let φ := f.noncommCoprod (zpowers g).subtype hc
    have hs : Function.Surjective φ := by
      apply MonoidHom.range_eq_top.mp
      exact (MonoidHom.noncommCoprod_range f (zpowers g).subtype hc).trans
        (by rw [range_subtype]; exact standardOuterQuotient_generators F)
    have hg : Nat.card (zpowers g) ∣ 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one (graphStandardQuotient_sq F)
    have hh := card_dvd_of_surjective φ hs
    rw [Nat.card_prod,hfield] at hh
    exact hh.trans (Nat.mul_dvd_mul_left n hg)
  have hdiag : Nat.card ((innerDiagonalOuter F).subgroupOf (standardOuter F)) ∣ 2^n-1 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (innerDiagonalOuter_le_standardOuter F)).toEquiv]
    simpa only [Nat.card_units,hF] using innerDiagonalOuter_card_dvd_units F
  have hh := Nat.mul_dvd_mul hquot hdiag
  rw [←Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((innerDiagonalOuter F).subgroupOf (standardOuter F)),hfull,card_top] at hh
  simpa only [Nat.mul_comm n 2] using hh

theorem doubledLinear_automorphism_nPrime_le {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n)
    (A : Subgroup (MulAut PSL(3,F))) (hA : MulAut.innerSubgroup PSL(3,F) ≤ A) :
    nPrime A ≤ n := by
  let I := MulAut.innerSubgroup PSL(3,F)
  let K := I.subgroupOf A
  let : K.Normal := inferInstance
  let := Atlas.sl_perfect (F := F) 3 (by decide)
  have hi : Function.Injective (MulAut.conj : PSL(3,F) →* MulAut PSL(3,F)) :=
    Theory.GroupTheory.conj_injective_of_center_eq_bot (Group.IsPerfect.center_quotient_center_eq_bot SL(3,F))
  let e : K ≃* PSL(3,F) := (subgroupOfEquivOfLe hA).trans (MonoidHom.ofInjective hi).symm
  have hc : SolvableSylowControl 2 K :=
    SolvableSylowControl.of_equiv e (linear_solvable_sylow_control hF hn)
  have hindex : K.index ∣ 2*n*(2^n-1) :=
    (I.relIndex_dvd_index_of_normal A).trans (linear_outer_card_dvd hF (by omega))
  have hexp (Q : Sylow 2 K) (b : K) (hb : b ∈ normalizer (Q : Set K))
      (ho : Odd (orderOf b)) : b ^ ((2^n-1)^2) = 1 := by
    let S := Q.mapSurjective (f := e.toMonoidHom) e.surjective
    have hmem : e b ∈ normalizer (S : Set PSL(3,F)) :=
      (Q : Subgroup K).le_normalizer_map e.toMonoidHom (mem_map_of_mem _ hb)
    have hd := linear_odd_normalizer_order_dvd hF hn.le S (e b) hmem
      (e.orderOf_eq b ▸ ho)
    rw [e.orderOf_eq] at hd
    exact orderOf_dvd_iff_pow_eq_one.mp hd
  apply nPrime_le_iff.mpr
  intro c w
  let := w.abelian
  let := w.cyclic
  obtain ⟨a,ha⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp
    (inferInstance : IsCyclic w.cyclicGroup)
  have ho : Odd (orderOf (a : A)) := by
    rw [Subgroup.orderOf_coe,ha]
    exact w.odd.of_dvd_nat (card_dvd_of_le w.cyclic_le)
  have hN := odd_abelian_permuting_normalizes_layer_sylow K w.abelianGroup
    w.sylow w.odd w.permutes hc
  have hmem : (a : A) ∈ normalizer ((w.sylow : Subgroup A) ⊓ K : Set A) :=
    hN (mem_sup_left (w.cyclic_le a.property))
  obtain ⟨Q,hQ⟩ := w.sylow.exists_subgroupOf_eq_of_normal K
  let b : K := ⟨(a : A)^K.index,K.pow_index_mem a⟩
  have hb : b ∈ normalizer (Q : Set K) := by
    have hp := (normalizer ((w.sylow : Subgroup A) ⊓ K : Set A)).pow_mem hmem K.index
    have hsub : ((w.sylow : Subgroup A) ⊓ K).subgroupOf K = (Q : Subgroup K) := by
      rw [hQ]
      ext x
      exact and_iff_left x.property
    change b ∈ normalizer ((Q : Subgroup K) : Set K)
    rw [←hsub,←subgroupOf_normalizer_eq (show (w.sylow : Subgroup A) ⊓ K ≤ K from inf_le_right)]
    exact hp
  have hob : Odd (orderOf b) := by
    rw [Subgroup.orderOf_mk]
    exact ho.of_dvd_nat (orderOf_pow_dvd _)
  have he : (a : A) ^ (K.index * (2^n-1)^2) = 1 := by
    simpa only [Subgroup.coe_pow,Subgroup.coe_one,pow_mul] using
      congrArg Subtype.val (hexp Q b hb hob)
  have hd := (orderOf_dvd_of_pow_eq_one he).trans
    (Nat.mul_dvd_mul hindex (dvd_refl ((2^n-1)^2)))
  rw [Subgroup.orderOf_coe,ha,w.card] at hd
  have ho' : Odd (2^c-1) := by
    rwa [Subgroup.orderOf_coe,ha,w.card] at ho
  apply Theory.NumberTheory.binary_mersenne_exponent_le_of_torus_power_dvd (k := 3) (by omega)
  apply ho'.coprime_two_right.dvd_of_dvd_mul_left
  have heq : 2*(n*(2^n-1)^3) = (2*n*(2^n-1))*(2^n-1)^2 := by ring
  rwa [heq]

theorem doubledLinear_centralCover_nPrime_le
    {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (X ⧸ center X) ≃* PSL(3,F))
    (A : Subgroup (MulAut X)) (hA : MulAut.innerSubgroup X ≤ A) : nPrime A ≤ n := by
  let f := MulAut.centralQuotientAction e
  have hf : Function.Injective f := MulAut.centralQuotientAction_injective e
  have hinner : MulAut.innerSubgroup PSL(3,F) ≤ A.map f := by
    rintro b ⟨y,rfl⟩
    obtain ⟨z,rfl⟩ := e.surjective y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center X) z
    exact ⟨MulAut.conj x,hA ⟨x,rfl⟩,MulAut.centralQuotientAction_conj e x⟩
  have hmap : Function.Injective (f.subgroupMap A) := by
    intro a b hab
    exact Subtype.ext (hf (congrArg Subtype.val hab))
  obtain ⟨w⟩ := nPrime_spec (X := A)
  exact (w.map (f.subgroupMap A) (f.subgroupMap_surjective A)
    (hmap.comp w.cyclicGroup.subtype_injective)).le_nPrime.trans
      (doubledLinear_automorphism_nPrime_le hF hn _ hinner)

end CFSG.Quasithin.Chapter7.NormalizedSource
