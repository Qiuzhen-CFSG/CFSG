module
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableSupplement
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.OuterOrder
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.GroupTheory.SolvableSylowControl.AbelianProduct
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.NumberTheory.BinarySemilinearTorusPowers
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.Parameter

/-!
# Cartan bounds for the nonbinary symplectic row

A solvable overgroup of a Sylow two-subgroup in Sp₄(2ⁿ), n > 1,
normalizes that Sylow. Odd elements of its normalizer have order dividing
(2ⁿ−1)². In an automorphism subgroup containing the inner group, the
outer quotient has order dividing 2n. Applying these facts to the actual
permuting abelian and cyclic Cartan witness bounds its exponent by n.
Faithful descent through a perfect central quotient preserves this bound.

Source: Aschbacher--Smith 7.3.4 and A.3.15, printed pp.699 and 50--51,
refs/quasithin.pdf. NonFFSourceDoubledSymplecticCartan applies the bound
to the original normalizer action on L/O₂(L).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open ChapterE.Section06.FixedPointBounds
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem symplectic_solvable_sylow_control {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n) : SolvableSylowControl 2 (Sp F) := by
  have hfour : 2 < Nat.card F := by
    rw [hF]
    exact (show 2^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
  intro S A hsol hSA
  exact solvable_overgroups_of_orthogonal_root_orbits hF hn
    (fun B hs hu => solvable_unipotent_point_orbit_orthogonal hfour B hs hu) S A hsol hSA

omit [CharP F 2] in
private theorem symplectic_odd_normalizer_order_dvd {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 ≤ n)
    (Q : Sylow 2 (Sp F)) (b : Sp F) (hb : b ∈ normalizer (Q : Set (Sp F)))
    (ho : Odd (orderOf b)) : orderOf b ∣ (2^n-1)^2 := by
  have hd := orderOf_dvd_natCard (⟨b,hb⟩ : normalizer (Q : Set (Sp F)))
  rw [Subgroup.orderOf_mk,
    Nat.card_congr (EvenBorelTorus.sylowNormalizerEquiv hF hn Q).toEquiv,
    card_borel,hF,←pow_mul] at hd
  exact (ho.coprime_two_right.pow_right (n*4)).dvd_of_dvd_mul_left hd

theorem doubledSymplectic_automorphism_nPrime_le {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n)
    (A : Subgroup (MulAut (Sp F))) (hA : MulAut.innerSubgroup (Sp F) ≤ A) :
    nPrime A ≤ n := by
  let I := MulAut.innerSubgroup (Sp F)
  let K := I.subgroupOf A
  let : K.Normal := inferInstance
  have hi : Function.Injective (MulAut.conj : Sp F →* MulAut (Sp F)) :=
    Theory.GroupTheory.conj_injective_of_center_eq_bot (EvenProjective.center_eq_bot (F := F))
  let e : K ≃* Sp F := (subgroupOfEquivOfLe hA).trans (MonoidHom.ofInjective hi).symm
  have hc : SolvableSylowControl 2 K :=
    SolvableSylowControl.of_equiv e (symplectic_solvable_sylow_control hF hn)
  have hfour : 2 < Nat.card F := by
    rw [hF]
    exact (show 2^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
  have hindex : K.index ∣ 2*n :=
    (I.relIndex_dvd_index_of_normal A).trans
      (card_outer_dvd_two_mul hF hfour SemilinearClassification.inner_field_of_preservesDiagram)
  have hexp (Q : Sylow 2 K) (b : K) (hb : b ∈ normalizer (Q : Set K))
      (ho : Odd (orderOf b)) : b ^ ((2^n-1)^2) = 1 := by
    let S := Q.mapSurjective (f := e.toMonoidHom) e.surjective
    have hmem : e b ∈ normalizer (S : Set (Sp F)) :=
      (Q : Subgroup K).le_normalizer_map e.toMonoidHom (mem_map_of_mem _ hb)
    have hd := symplectic_odd_normalizer_order_dvd hF hn.le S (e b) hmem
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
  exact Theory.NumberTheory.binary_mersenne_exponent_le_of_torus_power_dvd
    (by omega) (ho'.coprime_two_right.dvd_of_dvd_mul_left (by simpa only [mul_assoc] using hd))

theorem doubledSymplectic_centralCover_nPrime_le
    {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (X ⧸ center X) ≃* Sp F)
    (A : Subgroup (MulAut X)) (hA : MulAut.innerSubgroup X ≤ A) : nPrime A ≤ n := by
  let f := MulAut.centralQuotientAction e
  have hf : Function.Injective f := MulAut.centralQuotientAction_injective e
  have hinner : MulAut.innerSubgroup (Sp F) ≤ A.map f := by
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
      (doubledSymplectic_automorphism_nPrime_le hF hn _ hinner)

end CFSG.Quasithin.Chapter7.NormalizedSource
