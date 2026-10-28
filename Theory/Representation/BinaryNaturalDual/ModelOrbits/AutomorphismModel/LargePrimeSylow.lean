module
public import Theory.SpecificGroups.BinaryLinear.ThreeFreeSylowOvergroups
public import Theory.Representation.BinaryNaturalDual.ModelOrbits.AutomorphismModel.Structure
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.SubgroupProductCard
public import Theory.GroupTheory.PResidual.SubnormalSupplement

/-!
# Large-prime subgroups permuting with a model Sylow

In the degree-four and degree-five full binary automorphism groups, a subgroup
of order prime to three containing a Sylow two-subgroup equals that Sylow.
Intersect with the actual inner subgroup, use binary flag geometry there,
and then use the index-two quotient. If a p-subgroup with p>3 permutes with
an actual Sylow two-subgroup, their product is a three-free subgroup, so the
p-subgroup is trivial.

This is the finite model calculation used in Aschbacher--Smith, combined
manuscript of 1 March 2004, 12.1.9, printed pp.793--794. The supplied Sylow is
arbitrary; no invariance assumption on a torus or its subgroup is used.
-/

public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic
open scoped Pointwise
namespace BinaryNaturalDual.ModelOrbits.AutomorphismModel
variable {n : ℕ}

/-- In the degree four and five automorphism models, a three-free overgroup
of an actual Sylow two-subgroup equals that Sylow subgroup. -/
theorem eq_sylow_of_three_free (hn : n = 4 ∨ n = 5)
    (S : Sylow 2 (MulAut (LinearGroup n)))
    (H : Subgroup (MulAut (LinearGroup n)))
    (hSH : (S : Subgroup _) ≤ H) (h3 : ¬3 ∣ Nat.card H) : H = (S : Subgroup _) := by
  let : Finite (LinearGroup n) := Finite.of_injective
    (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective
  let I := MulAut.innerSubgroup (LinearGroup n)
  let J := H.subgroupOf I
  obtain ⟨R, hR⟩ := S.exists_subgroupOf_eq_of_normal I
  let e := innerEquiv (show 0 < n by omega)
  let R₀ := R.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let K := J.map e.symm.toMonoidHom
  have hRK : (R₀ : Subgroup (LinearGroup n)) ≤ K := by
    apply Subgroup.map_mono
    rw [hR]
    exact subgroupOf_mono I hSH
  have hcard : Nat.card K = Nat.card J :=
    (Nat.card_congr (J.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).toEquiv).symm
  have hJcard : Nat.card J = Nat.card (H ⊓ I : Subgroup _) := by
    change Nat.card (H.subgroupOf I) = _
    rw [← inf_subgroupOf_right H I]
    exact Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : H ⊓ I ≤ I)).toEquiv
  have hK3 : ¬3 ∣ Nat.card K := by
    rw [hcard, hJcard]
    exact fun hd => h3 (hd.trans (card_dvd_of_le inf_le_left))
  have hK : K = (R₀ : Subgroup (LinearGroup n)) := by
    cases n with
    | zero => omega
    | succ m => exact BinaryLinear.ThreeFreeSylowOvergroups.eq_sylow_of_three_free R₀ K hRK hK3
  have hK2 : IsPGroup 2 K := by rw [hK]; exact R₀.isPGroup'
  have hJ2 : IsPGroup 2 J := hK2.of_injective
    (J.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).toMonoidHom
    (J.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).injective
  have hH2 : IsPGroup 2 H := by
    intro x
    have hxI : (x : MulAut (LinearGroup n)) ^ 2 ∈ I :=
      I.sq_mem_of_index_two (inner_index hn) x
    let y : J := ⟨⟨x.val ^ 2, hxI⟩, H.pow_mem x.property 2⟩
    obtain ⟨k, hk⟩ := hJ2 y
    refine ⟨k + 1, ?_⟩
    apply Subtype.ext
    have he := congrArg (fun z : J => ((z : I) : MulAut (LinearGroup n))) hk
    change (x.val ^ 2) ^ (2 ^ k) = 1 at he
    change x.val ^ (2 ^ (k + 1)) = 1
    rw [← pow_mul, show 2 * 2 ^ k = 2 ^ (k + 1) by rw [pow_succ]; omega] at he
    exact he
  exact S.3 hH2 hSH

private theorem three_free_product {A : Type*} [Group A] [Finite A]
    (Y S : Subgroup A) (hY : ¬3 ∣ Nat.card Y) (hS : ¬3 ∣ Nat.card S)
    (hperm : (Y : Set A) * (S : Set A) = (S : Set A) * (Y : Set A)) :
    ¬3 ∣ Nat.card (Y ⊔ S : Subgroup A) := by
  intro hd
  have hc := card_set_mul_mul_card_inf Y S
  rw [← coe_sup_of_set_mul_comm Y S hperm] at hc
  change Nat.card (Y ⊔ S : Subgroup A) * Nat.card (Y ⊓ S : Subgroup A) =
    Nat.card Y * Nat.card S at hc
  have hprod := dvd_mul_of_dvd_left hd (Nat.card (Y ⊓ S : Subgroup A))
  rw [hc] at hprod
  exact (Nat.prime_three.dvd_mul.mp hprod).elim hY hS

/-- The literal permutability condition excludes every p-subgroup with p>3. -/
theorem permutable_prime_eq_bot (hn : n = 4 ∨ n = 5)
    (S : Sylow 2 (MulAut (LinearGroup n))) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p)
    (Y : Subgroup (MulAut (LinearGroup n))) (hY : IsPGroup p Y)
    (hperm : (Y : Set (MulAut (LinearGroup n))) * (S : Set (MulAut (LinearGroup n))) =
      (S : Set (MulAut (LinearGroup n))) * (Y : Set (MulAut (LinearGroup n)))) : Y = ⊥ := by
  let : Finite (LinearGroup n) := Finite.of_injective
    (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective
  let : Fact p.Prime := ⟨hp⟩
  let H := Y ⊔ (S : Subgroup _)
  have h3 : ¬3 ∣ Nat.card H := by
    apply three_free_product Y (S : Subgroup _) _ _ hperm
    · intro hy
      obtain ⟨k, hk⟩ := hY.exists_card_eq
      rw [hk] at hy
      have hd := Nat.prime_three.dvd_of_dvd_pow hy
      have he : 3 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hd
      omega
    · intro hs
      obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
      rw [hk] at hs
      exact (by decide : ¬3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hs)
  have hH := eq_sylow_of_three_free hn S H le_sup_right h3
  have hYS : Y ≤ (S : Subgroup _) := le_sup_left.trans_eq hH
  have hcop : Nat.Coprime p 2 := hp.coprime_iff_not_dvd.mpr (by
    intro hd
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega)
  apply eq_bot_iff.mpr
  intro y hy
  exact disjoint_def.mp (hY.disjoint_of_coprime S.isPGroup' hcop) hy (hYS hy)

end BinaryNaturalDual.ModelOrbits.AutomorphismModel
