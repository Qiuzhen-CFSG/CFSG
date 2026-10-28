module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.Normalizer.Permutation
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import FeitThompson.FinalTheorem

/-!
# Odd affine fixed sets in the trivial-circle branch

A normal two-complement makes the group solvable. In a faithful doubly
transitive action, a solvable group has a regular normal elementary abelian
subgroup. Cyclic Sylow two-subgroups exclude a binary regular subgroup in
degree at least three, so that regular subgroup has odd order. Each nonempty
subgroup fixed set is then in bijection with a subgroup of the regular group,
and consequently has odd cardinality.

Source: GLS IV, Chapter 2, Lemma 16.7, the case N(W)°=1.
-/

noncomputable section
namespace BenderSuzuki.ZD.Section16.NativeSource
open Subgroup PFAppendixIII PFchapter1section1 MulAction
variable {H Ω : Type*} [Group H] [Finite H] [MulAction H Ω] [Finite Ω]

/-- The normal-complement input of 16.6(e) implies solvability. -/
public theorem solvable_of_normal_two_complement (hc : HasNormalPComplement 2 H) :
    Group.IsSolvable H := by
  obtain ⟨K, hK, hkodd, hquot⟩ := hc
  let : K.Normal := hK
  let : Group.IsSolvable K := odd_order_theorem K (Nat.coprime_two_left.mp hkodd)
  let : Group.IsNilpotent (H ⧸ K) := hquot.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient K).mpr ⟨inferInstance, inferInstance⟩

/-- Cyclic Sylow subgroups pass to every surjective image. -/
public theorem cyclic_sylow_two_of_surjective {D : Type*} [Group D]
    (f : H →* D) (hf : Function.Surjective f)
    (hc : ∀ S : Sylow 2 H, IsCyclic S) (S : Sylow 2 D) : IsCyclic S := by
  obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective (f := f) hf 2 S
  let : IsCyclic P := hc P
  exact isCyclic_of_surjective (f.subgroupMap (P : Subgroup H))
    (f.subgroupMap_surjective _)

/-- The affine regular subgroup has odd order under the source cyclic-Sylow input. -/
public theorem exists_odd_regular_normal [FaithfulSMul H Ω]
    (htwo : IsMultiplyPretransitive H Ω 2) (hthree : 3 ≤ Nat.card Ω)
    (hsolv : Group.IsSolvable H) (hcyc : ∀ S : Sylow 2 H, IsCyclic S) :
    ∃ A : Subgroup H, A.Normal ∧ Odd (Nat.card A) ∧ IsMulCommutative A ∧
      IsPretransitive A Ω ∧ (∀ a : Ω, stabilizer A a = ⊥) := by
  let : Group.IsSolvable H := hsolv
  let : Nonempty Ω := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card Ω)).1
  let : IsMultiplyPretransitive H Ω 2 := htwo
  let : IsPretransitive H Ω := isPretransitive_of_is_two_pretransitive
  have hne : (⊤ : Subgroup H) ≠ ⊥ := by
    intro hb
    have hsub : Subsingleton H := by
      refine ⟨fun a b => ?_⟩
      have hall (x : H) : x = 1 := mem_bot.mp (hb ▸ mem_top x)
      rw [hall a, hall b]
    let : Subsingleton H := hsub
    have hΩ : Subsingleton Ω := ⟨fun a b => by
      obtain ⟨g, hg⟩ := exists_smul_eq H a b
      simpa only [Subsingleton.elim g 1, one_smul] using hg⟩
    let : Subsingleton Ω := hΩ
    have := Nat.card_unique (α := Ω)
    omega
  obtain ⟨A, p, hn, hp, helem, _, htrans, hreg⟩ :=
    exists_regular_elementaryAbelian_normal_of_solvable_normal htwo
      (⊤ : Subgroup H) inferInstance hne inferInstance
  let : IsElementaryAbelian p A := helem
  have hcard : Nat.card A = Nat.card Ω :=
    natCard_eq_of_pretransitive_stabilizer_bot htrans hreg (Classical.choice inferInstance)
  have hpne : p ≠ 2 := by
    intro he
    subst p
    obtain ⟨S, hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
    let : IsCyclic S := hcyc S
    let : IsCyclic A := isCyclic_of_le hAS
    have hd : Nat.card A ∣ 2 := by
      rw [← IsCyclic.exponent_eq_card]
      exact IsElementaryAbelian.exponent_dvd_p 2 A
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  have hodd : Odd (Nat.card A) := by
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [hn]
    exact (hp.odd_of_ne_two hpne).pow
  exact ⟨A, hn, hodd, inferInstance, htrans, hreg⟩

omit [Finite H] [Finite Ω] in
/-- Fixed sets in an odd regular normal action are odd when nonempty. -/
public theorem odd_fixed_card_of_odd_regular_normal
    (A : Subgroup H) [A.Normal] (hodd : Odd (Nat.card A))
    (htrans : IsPretransitive A Ω) (hreg : ∀ a : Ω, stabilizer A a = ⊥)
    (P : Subgroup H) (a : Ω) (ha : a ∈ fixedPointsOfSubgroup H Ω P) :
    Odd (Nat.card {x : Ω // x ∈ fixedPointsOfSubgroup H Ω P}) := by
  let C : Subgroup A := (centralizer (P : Set H)).comap A.subtype
  have hinj : Function.Injective (fun x : A => (x : H) • a) := by
    intro x y hxy
    have hmem : y⁻¹ * x ∈ stabilizer A a := by
      change ((y : H)⁻¹ * (x : H)) • a = a
      rw [mul_smul, inv_smul_eq_iff]
      exact hxy
    rw [hreg a, mem_bot] at hmem
    exact (inv_mul_eq_one.mp hmem).symm
  let f : C → {x : Ω // x ∈ fixedPointsOfSubgroup H Ω P} := fun x =>
    ⟨((x : A) : H) • a, fun p hp => by
      have hc : p * ((x : A) : H) = ((x : A) : H) * p :=
        mem_centralizer_iff.mp x.property p hp
      rw [← mul_smul, hc, mul_smul, ha p hp]⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact hinj (congrArg Subtype.val hxy)
    · intro b
      obtain ⟨x, hx⟩ := htrans.exists_smul_eq a b.val
      change (x : H) • a = b.val at hx
      have hxC : x ∈ C := by
        rw [mem_comap, mem_centralizer_iff]
        intro p hp
        have hxp : p * (x : H) * p⁻¹ ∈ A := (inferInstance : A.Normal).conj_mem _ x.property p
        have he : (⟨p * (x : H) * p⁻¹, hxp⟩ : A) = x := by
          apply hinj
          change (p * (x : H) * p⁻¹) • a = (x : H) • a
          rw [mul_smul, mul_smul, ha p⁻¹ (P.inv_mem hp), hx, b.property p hp]
        have hc := congrArg Subtype.val he
        exact mul_inv_eq_iff_eq_mul.mp hc
      exact ⟨⟨x, hxC⟩, Subtype.ext hx⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  exact hodd.of_dvd_nat C.card_subgroup_dvd_card

/-- The preceding affine obstruction on the original, possibly nonfaithful,
action. The fixed set is retained through the literal permutation kernel. -/
public theorem odd_fixed_card_of_normal_two_complement
    (htwo : IsMultiplyPretransitive H Ω 2) (hthree : 3 ≤ Nat.card Ω)
    (hcomp : HasNormalPComplement 2 H) (hcyc : ∀ S : Sylow 2 H, IsCyclic S)
    (P : Subgroup H) (a : Ω) (ha : a ∈ fixedPointsOfSubgroup H Ω P) :
    Odd (Nat.card {x : Ω // x ∈ fixedPointsOfSubgroup H Ω P}) := by
  let K := pointStabilizerCore H Ω
  let : K.Normal := pointStabilizerCore_normal
  let : MulAction (H ⧸ K) Ω := pointStabilizerCoreQuotientAction
  let : FaithfulSMul (H ⧸ K) Ω := faithfulSMul_pointStabilizerCoreQuotientAction
  let q := QuotientGroup.mk' K
  let : Group.IsSolvable H := solvable_of_normal_two_complement hcomp
  have hsolv : Group.IsSolvable (H ⧸ K) := inferInstance
  have hcyc' : ∀ S : Sylow 2 (H ⧸ K), IsCyclic S :=
    cyclic_sylow_two_of_surjective q (QuotientGroup.mk'_surjective K) hcyc
  obtain ⟨A, hn, hodd, _, htrans, hreg⟩ := exists_odd_regular_normal
    (pointStabilizerCoreQuotientAction_twoPretransitive htwo) hthree hsolv hcyc'
  let : A.Normal := hn
  have hfixed : fixedPointsOfSubgroup (H ⧸ K) Ω (P.map q) =
      fixedPointsOfSubgroup H Ω P := by
    ext x
    constructor
    · intro hx p hp
      exact (pointStabilizerCoreQuotientAction_mk_smul p x).symm.trans
        (hx (q p) (mem_map_of_mem q hp))
    · intro hx p hp
      obtain ⟨p, hp, rfl⟩ := hp
      exact (pointStabilizerCoreQuotientAction_mk_smul p x).trans (hx p hp)
  have hh := odd_fixed_card_of_odd_regular_normal A hodd htrans hreg
    (P.map q) a (hfixed.symm ▸ ha)
  rwa [hfixed] at hh

end BenderSuzuki.ZD.Section16.NativeSource
