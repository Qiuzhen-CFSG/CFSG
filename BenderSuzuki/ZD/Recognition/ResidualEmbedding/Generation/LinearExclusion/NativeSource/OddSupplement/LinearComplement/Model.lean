module

public import Glauberman.DicksonSylowNormalizer
public import Mathlib.GroupTheory.SchurZassenhaus

/-!
# The cyclic complement of a normal Sylow subgroup in binary PSL₂

The proved Borel normalizer calculation gives a cyclic quotient of order
dividing q−1 and a free action outside the normal Sylow subgroup. Applying
Schur–Zassenhaus produces an odd cyclic complement. A normalizer of a
nontrivial subgroup of that complement has trivial Sylow component: quotient
injectivity makes it centralize that subgroup, and freeness kills it.

This supplies the intrinsic model step used before GLS IV, Chapter 2,
Lemma 15.5. The source input is Huppert II.8.21, not a general subgroup
classification.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion.LinearComplement
open Subgroup
universe u

private theorem normalizer_eq_complement {H : Type*} [Group H]
    (U C : Subgroup H) [U.Normal] [IsMulCommutative C]
    (hcomp : U.IsComplement' C)
    (hfree : ∀ g : H, g ∉ U → ∀ x : U, x ≠ 1 → g * x * g⁻¹ ≠ x)
    (P : Subgroup H) (hPC : P ≤ C) (hPne : P ≠ ⊥) : normalizer (P : Set H) = C := by
  have hCN : C ≤ normalizer (P : Set H) :=
    (le_centralizer_iff.mpr (fun p hp => C.le_centralizer (hPC hp))).trans
      (Subgroup.centralizer_le_normalizer _)
  apply le_antisymm ?_ hCN
  intro g hg
  obtain ⟨⟨u, c⟩, huc⟩ := hcomp.surjective g
  change (u : H) * (c : H) = g at huc
  have huN : (u : H) ∈ normalizer (P : Set H) := by
    have hh := (normalizer (P : Set H)).mul_mem hg
      ((normalizer (P : Set H)).inv_mem (hCN c.property))
    simpa only [← huc, mul_inv_cancel_right] using hh
  obtain ⟨p, hpne0⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  have hp : (p : H) ∈ P := p.property
  have hpne : (p : H) ≠ 1 := fun hh => hpne0 (Subtype.ext hh)
  let q := QuotientGroup.mk' U
  let f : C →* H ⧸ U := q.comp C.subtype
  have hf : Function.Injective f := (injective_iff_map_eq_one f).mpr (by
    intro x hx
    apply Subtype.ext
    exact disjoint_def.mp hcomp.disjoint ((QuotientGroup.eq_one_iff x.val).mp hx) x.property)
  have hconjP : (u : H) * p * (u : H)⁻¹ ∈ P := (mem_normalizer_iff.mp huN p).mp hp
  have hup : (u : H) * p * (u : H)⁻¹ = p := by
    have hh : (⟨(u : H) * p * (u : H)⁻¹, hPC hconjP⟩ : C) = ⟨p, hPC hp⟩ := by
      apply hf
      change q ((u : H) * p * (u : H)⁻¹) = q p
      have huq : q (u : H) = 1 := (QuotientGroup.eq_one_iff (u : H)).mpr u.property
      rw [map_mul, map_mul, map_inv, huq]
      simp only [inv_one, one_mul, mul_one]
    exact congrArg Subtype.val hh
  have hpu : Commute (p : H) (u : H) := (mul_inv_eq_iff_eq_mul.mp hup).symm
  have hpU : (p : H) ∉ U := fun hh => hpne (disjoint_def.mp hcomp.disjoint hh (hPC hp))
  have hu1 : u = 1 := by
    by_contra hune
    apply hfree p hpU u hune
    rw [hpu.eq, mul_inv_cancel_right]
  rw [← huc, hu1, coe_one, one_mul]
  exact c.property

/-- A normal nontrivial Sylow subgroup in the concrete model has an odd
cyclic complement with the exact normalizers required in source 15.5. -/
public theorem exists_complement_of_normal_sylow
    {F : Type u} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 0 < n)
    (H : Subgroup (MatrixGroups.PSL2MatrixGroup F))
    (P : Sylow 2 H) [(P : Subgroup H).Normal] (hPne : (P : Subgroup H) ≠ ⊥) :
    ∃ C : Subgroup H, (P : Subgroup H).IsComplement' C ∧
      Odd (Nat.card C) ∧ IsCyclic C ∧ Nat.card C ∣ 2 ^ n - 1 ∧
      ∀ Q : Subgroup H, Q ≤ C → Q ≠ ⊥ → normalizer (Q : Set H) = C := by
  let N : Subgroup H := ⊤
  let PN := (P : Subgroup H).subgroupOf N
  let : PN.Normal := normal_subgroupOf_of_le_normalizer
    (show N ≤ normalizer ((P : Subgroup H) : Set H) from
      (P : Subgroup H).normalizer_eq_top.symm ▸ le_top)
  obtain ⟨hcyc, hdiv, hfree, _⟩ := Glauberman.Dickson.h821_borel_quotient_data
    hF H P hPne N (P : Subgroup H).normalizer_eq_top.symm PN rfl
  let e : N ≃* H := topEquiv
  have hmap : PN.map e.toMonoidHom = (P : Subgroup H) :=
    map_subgroupOf_eq_of_le le_top
  let eqv : (N ⧸ PN) ≃* H ⧸ (P : Subgroup H) := QuotientGroup.congr PN (P : Subgroup H) e hmap
  let : IsCyclic (N ⧸ PN) := hcyc
  let : IsCyclic (H ⧸ (P : Subgroup H)) :=
    isCyclic_of_surjective eqv eqv.surjective
  have hcard : Nat.card (H ⧸ (P : Subgroup H)) = Nat.card (N ⧸ PN) :=
    (Nat.card_congr eqv.toEquiv).symm
  have hdivq : (P : Subgroup H).index ∣ 2 ^ n - 1 := by
    rw [index_eq_card, hcard, ← hF]
    exact hdiv.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
  have hodd : Odd (2 ^ n - 1) := Nat.Even.sub_odd Nat.one_le_two_pow
    (even_two.pow_of_ne_zero hn.ne') odd_one
  have hindexodd : Odd (P : Subgroup H).index := hodd.of_dvd_nat hdivq
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have hcop : Nat.Coprime (Nat.card P) (P : Subgroup H).index := by
    rw [hk]
    exact hindexodd.coprime_two_left.pow_left k
  obtain ⟨C, hC⟩ := exists_right_complement'_of_coprime hcop
  have hc : Nat.card C = (P : Subgroup H).index := hC.symm.index_eq_card.symm
  let eC : C ≃* H ⧸ (P : Subgroup H) := hC.symm.QuotientMulEquiv.symm
  let : IsCyclic C := isCyclic_of_injective eC.toMonoidHom eC.injective
  refine ⟨C, hC, hc ▸ hindexodd, inferInstance, hc ▸ hdivq, ?_⟩
  intro Q hQC hQne
  apply normalizer_eq_complement P C hC ?_ Q hQC hQne
  intro g hg x hx
  exact hfree ⟨g, mem_top g⟩ hg x hx

end BenderSuzuki.ZD.LinearExclusion.LinearComplement
