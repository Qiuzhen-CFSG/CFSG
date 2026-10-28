module

public import Theory.GroupAction.SylowFixedInvolutionOddCore

/-!
# Odd cores for Sylow fixers in rank-one groups

Assume a centerless group has Sylow-inner pointwise fixers and that every
proper overgroup of a Sylow two-subgroup normalizes it. An inner involution
fixing that Sylow has a proper centralizer containing the Sylow. The Sylow
is therefore normal and self-centralizing in the centralizer, whose odd
core vanishes. The faithful automorphism-overgroup transfer retains the
original acting group and its specified order-two subgroup.

Source: the rank-one model inspection in Aschbacher–Smith E.6.19,
printed p.252, using the concrete Sylow geometry of F.1.3(1).
-/

public section
open Subgroup
namespace Theory.GroupAction
variable {X H : Type*} [Group X] [Group H]

/-- A finite p-group has trivial p'-core. -/
theorem pPrimeCore_eq_bot_of_isPGroup [Finite X] {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p X) : pPrimeCore p X = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  let y : pPrimeCore p X := ⟨x,hx⟩
  have hy : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes
    ((hp.of_injective (pPrimeCore p X).subtype
      (pPrimeCore p X).subtype_injective).orderOf_coprime pPrimeCore_coprime_card y)
    dvd_rfl (orderOf_dvd_natCard y)
  exact mem_bot.mpr (congrArg Subtype.val (orderOf_eq_one_iff.mp hy))

/-- Pointwise Sylow innerness and unique proper Sylow overgroups eliminate
odd cores in the actual faithful automorphism overgroup. -/
theorem SylowFixedInvolution.oddCore_eq_bot_of_sylow_overgroups
    [Finite X] [Finite H] {φ : H →* MulAut X} {E : Subgroup H}
    (d : SylowFixedInvolution φ E) (hc : center X = ⊥)
    (hinner : ∀ (S : Sylow 2 X) (a : MulAut X),
      (∀ x ∈ (S : Subgroup X), a x = x) →
      ∃ g ∈ (S : Subgroup X), a = MulAut.conj g)
    (hmax : ∀ (S : Sylow 2 X) (M : Subgroup X),
      (S : Subgroup X) ≤ M → M < ⊤ → M ≤ normalizer (S : Set X)) :
    pPrimeCore 2 (centralizer (E : Set H)) = ⊥ := by
  apply d.oddCore_eq_bot_of_inner hc hinner
  intro S z hz hfix
  let C := centralizer ({z} : Set X)
  have hSC : (S : Subgroup X) ≤ C := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp (hfix x hx)).symm
  have hC : C < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro ht
    have hzc : z ∈ center X := centralizer_eq_top_iff_subset.mp ht (Set.mem_singleton z)
    rw [hc, mem_bot] at hzc
    simp [hzc] at hz
  let P := (S : Subgroup X).subgroupOf C
  let : P.Normal := (normal_subgroupOf_iff_le_normalizer hSC).mpr (hmax S C hSC hC)
  apply Theory.GroupTheory.pPrimeCore_eq_bot_of_selfCentralizing P
    (pPrimeCore_eq_bot_of_isPGroup S.isPGroup'.comap_subtype)
  intro x hx
  have hxf : ∀ y ∈ (S : Subgroup X), MulAut.conj (x : X) y = y := by
    intro y hy
    have he := congrArg Subtype.val (hx ⟨y,hSC hy⟩ hy)
    exact mul_inv_eq_iff_eq_mul.mpr he.symm
  obtain ⟨g,hg,he⟩ := hinner S (MulAut.conj (x : X)) hxf
  have hxg : (x : X) = g := MulAut.conj_injective_of_center_eq_bot hc he
  change (x : X) ∈ (S : Subgroup X)
  rwa [hxg]

end Theory.GroupAction
