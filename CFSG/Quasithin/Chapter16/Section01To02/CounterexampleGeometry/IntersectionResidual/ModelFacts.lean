module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.IntersectionResidual.Reduction
public import BenderSuzuki.Converse.PSL2
public import BenderSuzuki.External.Huppert.XI.theorem_3_6
public import Theory.SpecificGroups.Suzuki.StandardSubgroups
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Mathlib.Algebra.CharP.CharAndCard
public import Theory.Quasithin.Rank

/-!
# Local primes and centers for the models in Lemmas 16.2.8–9

The split torus normalizes a nontrivial root two-group in the even linear
and Suzuki models, so every prime divisor of q − 1 occurs in a two-local.
Simplicity and perfectness give the trivial centers used for tight embedding.
For quasisimple covers, a center-free quotient by O₂ identifies O₂ with the
center, justifying passage to the exact central quotient in A.1.34.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemmas 16.2.8–9, printed p.1175; the concrete Suzuki
subgroups are from Huppert–Blackburn, *Finite Groups III*, XI.3.1–6.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry

variable {X Y : Type*} [Group X] [Group Y]

theorem IsOddLocalPrime.of_mulEquiv {p : ℕ} (hp : IsOddLocalPrime p X) (e : X ≃* Y) :
    IsOddLocalPrime p Y := by
  obtain ⟨hp, ho, M, hl, hd⟩ := hp
  refine ⟨hp, ho, M.map e.toMonoidHom, hl.map_equiv e, ?_⟩
  rwa [card_map_of_injective e.injective]

private theorem center_eq_bot_of_simple_perfect [IsSimpleGroup X] [Group.IsPerfect X] :
    center X = ⊥ := by
  rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative X (center_eq_top_iff.mp h)).elim

private theorem center_eq_bot_of_equiv (e : X ≃* Y) (hy : center Y = ⊥) :
    center X = ⊥ := by
  apply card_eq_one.mp
  rw [Nat.card_congr (centerCongr e).toEquiv, hy]
  simp

private theorem center_eq_bot_of_nonsolvable_simple [IsSimpleGroup X]
    (h : ¬ Group.IsSolvable X) : center X = ⊥ := by
  rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with he | he
  · exact he
  · let : IsMulCommutative X := center_eq_top_iff.mp he
    exact (h (Group.isSolvable_of_comm (fun a b => mem_center_iff.mp (he ▸ mem_top b) a))).elim

theorem suzuki_center_eq_bot {m : ℕ} (hm : 0 < m) :
    center (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) = ⊥ := by
  let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  exact center_eq_bot_of_nonsolvable_simple
    (BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm)

theorem center_eq_bot_of_linear_even [IsQuasisimple X] {n : ℕ} (hn : 2 ≤ n)
    (h : ClassicalGroup.IsPSL X 2 (2 ^ n)) : center X = ⊥ := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := h
  have hfour : 4 ≤ Nat.card F := by
    rw [hc]
    exact Nat.pow_le_pow_right (n := 2) (by decide) hn
  let : IsSimpleGroup X := e.isSimpleGroup_congr.mpr
    (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hfour)
  exact center_eq_bot_of_simple_perfect

theorem center_eq_bot_of_linear_odd [IsQuasisimple X] {r : ℕ} (hr : Odd r)
    (h : ClassicalGroup.IsPSL X 2 r) : center X = ⊥ := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := h
  let : Nontrivial X := e.surjective.nontrivial
  have hns : ¬ Group.IsSolvable PSL(2,F) := by
    intro hs
    let := hs
    let : Group.IsSolvable X := Group.isSolvable_of_surjective
      (f := e.symm.toMonoidHom) e.symm.surjective
    exact Group.IsPerfect.not_isSolvable X inferInstance
  have hf := Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
    (hc.symm ▸ hr) hns
  let : IsSimpleGroup X := e.isSimpleGroup_congr.mpr
    (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hf)
  exact center_eq_bot_of_simple_perfect

theorem center_eq_bot_of_suzuki {m : ℕ} (hm : 0 < m)
    (h : Nonempty (X ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) : center X = ⊥ := by
  obtain ⟨e⟩ := h
  exact center_eq_bot_of_equiv e (suzuki_center_eq_bot hm)

private theorem odd_prime_of_dvd_two_pow_sub_one {p n : ℕ} (hp : p.Prime)
    (hn : n ≠ 0) (hd : p ∣ 2 ^ n - 1) : Odd p := by
  apply hp.odd_of_ne_two
  intro he
  subst p
  have ho : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow n 2 (by decide)) (even_two.pow_of_ne_zero hn) odd_one
  exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hd)

theorem linear_even_local_prime {F : Type*} [Field F] [Finite F]
    {n p : ℕ} (hn : 2 ≤ n) (hc : Nat.card F = 2 ^ n)
    (hp : p.Prime) (hd : p ∣ 2 ^ n - 1) : IsOddLocalPrime p PSL(2,F) := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa [Nat.card_eq_fintype_card] using hc)
  let Q := BenderSuzuki.Converse.PUnip F
  let D := BenderSuzuki.Converse.PTorus F
  have hqcard : Nat.card Q = 2 ^ n := by
    rw [BenderSuzuki.Converse.PUnip_card, hc]
  have hqne : Q ≠ ⊥ := by
    intro he
    have : 2 ^ n = 1 := by simpa [he] using hqcard.symm
    have : 1 < 2 ^ n := Nat.one_lt_pow (by omega) (by decide)
    omega
  have hnQ : D ≤ normalizer (Q : Set PSL(2,F)) :=
    BenderSuzuki.Converse.PTorus_le_PBorel.trans
      ((normal_subgroupOf_iff_le_normalizer BenderSuzuki.Converse.PUnip_le_PBorel).mp
        BenderSuzuki.Converse.PUnip_normal_in_PBorel)
  refine ⟨hp, odd_prime_of_dvd_two_pow_sub_one hp (by omega) hd,
    normalizer (Q : Set PSL(2,F)), ⟨Q, hqne, IsPGroup.of_card hqcard, rfl⟩, ?_⟩
  apply dvd_trans (b := Nat.card D) _ (card_dvd_of_le hnQ)
  rwa [BenderSuzuki.Converse.PTorus_card, Nat.card_units, hc]

theorem suzuki_local_prime {m p : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hd : p ∣ 2 ^ (2 * m + 1) - 1) :
    IsOddLocalPrime p (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  open BenderSuzuki.MatrixGroups in
  have hqne : SuzukiRootSubgroup m ≠ ⊥ := by
    intro he
    have hcard := suzukiRootSubgroup_card m hm
    rw [he, Nat.card_eq_fintype_card, Fintype.card_ofSubsingleton] at hcard
    have : 1 < (2 ^ (2 * m + 1)) ^ 2 :=
      Nat.one_lt_pow (by decide) (Nat.one_lt_pow (by omega) (by decide))
    omega
  open BenderSuzuki.MatrixGroups in
  refine ⟨hp, odd_prime_of_dvd_two_pow_sub_one hp (by omega) hd,
    normalizer (SuzukiRootSubgroup m : Set _),
    ⟨SuzukiRootSubgroup m, hqne, suzukiRootSubgroup_isPGroup m hm, rfl⟩, ?_⟩
  open BenderSuzuki.MatrixGroups in
  apply dvd_trans (b := Nat.card (SuzukiSplitTorus m)) _
    (card_dvd_of_le (suzukiSplitTorus_le_normalizer_root m))
  rwa [BenderSuzuki.MatrixGroups.suzukiSplitTorus_card m hm]

private noncomputable def quotientCenterEquiv (hc : center X = ⊥) : X ⧸ center X ≃* X :=
  (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot

theorem linear_even_quotient_local_prime [IsQuasisimple X] {n p : ℕ} (hn : 2 ≤ n)
    (h : ClassicalGroup.IsPSL X 2 (2 ^ n)) (hp : p.Prime) (hd : p ∣ 2 ^ n - 1) :
    IsOddLocalPrime p (X ⧸ center X) := by
  have hc := center_eq_bot_of_linear_even hn h
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  exact (linear_even_local_prime hn hF hp hd).of_mulEquiv
    (e.symm.trans (quotientCenterEquiv hc).symm)

theorem suzuki_quotient_local_prime {m p : ℕ} (hm : 0 < m)
    (h : Nonempty (X ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
    (hp : p.Prime) (hd : p ∣ 2 ^ (2 * m + 1) - 1) :
    IsOddLocalPrime p (X ⧸ center X) := by
  have hc := center_eq_bot_of_suzuki hm h
  obtain ⟨e⟩ := h
  exact (suzuki_local_prime hm hp hd).of_mulEquiv
    (e.symm.trans (quotientCenterEquiv hc).symm)

/-- For a quasisimple group with center-free quotient by its two-core,
the two-core is exactly the center. -/
theorem twoCore_eq_center_of_quotient_center_eq_bot [Finite X] [IsQuasisimple X]
    (hc : center (X ⧸ pCore 2 X) = ⊥) : pCore 2 X = center X := by
  have hn : Nontrivial (X ⧸ center X) := IsQuasisimple.simple.toNontrivial
  let : Nontrivial X := (QuotientGroup.mk'_surjective (center X)).nontrivial
  apply le_antisymm
  · rcases IsQuasisimple.normal_le_center_or_eq_top (pCore 2 X) with h | h
    · exact h
    · have hp : IsPGroup 2 X := by
        have ht : IsPGroup 2 (⊤ : Subgroup X) := h ▸ pCore_isPGroup (p := 2) (G := X)
        exact ht.of_equiv (Subgroup.topEquiv)
      let : Group.IsNilpotent X := hp.isNilpotent
      exact (Group.IsPerfect.not_isSolvable X inferInstance).elim
  · intro x hx
    rw [← QuotientGroup.ker_mk' (pCore 2 X)]
    change QuotientGroup.mk' (pCore 2 X) x = 1
    have hmem : QuotientGroup.mk' (pCore 2 X) x ∈ center (X ⧸ pCore 2 X) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) y
      simpa only [map_mul] using congrArg (QuotientGroup.mk' (pCore 2 X))
        (mem_center_iff.mp hx y)
    simpa only [hc, mem_bot] using hmem

/-- The covered Suzuki case uses its genuine central quotient, identified
with the quotient by O₂ rather than silently interchanging those kernels. -/
theorem covered_suzuki_quotient_local_prime [Finite X] [IsQuasisimple X] {m p : ℕ}
    (hm : 0 < m)
    (h : Nonempty ((X ⧸ pCore 2 X) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
    (hp : p.Prime) (hd : p ∣ 2 ^ (2 * m + 1) - 1) :
    IsOddLocalPrime p (X ⧸ center X) := by
  have hc := twoCore_eq_center_of_quotient_center_eq_bot
    (center_eq_bot_of_suzuki hm h)
  obtain ⟨e⟩ := h
  exact (suzuki_local_prime hm hp hd).of_mulEquiv
    (e.symm.trans (QuotientGroup.quotientMulEquivOfEq hc))

/-- The characteristic-two linear quotient in the source has the same
local-prime property, even when the component is given as a cover. -/
theorem linear_even_core_quotient_local_prime [Finite X] [IsQuasisimple X] {n p : ℕ}
    (hn : 2 ≤ n) (h : ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 (2 ^ n))
    (hp : p.Prime) (hd : p ∣ 2 ^ n - 1) : IsOddLocalPrime p (X ⧸ center X) := by
  have hnontriv : Nontrivial (X ⧸ pCore 2 X) := by
    obtain ⟨F, _, _, _, ⟨e⟩⟩ := h
    exact e.surjective.nontrivial
  let : IsQuasisimple (X ⧸ pCore 2 X) :=
    IsQuasisimple.of_surjective (QuotientGroup.mk' (pCore 2 X))
      (QuotientGroup.mk'_surjective _)
  have hc := twoCore_eq_center_of_quotient_center_eq_bot
    (center_eq_bot_of_linear_even hn h)
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  exact (linear_even_local_prime hn hF hp hd).of_mulEquiv
    (e.symm.trans (QuotientGroup.quotientMulEquivOfEq hc))

end CFSG.Quasithin.Chapter16.CounterexampleGeometry

end
