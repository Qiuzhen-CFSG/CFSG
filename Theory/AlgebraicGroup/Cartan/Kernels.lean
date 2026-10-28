module

public import Theory.AlgebraicGroup.RootSystems.Dynkin

/-! Multiplicative kernels of standard Cartan equations. -/

namespace Theory.AlgebraicGroup

/-- The multiplicative kernel of the tridiagonal Cartan equations of type `A`.

For a chain indexed by `0, ..., m`, the boundary terms outside the chain are
understood to be one.  Thus the first and last equations are respectively
`t 0 ^ 2 = t 1` and `t m ^ 2 = t (m - 1)` when the chain has more than one
node. -/
private lemma typeAChainCartanKernel
    {G : Type*} [CommGroup G] (m : ℕ) (t : ℕ → G)
    (h : ∀ i, i ≤ m →
      t i ^ 2 = (if i = 0 then 1 else t (i - 1)) *
        (if i = m then 1 else t (i + 1))) :
    ∃ ω : G, ω ^ (m + 2) = 1 ∧ ∀ i, i ≤ m → t i = ω ^ (i + 1) := by
  let ω := t 0
  have ht : ∀ i, i ≤ m → t i = ω ^ (i + 1) := by
    intro i
    induction i using Nat.twoStepInduction with
    | zero =>
        intro _
        simp [ω]
    | one =>
        intro hi
        have hm : m ≠ 0 := by omega
        have h0 := h 0 (Nat.zero_le m)
        simp [hm.symm] at h0
        simpa [ω, pow_two] using h0.symm
    | more i hi hi1 =>
        intro hi2
        have him : i + 1 ≠ m := by omega
        have hrec := h (i + 1) (by omega)
        simp [him] at hrec
        rw [hi (by omega), hi1 (by omega)] at hrec
        calc
          t (i + 2) = (ω ^ (i + 1))⁻¹ * (ω ^ (i + 2)) ^ 2 := by
            rw [hrec]
            simp
          _ = ω ^ (i + 3) := by group
  refine ⟨ω, ?_, ht⟩
  by_cases hm : m = 0
  · subst m
    have h0 := h 0 (by simp)
    simpa [ω] using h0
  · have hlast := h m le_rfl
    simp [hm] at hlast
    rw [ht m le_rfl, ht (m - 1) (Nat.sub_le m 1)] at hlast
    have hmpred : m - 1 + 1 = m :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)
    rw [hmpred] at hlast
    have hcancel : ω ^ m * ω ^ (m + 2) = ω ^ m := by
      calc
        ω ^ m * ω ^ (m + 2) = (ω ^ (m + 1)) ^ 2 := by group
        _ = ω ^ m := hlast
    apply mul_left_cancel (a := ω ^ m)
    simpa using hcancel

/-- The multiplicative kernel of the rank-at-least-two type `B` chain equations.

The final double bond is represented by the terminal equation
`t m ^ 2 = t (m - 1) ^ 2`; the theorem keeps this endpoint arithmetic
explicit and does not package any conclusion-bearing setup in a definition. -/
private lemma typeBChainCartanKernel
    {G : Type*} [CommGroup G] (m : ℕ) (t : ℕ → G)
    (hm : 1 ≤ m)
    (h : ∀ i, i ≤ m →
      t i ^ 2 = (if i = 0 then 1 else t (i - 1)) *
        (if i = m then t (m - 1) else t (i + 1))) :
    ∃ ω : G, ω ^ 2 = 1 ∧ ∀ i, i ≤ m → t i = ω ^ (i + 1) := by
  let ω := t 0
  have hm0 : m ≠ 0 := Nat.ne_of_gt hm
  have hzero : (0 : ℕ) ≠ m := by omega
  have ht : ∀ i, i ≤ m → t i = ω ^ (i + 1) := by
    intro i
    induction i using Nat.twoStepInduction with
    | zero =>
        intro _
        simp [ω]
    | one =>
        intro hi
        have h0 := h 0 (Nat.zero_le m)
        simp [hzero] at h0
        simpa [ω, pow_two] using h0.symm
    | more i hi hi1 =>
        intro hi2
        have hnotlast : i + 1 ≠ m := by omega
        have hrec := h (i + 1) (by omega)
        simp [hnotlast] at hrec
        rw [hi (by omega), hi1 (by omega)] at hrec
        calc
          t (i + 2) = (ω ^ (i + 1))⁻¹ * (ω ^ (i + 2)) ^ 2 := by
            rw [hrec]
            simp
          _ = ω ^ (i + 3) := by group
  refine ⟨ω, ?_, ht⟩
  have hlast := h m le_rfl
  simp [hm0] at hlast
  rw [ht m le_rfl, ht (m - 1) (Nat.sub_le m 1)] at hlast
  have hmpred : m - 1 + 1 = m := Nat.sub_add_cancel hm
  rw [hmpred] at hlast
  have hcancel : ω ^ (2 * m) * ω ^ 2 = ω ^ (2 * m) := by
    calc
      ω ^ (2 * m) * ω ^ 2 = (ω ^ (m + 1)) ^ 2 := by group
      _ = (ω ^ m) ^ 2 := by simpa [pow_two] using hlast
      _ = ω ^ (m * 2) := by rw [← pow_mul]
      _ = ω ^ (2 * m) := by rw [Nat.mul_comm]
  apply mul_left_cancel (a := ω ^ (2 * m))
  simpa [Nat.mul_comm] using hcancel

/-- The multiplicative kernel of the rank-at-least-two type `C` chain equations.

The penultimate and terminal equations expose the double bond explicitly.  The
regular part is the ordinary tridiagonal recurrence, and the conclusion is
proved from those equations rather than stored in a setup structure. -/
private lemma typeCChainCartanKernel
    {G : Type*} [CommGroup G] (m : ℕ) (t : ℕ → G)
    (hm : 1 ≤ m)
    (hreg : ∀ i, i + 1 < m →
      t i ^ 2 = (if i = 0 then 1 else t (i - 1)) * t (i + 1))
    (hpenult : t (m - 1) ^ 2 =
      (if m = 1 then 1 else t (m - 2)) * t m ^ 2)
    (hlast : t m ^ 2 = t (m - 1)) :
    ∃ ω : G, ω ^ 2 = 1 ∧
      ∀ i, i ≤ m → t i = (if i = m then ω else 1) := by
  by_cases hm1 : m = 1
  · subst m
    have hp := hpenult
    simp at hp
    have hl := hlast
    have hzero : t 0 = 1 := by
      have heq : t 0 * t 0 = 1 * t 0 := by
        simpa [pow_two] using hp.trans hl
      exact mul_right_cancel heq
    refine ⟨t 1, ?_, ?_⟩
    · simpa [hzero] using hl
    · intro i hi
      have hi' : i = 0 ∨ i = 1 := by omega
      rcases hi' with rfl | rfl
      · simp [hzero]
      · simp
  · have hm2 : 2 ≤ m := by omega
    let ω := t 0
    have ht : ∀ i, i ≤ m - 1 → t i = ω ^ (i + 1) := by
      intro i
      induction i using Nat.twoStepInduction with
      | zero =>
          intro _
          simp [ω]
      | one =>
          intro hi
          have h0 := hreg 0 (by omega)
          simp at h0
          simpa [ω, pow_two] using h0.symm
      | more i hi hi1 =>
          intro hi2
          have hrec := hreg (i + 1) (by omega)
          simp at hrec
          rw [hi (by omega), hi1 (by omega)] at hrec
          calc
            t (i + 2) = (ω ^ (i + 1))⁻¹ * (ω ^ (i + 2)) ^ 2 := by
              rw [hrec]
              simp
            _ = ω ^ (i + 3) := by group
    have hmpred : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
    have htlast : t (m - 1) = ω ^ m := by
      calc
        t (m - 1) = ω ^ (m - 1 + 1) := ht (m - 1) (by omega)
        _ = ω ^ m := by rw [hmpred]
    have hlast' : t m ^ 2 = ω ^ m := by
      calc
        t m ^ 2 = t (m - 1) := hlast
        _ = ω ^ m := htlast
    have hmne1 : m ≠ 1 := hm1
    have hmpred2 : m - 2 + 1 = m - 1 := by omega
    have hpen : (ω ^ m) ^ 2 = ω ^ (m - 1) * ω ^ m := by
      calc
        (ω ^ m) ^ 2 = t (m - 1) ^ 2 := by
          rw [htlast]
        _ = (if m = 1 then 1 else t (m - 2)) * t m ^ 2 := hpenult
        _ = ω ^ (m - 1) * ω ^ m := by
          simp [hmne1]
          rw [ht (m - 2) (by omega), hlast']
          rw [hmpred2]
    have hω : ω = 1 := by
      have hratio : (ω ^ m) ^ 2 * (ω ^ (m - 1) * ω ^ m)⁻¹ = 1 := by
        rw [hpen]
        simp
      rw [← hmpred] at hratio
      calc
        ω = (ω ^ (m - 1 + 1)) ^ 2 *
            (ω ^ (m - 1) * ω ^ (m - 1 + 1))⁻¹ := by group
        _ = 1 := hratio
    refine ⟨t m, ?_, ?_⟩
    · have htlast_one : t (m - 1) = 1 := by simpa [hω] using htlast
      simpa [htlast_one] using hlast
    · intro i hi
      by_cases him : i = m
      · simp [him]
      · have hilast : i ≤ m - 1 := by omega
        rw [ht i hilast, hω]
        simp [him]

/-- The multiplicative kernel of the chain-and-fork Cartan equations of type `D`. -/
private lemma typeDForkCartanKernel
    {G : Type*} [CommGroup G] (m : ℕ) (hm : 1 ≤ m)
    (t : ℕ → G) (u v : G)
    (hchain : ∀ i, i < m →
      t i ^ 2 = (if i = 0 then 1 else t (i - 1)) * t (i + 1))
    (hbranch : t m ^ 2 = t (m - 1) * u * v)
    (hu : u ^ 2 = t m) (hv : v ^ 2 = t m) :
    ∃ ω : G, ω ^ 2 = 1 ∧
      (∀ i, i ≤ m → t i = ω ^ (i + 1)) ∧
      u ^ 2 = ω ^ (m + 1) ∧ v = ω * u := by
  let ω := t 0
  have ht : ∀ i, i ≤ m → t i = ω ^ (i + 1) := by
    intro i
    induction i using Nat.twoStepInduction with
    | zero =>
        intro _
        simp [ω]
    | one =>
        intro _
        have h0 := hchain 0 hm
        simpa [ω, pow_two] using h0.symm
    | more i hi hi1 =>
        intro hi2
        have hrec := hchain (i + 1) (by omega)
        simp at hrec
        rw [hi (by omega), hi1 (by omega)] at hrec
        calc
          t (i + 2) = (ω ^ (i + 1))⁻¹ * (ω ^ (i + 2)) ^ 2 := by
            rw [hrec]
            simp
          _ = ω ^ (i + 3) := by group
  have htm := ht m le_rfl
  have htmpred := ht (m - 1) (Nat.sub_le m 1)
  have hmpred : m - 1 + 1 = m := Nat.sub_add_cancel hm
  rw [hmpred] at htmpred
  have hprod : u * v = ω ^ (m + 2) := by
    rw [htm, htmpred] at hbranch
    calc
      u * v = (ω ^ m)⁻¹ * ((ω ^ (m + 1)) ^ 2) := by
        rw [hbranch]
        group
      _ = ω ^ (m + 2) := by group
  have hu' : u ^ 2 = ω ^ (m + 1) := by simpa [htm] using hu
  have hv' : v ^ 2 = ω ^ (m + 1) := by simpa [htm] using hv
  have hvform : v = ω * u := by
    calc
      v = u⁻¹ * (u * v) := by group
      _ = u⁻¹ * ω ^ (m + 2) := by rw [hprod]
      _ = u⁻¹ * (ω * ω ^ (m + 1)) := by group
      _ = u⁻¹ * (ω * u ^ 2) := by rw [← hu']
      _ = ω * (u⁻¹ * u) * u := by rw [pow_two]; ac_rfl
      _ = ω * u := by simp
  have hsq : (ω * u) ^ 2 = u ^ 2 := by rw [← hvform, hv', hu']
  have hcancel : ω ^ 2 * u ^ 2 = u ^ 2 := by
    simpa [mul_pow] using hsq
  have hω : ω ^ 2 = 1 := by
    calc
      ω ^ 2 = (ω ^ 2 * u ^ 2) * (u ^ 2)⁻¹ := by group
      _ = u ^ 2 * (u ^ 2)⁻¹ := by rw [hcancel]
      _ = 1 := by simp
  exact ⟨ω, hω, ht, hu', hvform⟩

/-! Cartan-kernel identities for even type `D`. -/

/-- The even-rank specialization of the type `D` fork kernel. -/
private lemma typeDEvenForkCartanKernel
    {G : Type*} [CommGroup G] (q : ℕ) (hq : 2 ≤ q)
    (t : ℕ → G) (u v : G)
    (hchain : ∀ i, i < 2 * q - 3 →
      t i ^ 2 = (if i = 0 then 1 else t (i - 1)) * t (i + 1))
    (hbranch : t (2 * q - 3) ^ 2 = t (2 * q - 4) * u * v)
    (hu : u ^ 2 = t (2 * q - 3))
    (hv : v ^ 2 = t (2 * q - 3)) :
    ∃ ω η : G, ω ^ 2 = 1 ∧ η ^ 2 = 1 ∧
      (∀ i, i ≤ 2 * q - 3 → t i = ω ^ (i + 1)) ∧
      u = η ∧ v = ω * η := by
  obtain ⟨ω, hω, ht, hu', hv'⟩ :=
    typeDForkCartanKernel (2 * q - 3) (by omega) t u v
      hchain hbranch hu hv
  refine ⟨ω, u, hω, ?_, ht, rfl, hv'⟩
  calc
    u ^ 2 = ω ^ (2 * q - 3 + 1) := hu'
    _ = ω ^ (2 * (q - 1)) := by congr 1; omega
    _ = (ω ^ 2) ^ (q - 1) := by rw [pow_mul]
    _ = 1 := by simp [hω]

/-- The odd-rank specialization of the type `D` fork kernel. -/
private lemma typeDOddForkCartanKernel
    {G : Type*} [CommGroup G] (q : ℕ) (hq : 2 ≤ q)
    (t : ℕ → G) (u v : G)
    (hchain : ∀ i, i < 2 * q - 2 →
      t i ^ 2 = (if i = 0 then 1 else t (i - 1)) * t (i + 1))
    (hbranch : t (2 * q - 2) ^ 2 = t (2 * q - 3) * u * v)
    (hu : u ^ 2 = t (2 * q - 2))
    (hv : v ^ 2 = t (2 * q - 2)) :
    ∃ η : G, η ^ 4 = 1 ∧
      (∀ i, i ≤ 2 * q - 2 → t i = (η ^ 2) ^ (i + 1)) ∧
      u = η ∧ v = η ^ 2 * η := by
  obtain ⟨ω, hω, ht, hu', hv'⟩ :=
    typeDForkCartanKernel (2 * q - 2) (by omega) t u v
      hchain hbranch hu hv
  have huω : u ^ 2 = ω := by
    calc
      u ^ 2 = ω ^ (2 * q - 2 + 1) := hu'
      _ = ω ^ (2 * (q - 1) + 1) := by congr 1; omega
      _ = (ω ^ 2) ^ (q - 1) * ω := by rw [pow_add, pow_mul, pow_one]
      _ = ω := by simp [hω]
  have hu4 : u ^ 4 = 1 := by
    calc
      u ^ 4 = (u ^ 2) ^ 2 := by group
      _ = ω ^ 2 := by rw [huω]
      _ = 1 := hω
  refine ⟨u, hu4, ?_, rfl, ?_⟩
  · intro i hi
    calc
      t i = ω ^ (i + 1) := ht i hi
      _ = (u ^ 2) ^ (i + 1) := by rw [huω]
  · calc
      v = ω * u := hv'
      _ = u ^ 2 * u := by rw [huω]

open scoped BigOperators

/-- The common multiplicative kernel of the standard type `A` Cartan relations. -/
public theorem dynkinCartanRelationKernel_A
    {k : Type*} [Field k] (m : ℕ) (t : Fin (m + 1) → kˣ)
    (h : ∀ j,
      (∏ i, t i ^ dynkinCartanEntry ⟨.A, m + 1⟩ i j) = 1) :
    ∃ ω : kˣ, ω ^ (m + 2) = 1 ∧
      ∀ i, t i = ω ^ (i.val + 1) := by
  classical
  let tn : ℕ → kˣ := fun i =>
    if hi : i < m + 1 then t ⟨i, hi⟩ else 1
  have prod_eq_support
      (f : Fin (m + 1) → kˣ) (S : Finset (Fin (m + 1)))
      (hf : ∀ x, x ∉ S → f x = 1) :
      (∏ x, f x) = ∏ x ∈ S, f x := by
    symm
    apply Finset.prod_subset (by simp)
    intro x _ hx
    exact hf x hx
  have hrec : ∀ i, i ≤ m →
      tn i ^ 2 = (if i = 0 then 1 else tn (i - 1)) *
        (if i = m then 1 else tn (i + 1)) := by
    intro i hi
    let j : Fin (m + 1) := ⟨i, by omega⟩
    have hibound : i < m + 1 := by omega
    have htj : tn i = t j := by
      simp only [tn, dif_pos hibound]
      apply congrArg t
      apply Fin.ext
      rfl
    rw [htj]
    by_cases hi0 : i = 0
    · subst i
      by_cases hm0 : m = 0
      · subst m
        have hj := h (0 : Fin 1)
        have hj0 : j = (0 : Fin 1) := by
          apply Fin.ext
          simp [j]
        rw [hj0]
        simpa [tn, dynkinCartanEntry, zpow_ofNat] using hj
      · let s : Fin (m + 1) := ⟨1, by omega⟩
        have hj := h j
        have hsupp :
            (∏ x, t x ^ dynkinCartanEntry ⟨.A, m + 1⟩ x j) =
              ∏ x ∈ ({j, s} : Finset (Fin (m + 1))),
                t x ^ dynkinCartanEntry ⟨.A, m + 1⟩ x j := by
          apply prod_eq_support
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
          have hx1 : x.val ≠ 1 := by
            intro hxval
            apply hx.2
            apply Fin.ext
            simpa [s] using hxval
          have hadj :
              ¬(x.val + 1 = j.val ∨ j.val + 1 = x.val) := by
            simp [j]
            omega
          rw [dynkinCartanEntry, if_neg hx.1, if_neg hadj]
          simp
        rw [hsupp] at hj
        have hjs : j ≠ s := by
          intro hjs
          have := congrArg Fin.val hjs
          simp [j, s] at this
        rw [Finset.prod_pair hjs] at hj
        have heq : (t j) ^ 2 * (t s)⁻¹ = 1 := by
          simpa [dynkinCartanEntry, j, s, zpow_ofNat] using hj
        have hcoord : (t j) ^ 2 = t s := mul_inv_eq_one.mp heq
        rw [if_pos rfl, if_neg (Ne.symm hm0), one_mul]
        have h1bound : 1 < m + 1 := by omega
        have htns : tn 1 = t s := by
          simp only [tn, dif_pos h1bound]
          apply congrArg t
          apply Fin.ext
          rfl
        rw [htns]
        exact hcoord
    · by_cases him : i = m
      · subst i
        let p : Fin (m + 1) := ⟨m - 1, by omega⟩
        have hj := h j
        have hsupp :
            (∏ x, t x ^ dynkinCartanEntry ⟨.A, m + 1⟩ x j) =
              ∏ x ∈ ({p, j} : Finset (Fin (m + 1))),
                t x ^ dynkinCartanEntry ⟨.A, m + 1⟩ x j := by
          apply prod_eq_support
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
          have hxp : x.val ≠ m - 1 := by
            intro hxval
            apply hx.1
            apply Fin.ext
            simpa [p] using hxval
          have hxm : x.val ≠ m := by
            intro hxval
            apply hx.2
            apply Fin.ext
            simpa [j] using hxval
          have hxpred : x.val + 1 ≠ m := by omega
          have hxsucc : m + 1 ≠ x.val := by omega
          have hadj :
              ¬(x.val + 1 = j.val ∨ j.val + 1 = x.val) := by
            simp [j, hxpred, hxsucc]
          simp [dynkinCartanEntry, hx.2, hadj]
        rw [hsupp] at hj
        have hpj : p ≠ j := by
          intro hpj
          have := congrArg Fin.val hpj
          simp [p, j] at this
          omega
        rw [Finset.prod_pair hpj] at hj
        have hpredEq : m - 1 + 1 = m :=
          Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi0)
        have heq : (t p)⁻¹ * (t j) ^ 2 = 1 := by
          simpa [dynkinCartanEntry, p, j, hpj, hpredEq, zpow_ofNat] using hj
        have hcoord : (t j) ^ 2 = t p := by
          symm
          exact inv_mul_eq_one.mp heq
        rw [if_neg hi0, if_pos rfl, mul_one]
        have hmpred : m - 1 < m + 1 := by omega
        have htnp : tn (m - 1) = t p := by
          simp only [tn, dif_pos hmpred]
          apply congrArg t
          apply Fin.ext
          rfl
        rw [htnp]
        exact hcoord
      · let p : Fin (m + 1) := ⟨i - 1, by omega⟩
        let s : Fin (m + 1) := ⟨i + 1, by omega⟩
        have hj := h j
        have hsupp :
            (∏ x, t x ^ dynkinCartanEntry ⟨.A, m + 1⟩ x j) =
              ∏ x ∈ ({p, j, s} : Finset (Fin (m + 1))),
                t x ^ dynkinCartanEntry ⟨.A, m + 1⟩ x j := by
          apply prod_eq_support
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
          have hxp : x.val ≠ i - 1 := by
            intro hxval
            apply hx.1
            apply Fin.ext
            simpa [p] using hxval
          have hxj : x.val ≠ i := by
            intro hxval
            apply hx.2.1
            apply Fin.ext
            simpa [j] using hxval
          have hxs : x.val ≠ i + 1 := by
            intro hxval
            apply hx.2.2
            apply Fin.ext
            simpa [s] using hxval
          have hxpred : x.val + 1 ≠ i := by omega
          have hxsucc : i + 1 ≠ x.val := by omega
          have hadj :
              ¬(x.val + 1 = j.val ∨ j.val + 1 = x.val) := by
            simp [j, hxpred, hxsucc]
          simp [dynkinCartanEntry, hx.2.1, hadj]
        rw [hsupp] at hj
        have hpj : p ≠ j := by
          intro hpj
          have := congrArg Fin.val hpj
          simp [p, j] at this
          omega
        have hps : p ≠ s := by
          intro hps
          have := congrArg Fin.val hps
          simp [p, s] at this
        have hjs : j ≠ s := by
          intro hjs
          have := congrArg Fin.val hjs
          simp [j, s] at this
        have hipredEq : i - 1 + 1 = i :=
          Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi0)
        simp [Finset.prod_insert, hpj, hps, hjs, hipredEq,
          dynkinCartanEntry, p, j, s, zpow_ofNat] at hj
        have heq : (t p)⁻¹ * (t j) ^ 2 * (t s)⁻¹ = 1 := by
          simpa [mul_assoc] using hj
        have hcoord : (t j) ^ 2 = t p * t s := by
          calc
            (t j) ^ 2 = t p * ((t p)⁻¹ * (t j) ^ 2 * (t s)⁻¹) * t s := by
              group
            _ = t p * t s := by rw [heq]; simp
        have hpbound : i - 1 < m + 1 := by omega
        have hsbound : i + 1 < m + 1 := by omega
        have htnp : tn (i - 1) = t p := by
          simp only [tn, dif_pos hpbound]
          apply congrArg t
          apply Fin.ext
          rfl
        have htns : tn (i + 1) = t s := by
          simp only [tn, dif_pos hsbound]
          apply congrArg t
          apply Fin.ext
          rfl
        rw [if_neg hi0, if_neg him, htnp, htns]
        exact hcoord
  obtain ⟨ω, hω, ht⟩ := typeAChainCartanKernel m tn hrec
  refine ⟨ω, hω, ?_⟩
  intro i
  have hi : i.val ≤ m := by omega
  have hitn : tn i.val = t i := by
    simp only [tn, dif_pos i.isLt]
  simpa [hitn] using ht i.val hi

open scoped BigOperators

public theorem dynkinCartanRelationKernel_B
    {k : Type*} [Field k] (m : ℕ) (hm : 1 ≤ m) (t : Fin (m + 1) → kˣ)
    (h : ∀ j,
      (∏ i, t i ^ dynkinCartanEntry ⟨.B, m + 1⟩ i j) = 1) :
    ∃ ω : kˣ, ω ^ 2 = 1 ∧
      ∀ i, t i = ω ^ (i.val + 1) := by
  classical
  let tn : ℕ → kˣ := fun i =>
    if hi : i < m + 1 then t ⟨i, hi⟩ else 1
  have prod_eq_support
      (f : Fin (m + 1) → kˣ) (S : Finset (Fin (m + 1)))
      (hf : ∀ x, x ∉ S → f x = 1) :
      (∏ x, f x) = ∏ x ∈ S, f x := by
    symm
    apply Finset.prod_subset (by simp)
    intro x _ hx
    exact hf x hx
  have hrec : ∀ i, i ≤ m →
      tn i ^ 2 = (if i = 0 then 1 else tn (i - 1)) *
        (if i = m then tn (m - 1) else tn (i + 1)) := by
    intro i hi
    let j : Fin (m + 1) := ⟨i, by omega⟩
    have hibound : i < m + 1 := by omega
    have htj : tn i = t j := by
      simp only [tn, dif_pos hibound]
      apply congrArg t
      apply Fin.ext
      rfl
    rw [htj]
    by_cases hi0 : i = 0
    · subst i
      let s : Fin (m + 1) := ⟨1, by omega⟩
      have hj := h j
      have hsupp :
          (∏ x, t x ^ dynkinCartanEntry ⟨.B, m + 1⟩ x j) =
            ∏ x ∈ ({j, s} : Finset (Fin (m + 1))),
              t x ^ dynkinCartanEntry ⟨.B, m + 1⟩ x j := by
        apply prod_eq_support
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        have hx0 : x.val ≠ 0 := by
          intro hxval
          apply hx.1
          apply Fin.ext
          simpa [j] using hxval
        have hx1 : x.val ≠ 1 := by
          intro hxval
          apply hx.2
          apply Fin.ext
          simpa [s] using hxval
        have hleft : x.val + 1 ≠ j.val := by simp [j]
        have hright : j.val + 1 ≠ x.val := by simp [j]; omega
        simp [dynkinCartanEntry, hx.1, hleft, hright]
      rw [hsupp] at hj
      have hjs : j ≠ s := by
        intro hjs
        have := congrArg Fin.val hjs
        simp [j, s] at this
      rw [Finset.prod_pair hjs] at hj
      have heq : (t j) ^ 2 * (t s)⁻¹ = 1 := by
        simpa [dynkinCartanEntry, j, s, zpow_ofNat] using hj
      have hcoord : (t j) ^ 2 = t s := mul_inv_eq_one.mp heq
      rw [if_pos rfl, if_neg (by omega), one_mul]
      have htns : tn 1 = t s := by
        simp only [tn, dif_pos (by omega : 1 < m + 1)]
        apply congrArg t
        apply Fin.ext
        rfl
      rw [htns]
      exact hcoord
    · by_cases him : i = m
      · subst i
        let p : Fin (m + 1) := ⟨m - 1, by omega⟩
        have hj := h j
        have hsupp :
            (∏ x, t x ^ dynkinCartanEntry ⟨.B, m + 1⟩ x j) =
              ∏ x ∈ ({p, j} : Finset (Fin (m + 1))),
                t x ^ dynkinCartanEntry ⟨.B, m + 1⟩ x j := by
          apply prod_eq_support
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
          have hxp : x.val ≠ m - 1 := by
            intro hxval
            apply hx.1
            apply Fin.ext
            simpa [p] using hxval
          have hxj : x.val ≠ m := by
            intro hxval
            apply hx.2
            apply Fin.ext
            simpa [j] using hxval
          have hleft : x.val + 1 ≠ j.val := by simp [j]; omega
          have hright : j.val + 1 ≠ x.val := by simp [j]; omega
          simp [dynkinCartanEntry, hx.2, hleft, hright]
        rw [hsupp] at hj
        have hpj : p ≠ j := by
          intro hpj
          have := congrArg Fin.val hpj
          simp [p, j] at this
          omega
        rw [Finset.prod_pair hpj] at hj
        have hpredEq : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
        have heq : (t p) ^ (-2 : ℤ) * (t j) ^ 2 = 1 := by
          simpa [dynkinCartanEntry, p, j, hpj, hpredEq, zpow_neg,
            zpow_ofNat] using hj
        have heq' : ((t p) ^ 2)⁻¹ * (t j) ^ 2 = 1 := by
          simpa [zpow_neg, zpow_ofNat, pow_two] using heq
        have hcoord : (t j) ^ 2 = (t p) ^ 2 := (inv_mul_eq_one.mp heq').symm
        rw [if_neg hi0, if_pos rfl]
        have htnp : tn (m - 1) = t p := by
          simp only [tn, dif_pos (by omega : m - 1 < m + 1)]
          apply congrArg t
          apply Fin.ext
          rfl
        rw [htnp]
        simpa [pow_two] using hcoord
      · let p : Fin (m + 1) := ⟨i - 1, by omega⟩
        let s : Fin (m + 1) := ⟨i + 1, by omega⟩
        have hj := h j
        have hsupp :
            (∏ x, t x ^ dynkinCartanEntry ⟨.B, m + 1⟩ x j) =
              ∏ x ∈ ({p, j, s} : Finset (Fin (m + 1))),
                t x ^ dynkinCartanEntry ⟨.B, m + 1⟩ x j := by
          apply prod_eq_support
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
          have hxp : x.val ≠ i - 1 := by
            intro hxval
            apply hx.1
            apply Fin.ext
            simpa [p] using hxval
          have hxj : x.val ≠ i := by
            intro hxval
            apply hx.2.1
            apply Fin.ext
            simpa [j] using hxval
          have hxs : x.val ≠ i + 1 := by
            intro hxval
            apply hx.2.2
            apply Fin.ext
            simpa [s] using hxval
          have hleft : x.val + 1 ≠ j.val := by simp [j]; omega
          have hright : j.val + 1 ≠ x.val := by simp [j]; omega
          simp [dynkinCartanEntry, hx.2.1, hleft, hright]
        rw [hsupp] at hj
        have hpj : p ≠ j := by
          intro hpj
          have := congrArg Fin.val hpj
          simp [p, j] at this
          omega
        have hps : p ≠ s := by
          intro hps
          have := congrArg Fin.val hps
          simp [p, s] at this
        have hjs : j ≠ s := by
          intro hjs
          have := congrArg Fin.val hjs
          simp [j, s] at this
        have hipredEq : i - 1 + 1 = i := Nat.sub_add_cancel (by omega)
        have hsucc_ne : i + 1 + 1 ≠ i := by omega
        simp [Finset.prod_insert, hpj, hps, hjs, hipredEq, him,
          hsucc_ne, dynkinCartanEntry, p, j, s, zpow_ofNat] at hj
        have heq : (t p)⁻¹ * (t j) ^ 2 * (t s)⁻¹ = 1 := by
          simpa [mul_assoc] using hj
        have hcoord : (t j) ^ 2 = t p * t s := by
          calc
            (t j) ^ 2 = t p * ((t p)⁻¹ * (t j) ^ 2 * (t s)⁻¹) * t s := by
              group
            _ = t p * t s := by rw [heq]; simp
        have htnp : tn (i - 1) = t p := by
          simp only [tn, dif_pos (by omega : i - 1 < m + 1)]
          apply congrArg t
          apply Fin.ext
          rfl
        have htns : tn (i + 1) = t s := by
          simp only [tn, dif_pos (by omega : i + 1 < m + 1)]
          apply congrArg t
          apply Fin.ext
          rfl
        rw [if_neg hi0, if_neg him, htnp, htns]
        exact hcoord
  obtain ⟨ω, hω, ht⟩ := typeBChainCartanKernel m tn hm hrec
  refine ⟨ω, hω, ?_⟩
  intro i
  have hi : i.val ≤ m := by omega
  have hitn : tn i.val = t i := by
    simp only [tn, dif_pos i.isLt]
  simpa [hitn] using ht i.val hi

open scoped BigOperators

public theorem dynkinCartanRelationKernel_B2
    {k : Type*} [Field k] (t : Fin 2 → kˣ)
    (h : ∀ j, (∏ i, t i ^ dynkinCartanEntry ⟨.B, 2⟩ i j) = 1) :
    ∃ ω : kˣ, ω ^ (2 : ℤ) = 1 ∧ t 0 = ω ∧ t 1 = 1 := by
  have h0 := h (0 : Fin 2)
  have h1 := h (1 : Fin 2)
  simp [dynkinCartanEntry] at h0 h1
  have ht1 : t 1 = t 0 ^ (2 : ℤ) := by
    apply inv_mul_eq_one.mp
    simpa [mul_comm] using h0
  have ht0 : t 0 ^ (2 : ℤ) = 1 := by
    rw [ht1] at h1
    have heq := inv_mul_eq_one.mp h1
    let a : kˣ := t 0 ^ (2 : ℕ)
    change a = a ^ (2 : ℕ) at heq
    have haeq : a * a = a := (pow_two a).symm.trans heq.symm
    have ha : a = 1 := by
      apply mul_left_cancel (a := a)
      simpa using haeq
    simpa [zpow_ofNat] using ha
  have ht1one : t 1 = 1 := by simpa [ht0] using ht1
  refine ⟨t 0, ht0, rfl, ht1one⟩

open scoped BigOperators

/-- The common multiplicative kernel of the standard type `C` Cartan relations. -/
public theorem dynkinCartanRelationKernel_C
    {k : Type*} [Field k] (m : ℕ) (hm : 1 ≤ m)
    (t : Fin (m + 1) → kˣ)
    (h : ∀ j,
      (∏ i, t i ^ dynkinCartanEntry ⟨.C, m + 1⟩ i j) = 1) :
    ∃ ω : kˣ, ω ^ 2 = 1 ∧
      ∀ i, t i = (if i.val = m then ω else 1) := by
  classical
  let tn : ℕ → kˣ := fun i =>
    if hi : i < m + 1 then t ⟨i, hi⟩ else 1
  have prod_eq_support
      (f : Fin (m + 1) → kˣ) (S : Finset (Fin (m + 1)))
      (hf : ∀ x, x ∉ S → f x = 1) :
      (∏ x, f x) = ∏ x ∈ S, f x := by
    symm
    apply Finset.prod_subset (by simp)
    intro x _ hx
    exact hf x hx
  have hreg : ∀ i, i + 1 < m →
      tn i ^ 2 = (if i = 0 then 1 else tn (i - 1)) * tn (i + 1) := by
    intro i hi
    let j : Fin (m + 1) := ⟨i, by omega⟩
    have htj : tn i = t j := by
      simp only [tn, dif_pos (by omega : i < m + 1)]
      apply congrArg t
      apply Fin.ext
      rfl
    rw [htj]
    by_cases hi0 : i = 0
    · subst i
      let s : Fin (m + 1) := ⟨1, by omega⟩
      have hj := h j
      have hsupp :
          (∏ x, t x ^ dynkinCartanEntry ⟨.C, m + 1⟩ x j) =
            ∏ x ∈ ({j, s} : Finset (Fin (m + 1))),
              t x ^ dynkinCartanEntry ⟨.C, m + 1⟩ x j := by
        apply prod_eq_support
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        have hleft : x.val + 1 ≠ j.val := by simp [j]
        have hright : j.val + 1 ≠ x.val := by
          simp [j]
          intro hx1
          apply hx.2
          apply Fin.ext
          simpa [s] using hx1.symm
        rw [dynkinCartanEntry, if_neg hx.1, if_neg hleft]
        rw [if_neg hright]
        simp [hleft, hright]
      rw [hsupp] at hj
      have hjs : j ≠ s := by
        intro hjs
        have := congrArg Fin.val hjs
        simp [j, s] at this
      rw [Finset.prod_pair hjs] at hj
      have hm1 : m ≠ 1 := by omega
      have heq : (t j) ^ 2 * (t s)⁻¹ = 1 := by
        simpa [dynkinCartanEntry, j, s, hm1, zpow_ofNat] using hj
      have hcoord : (t j) ^ 2 = t s := mul_inv_eq_one.mp heq
      rw [if_pos rfl, one_mul]
      have htns : tn 1 = t s := by
        simp only [tn, dif_pos (by omega : 1 < m + 1)]
        apply congrArg t
        apply Fin.ext
        rfl
      rw [htns]
      exact hcoord
    · let p : Fin (m + 1) := ⟨i - 1, by omega⟩
      let s : Fin (m + 1) := ⟨i + 1, by omega⟩
      have hj := h j
      have hsupp :
          (∏ x, t x ^ dynkinCartanEntry ⟨.C, m + 1⟩ x j) =
            ∏ x ∈ ({p, j, s} : Finset (Fin (m + 1))),
              t x ^ dynkinCartanEntry ⟨.C, m + 1⟩ x j := by
        apply prod_eq_support
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        have hxp : x.val ≠ i - 1 := by
          intro hxval
          apply hx.1
          apply Fin.ext
          simpa [p] using hxval
        have hxs : x.val ≠ i + 1 := by
          intro hxval
          apply hx.2.2
          apply Fin.ext
          simpa [s] using hxval
        have hleft : x.val + 1 ≠ j.val := by
          simp [j]
          omega
        have hright : j.val + 1 ≠ x.val := by
          simp [j]
          omega
        rw [dynkinCartanEntry, if_neg hx.2.1, if_neg hleft]
        rw [if_neg hright]
        simp [hleft, hright]
      rw [hsupp] at hj
      have hpj : p ≠ j := by
        intro hpj
        have := congrArg Fin.val hpj
        simp [p, j] at this
        omega
      have hps : p ≠ s := by
        intro hps
        have := congrArg Fin.val hps
        simp [p, s] at this
      have hjs : j ≠ s := by
        intro hjs
        have := congrArg Fin.val hjs
        simp [j, s] at this
      have hipred : i - 1 + 1 = i := Nat.sub_add_cancel (by omega)
      have hsuccNotTerminal : i + 1 ≠ m := by omega
      simp [Finset.prod_insert, hpj, hps, hjs, hipred, hsuccNotTerminal,
        dynkinCartanEntry, p, j, s, zpow_ofNat] at hj
      have heq : (t p)⁻¹ * (t j) ^ 2 * (t s)⁻¹ = 1 := by
        simpa [mul_assoc] using hj
      have hcoord : (t j) ^ 2 = t p * t s := by
        calc
          (t j) ^ 2 = t p * ((t p)⁻¹ * (t j) ^ 2 * (t s)⁻¹) * t s := by
            group
          _ = t p * t s := by rw [heq]; simp
      have htnp : tn (i - 1) = t p := by
        simp only [tn, dif_pos (by omega : i - 1 < m + 1)]
        apply congrArg t
        apply Fin.ext
        rfl
      have htns : tn (i + 1) = t s := by
        simp only [tn, dif_pos (by omega : i + 1 < m + 1)]
        apply congrArg t
        apply Fin.ext
        rfl
      rw [if_neg hi0, htnp, htns]
      exact hcoord
  have hpenult : tn (m - 1) ^ 2 =
      (if m = 1 then 1 else tn (m - 2)) * tn m ^ 2 := by
    let j : Fin (m + 1) := ⟨m - 1, by omega⟩
    have htj : tn (m - 1) = t j := by
      simp only [tn, dif_pos (by omega : m - 1 < m + 1)]
      apply congrArg t
      apply Fin.ext
      rfl
    rw [htj]
    by_cases hm1 : m = 1
    · subst m
      let s : Fin 2 := ⟨1, by omega⟩
      have hj := h j
      have hsupp :
          (∏ x, t x ^ dynkinCartanEntry ⟨.C, 2⟩ x j) =
            ∏ x ∈ ({j, s} : Finset (Fin 2)),
              t x ^ dynkinCartanEntry ⟨.C, 2⟩ x j := by
        apply prod_eq_support
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        fin_cases x <;> simp_all [j, s]
      rw [hsupp] at hj
      have hjs : j ≠ s := by
        intro hjs
        have := congrArg Fin.val hjs
        simp [j, s] at this
      rw [Finset.prod_pair hjs] at hj
      have heq : (t j) ^ 2 * ((t s) ^ 2)⁻¹ = 1 := by
        simpa [dynkinCartanEntry, j, s, zpow_neg, zpow_ofNat] using hj
      have hcoord : (t j) ^ 2 = (t s) ^ 2 := mul_inv_eq_one.mp heq
      rw [if_pos rfl, one_mul]
      have htns : tn 1 = t s := by
        simp only [tn, dif_pos (by omega : 1 < 2)]
        apply congrArg t
        apply Fin.ext
        rfl
      rw [htns]
      exact hcoord
    · have hm2 : 2 ≤ m := by omega
      let p : Fin (m + 1) := ⟨m - 2, by omega⟩
      let s : Fin (m + 1) := ⟨m, by omega⟩
      have hj := h j
      have hsupp :
          (∏ x, t x ^ dynkinCartanEntry ⟨.C, m + 1⟩ x j) =
            ∏ x ∈ ({p, j, s} : Finset (Fin (m + 1))),
              t x ^ dynkinCartanEntry ⟨.C, m + 1⟩ x j := by
        apply prod_eq_support
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        have hxp : x.val ≠ m - 2 := by
          intro hxval
          apply hx.1
          apply Fin.ext
          simpa [p] using hxval
        have hxs : x.val ≠ m := by
          intro hxval
          apply hx.2.2
          apply Fin.ext
          simpa [s] using hxval
        have hleft : x.val + 1 ≠ j.val := by
          simp [j]
          omega
        have hright : j.val + 1 ≠ x.val := by
          simp [j]
          omega
        rw [dynkinCartanEntry, if_neg hx.2.1, if_neg hleft]
        rw [if_neg hright]
        simp [hleft, hright]
      rw [hsupp] at hj
      have hpj : p ≠ j := by
        intro hpj
        have := congrArg Fin.val hpj
        simp [p, j] at this
        omega
      have hps : p ≠ s := by
        intro hps
        have := congrArg Fin.val hps
        simp [p, s] at this
        omega
      have hjs : j ≠ s := by
        intro hjs
        have := congrArg Fin.val hjs
        simp [j, s] at this
        omega
      have hpred : m - 2 + 1 = m - 1 := by omega
      have hsucc : m - 1 + 1 = m := by omega
      have hne1 : m ≠ m - 1 := by omega
      have hne2 : m + 1 ≠ m - 1 := by omega
      simp [Finset.prod_insert, hpj, hps, hjs, hpred, hsucc, hne1, hne2,
        dynkinCartanEntry, p, j, s, zpow_neg, zpow_ofNat] at hj
      have heq : (t p)⁻¹ * (t j) ^ 2 * ((t s) ^ 2)⁻¹ = 1 := by
        simpa [mul_assoc] using hj
      have hcoord : (t j) ^ 2 = t p * (t s) ^ 2 := by
        calc
          (t j) ^ 2 =
              t p * ((t p)⁻¹ * (t j) ^ 2 * ((t s) ^ 2)⁻¹) * (t s) ^ 2 := by
            group
          _ = t p * (t s) ^ 2 := by rw [heq]; simp
      have htnp : tn (m - 2) = t p := by
        simp only [tn, dif_pos (by omega : m - 2 < m + 1)]
        apply congrArg t
        apply Fin.ext
        rfl
      have htns : tn m = t s := by
        simp only [tn, dif_pos (by omega : m < m + 1)]
        apply congrArg t
        apply Fin.ext
        rfl
      rw [if_neg hm1, htnp, htns]
      exact hcoord
  have hlast : tn m ^ 2 = tn (m - 1) := by
    let j : Fin (m + 1) := ⟨m, by omega⟩
    let p : Fin (m + 1) := ⟨m - 1, by omega⟩
    have hj := h j
    have hsupp :
        (∏ x, t x ^ dynkinCartanEntry ⟨.C, m + 1⟩ x j) =
          ∏ x ∈ ({p, j} : Finset (Fin (m + 1))),
            t x ^ dynkinCartanEntry ⟨.C, m + 1⟩ x j := by
      apply prod_eq_support
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      have hxp : x.val ≠ m - 1 := by
        intro hxval
        apply hx.1
        apply Fin.ext
        simpa [p] using hxval
      have hleft : x.val + 1 ≠ j.val := by
        simp [j]
        omega
      have hright : j.val + 1 ≠ x.val := by simp [j]; omega
      rw [dynkinCartanEntry, if_neg hx.2, if_neg hleft]
      rw [if_neg hright]
      simp [hleft, hright]
    rw [hsupp] at hj
    have hpj : p ≠ j := by
      intro hpj
      have := congrArg Fin.val hpj
      simp [p, j] at this
      omega
    rw [Finset.prod_pair hpj] at hj
    have hpred : m - 1 + 1 = m := Nat.sub_add_cancel hm
    have heq : (t p)⁻¹ * (t j) ^ 2 = 1 := by
      simpa [dynkinCartanEntry, p, j, hpj, hpred, zpow_ofNat] using hj
    have hcoord : (t j) ^ 2 = t p := by
      symm
      exact inv_mul_eq_one.mp heq
    have htj : tn m = t j := by
      simp only [tn, dif_pos (by omega : m < m + 1)]
      apply congrArg t
      apply Fin.ext
      rfl
    have htnp : tn (m - 1) = t p := by
      simp only [tn, dif_pos (by omega : m - 1 < m + 1)]
      apply congrArg t
      apply Fin.ext
      rfl
    rw [htj, htnp]
    exact hcoord
  obtain ⟨ω, hω, ht⟩ := typeCChainCartanKernel m tn hm hreg hpenult hlast
  refine ⟨ω, hω, ?_⟩
  intro i
  have hi : i.val ≤ m := by omega
  have hitn : tn i.val = t i := by
    simp only [tn, dif_pos i.isLt]
  simpa [hitn] using ht i.val hi

open scoped BigOperators

public theorem dynkinCartanRelationKernel_C2
    {k : Type*} [Field k] (t : Fin 2 → kˣ)
    (h : ∀ j, (∏ i, t i ^ dynkinCartanEntry ⟨.C, 2⟩ i j) = 1) :
    ∃ ω : kˣ, ω ^ (2 : ℤ) = 1 ∧ t 0 = 1 ∧ t 1 = ω := by
  have h0 := h (0 : Fin 2)
  have h1 := h (1 : Fin 2)
  simp [dynkinCartanEntry] at h0 h1
  have ht0 : t 0 = t 1 ^ (2 : ℤ) := by
    apply inv_mul_eq_one.mp
    simpa [mul_comm] using h1
  have ht1 : t 1 ^ (2 : ℤ) = 1 := by
    rw [ht0] at h0
    have heq := mul_inv_eq_one.mp h0
    let a : kˣ := t 1 ^ (2 : ℕ)
    change a ^ (2 : ℕ) = a at heq
    have haeq : a * a = a := (pow_two a).symm.trans heq
    have ha : a = 1 := by
      apply mul_right_cancel (b := a)
      simpa using haeq
    simpa [zpow_ofNat] using ha
  have ht0one : t 0 = 1 := by simpa [ht1] using ht0
  refine ⟨t 1, ht1, ht0one, rfl⟩

open scoped BigOperators

public theorem dynkinCartanRelationKernel_C3
    {k : Type*} [Field k] (t : Fin 3 → kˣ)
    (h : ∀ j, (∏ i, t i ^ dynkinCartanEntry ⟨.C, 3⟩ i j) = 1) :
    ∃ ω : kˣ, ω ^ (2 : ℤ) = 1 ∧ t 0 = 1 ∧ t 1 = 1 ∧ t 2 = ω := by
  have h0 := h (0 : Fin 3)
  have h1 := h (1 : Fin 3)
  have h2 := h (2 : Fin 3)
  rw [Fin.prod_univ_three] at h0 h1 h2
  simp [dynkinCartanEntry] at h0 h1 h2
  have ht1 : t 1 = t 0 ^ (2 : ℤ) := by
    apply inv_mul_eq_one.mp
    simpa [mul_comm] using h0
  have ht2sq : t 2 ^ (2 : ℤ) = t 1 := by
    exact (inv_mul_eq_one.mp h2).symm
  rw [ht1] at h1
  rw [ht1] at ht2sq
  have ht2sq' : t 2 ^ (2 : ℕ) = t 0 ^ (2 : ℕ) := by
    simpa [zpow_ofNat] using ht2sq
  rw [ht2sq'] at h1
  have ht0 : t 0 = 1 := by
    calc
      t 0 = (t 0)⁻¹ * (t 0 ^ (2 : ℤ)) ^ (2 : ℤ) *
          (t 0 ^ (2 : ℤ))⁻¹ := by group
      _ = 1 := by simpa [zpow_neg] using h1
  have ht1one : t 1 = 1 := by simpa [ht0] using ht1
  have ht2 : t 2 ^ (2 : ℤ) = 1 := by simpa [ht0] using ht2sq
  exact ⟨t 2, ht2, ht0, ht1one, rfl⟩

open scoped BigOperators

/-- The common multiplicative kernel of the standard type `D` Cartan relations. -/
public theorem dynkinCartanRelationKernel_D
    {k : Type*} [Field k] (m : ℕ) (hm : 1 ≤ m)
    (t : Fin (m + 3) → kˣ)
    (h : ∀ j,
      (∏ i, t i ^ dynkinCartanEntry ⟨.D, m + 3⟩ i j) = 1) :
    ∃ ω : kˣ, ω ^ 2 = 1 ∧
      (∀ i : Fin (m + 1),
        t ⟨i.val, by omega⟩ = ω ^ (i.val + 1)) ∧
      t ⟨m + 1, by omega⟩ ^ 2 = ω ^ (m + 1) ∧
      t ⟨m + 2, by omega⟩ = ω * t ⟨m + 1, by omega⟩ := by
  classical
  let tn : ℕ → kˣ := fun i =>
    if hi : i < m + 1 then t ⟨i, by omega⟩ else 1
  let u : Fin (m + 3) := ⟨m + 1, by omega⟩
  let v : Fin (m + 3) := ⟨m + 2, by omega⟩
  have prod_eq_support
      (f : Fin (m + 3) → kˣ) (S : Finset (Fin (m + 3)))
      (hf : ∀ x, x ∉ S → f x = 1) :
      (∏ x, f x) = ∏ x ∈ S, f x := by
    symm
    apply Finset.prod_subset (by simp)
    intro x _ hx
    exact hf x hx
  have hchain : ∀ i, i < m →
      tn i ^ 2 = (if i = 0 then 1 else tn (i - 1)) * tn (i + 1) := by
    intro i hi
    let j : Fin (m + 3) := ⟨i, by omega⟩
    have htj : tn i = t j := by
      simp only [tn, dif_pos (by omega : i < m + 1)]
      apply congrArg t
      apply Fin.ext
      rfl
    rw [htj]
    by_cases hi0 : i = 0
    · subst i
      let s : Fin (m + 3) := ⟨1, by omega⟩
      have hj := h j
      have hsupp :
          (∏ x, t x ^ dynkinCartanEntry ⟨.D, m + 3⟩ x j) =
            ∏ x ∈ ({j, s} : Finset (Fin (m + 3))),
              t x ^ dynkinCartanEntry ⟨.D, m + 3⟩ x j := by
        apply prod_eq_support
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        have hx0 : x.val ≠ 0 := by
          intro hxval
          apply hx.1
          apply Fin.ext
          simpa [j] using hxval
        have hx1 : x.val ≠ 1 := by
          intro hxval
          apply hx.2
          apply Fin.ext
          simpa [s] using hxval
        have hadj : ¬(
            (x.val + 1 = j.val ∧ j.val + 2 < m + 3) ∨
            (j.val + 1 = x.val ∧ x.val + 2 < m + 3) ∨
            (x.val + 3 = m + 3 ∧
              (j.val + 2 = m + 3 ∨ j.val + 1 = m + 3)) ∨
            (j.val + 3 = m + 3 ∧
              (x.val + 2 = m + 3 ∨ x.val + 1 = m + 3))) := by
          simp [j]
          omega
        rw [dynkinCartanEntry, if_neg hx.1, if_neg hadj]
        simp
      rw [hsupp, Finset.prod_pair (by simp [j, s])] at hj
      have hdiag : dynkinCartanEntry ⟨.D, m + 3⟩ j j = 2 := by
        simp [dynkinCartanEntry]
      have hedge : dynkinCartanEntry ⟨.D, m + 3⟩ s j = -1 := by
        simp [dynkinCartanEntry, s, j]
      rw [hdiag, hedge] at hj
      have heq : (t j) ^ 2 * (t s)⁻¹ = 1 := by
        simpa [zpow_ofNat] using hj
      have hcoord : (t j) ^ 2 = t s := mul_inv_eq_one.mp heq
      rw [if_pos rfl, one_mul]
      have htns : tn 1 = t s := by
        simp only [tn, dif_pos (by omega : 1 < m + 1)]
        apply congrArg t
        apply Fin.ext
        rfl
      rw [htns]
      exact hcoord
    · let p : Fin (m + 3) := ⟨i - 1, by omega⟩
      let s : Fin (m + 3) := ⟨i + 1, by omega⟩
      have hj := h j
      have hsupp :
          (∏ x, t x ^ dynkinCartanEntry ⟨.D, m + 3⟩ x j) =
            ∏ x ∈ ({p, j, s} : Finset (Fin (m + 3))),
              t x ^ dynkinCartanEntry ⟨.D, m + 3⟩ x j := by
        apply prod_eq_support
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        have hxp : x.val ≠ i - 1 := by
          intro hxval
          apply hx.1
          apply Fin.ext
          simpa [p] using hxval
        have hxs : x.val ≠ i + 1 := by
          intro hxval
          apply hx.2.2
          apply Fin.ext
          simpa [s] using hxval
        have hadj : ¬(
            (x.val + 1 = j.val ∧ j.val + 2 < m + 3) ∨
            (j.val + 1 = x.val ∧ x.val + 2 < m + 3) ∨
            (x.val + 3 = m + 3 ∧
              (j.val + 2 = m + 3 ∨ j.val + 1 = m + 3)) ∨
            (j.val + 3 = m + 3 ∧
              (x.val + 2 = m + 3 ∨ x.val + 1 = m + 3))) := by
          simp [j]
          omega
        rw [dynkinCartanEntry, if_neg hx.2.1, if_neg hadj]
        simp
      have hpj : p ≠ j := by
        intro hpj
        have := congrArg Fin.val hpj
        simp [p, j] at this
        omega
      have hps : p ≠ s := by
        intro hps
        have := congrArg Fin.val hps
        simp [p, s] at this
      have hjs : j ≠ s := by
        intro hjs
        have := congrArg Fin.val hjs
        simp [j, s] at this
      rw [hsupp, Finset.prod_insert (by simp [hpj, hps]),
        Finset.prod_pair hjs] at hj
      have hdiag : dynkinCartanEntry ⟨.D, m + 3⟩ j j = 2 := by
        simp [dynkinCartanEntry]
      have hpred : dynkinCartanEntry ⟨.D, m + 3⟩ p j = -1 := by
        simp [dynkinCartanEntry, p, j]
        omega
      have hsucc : dynkinCartanEntry ⟨.D, m + 3⟩ s j = -1 := by
        simp [dynkinCartanEntry, s, j]
        omega
      rw [hpred, hdiag, hsucc] at hj
      have heq : (t p)⁻¹ * (t j) ^ 2 * (t s)⁻¹ = 1 := by
        simpa [zpow_ofNat, mul_assoc] using hj
      have hcoord : (t j) ^ 2 = t p * t s := by
        calc
          (t j) ^ 2 = t p * ((t p)⁻¹ * (t j) ^ 2 * (t s)⁻¹) * t s := by
            group
          _ = t p * t s := by rw [heq]; simp
      have htnp : tn (i - 1) = t p := by
        simp only [tn, dif_pos (by omega : i - 1 < m + 1)]
        apply congrArg t
        apply Fin.ext
        rfl
      have htns : tn (i + 1) = t s := by
        simp only [tn, dif_pos (by omega : i + 1 < m + 1)]
        apply congrArg t
        apply Fin.ext
        rfl
      rw [if_neg hi0, htnp, htns]
      exact hcoord
  let p : Fin (m + 3) := ⟨m - 1, by omega⟩
  let j : Fin (m + 3) := ⟨m, by omega⟩
  have hbranch : tn m ^ 2 = tn (m - 1) * t u * t v := by
    have hj := h j
    have hsupp :
        (∏ x, t x ^ dynkinCartanEntry ⟨.D, m + 3⟩ x j) =
          ∏ x ∈ ({p, j, u, v} : Finset (Fin (m + 3))),
            t x ^ dynkinCartanEntry ⟨.D, m + 3⟩ x j := by
      apply prod_eq_support
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      have hxp : x.val ≠ m - 1 := by
        intro hxval
        apply hx.1
        apply Fin.ext
        simpa [p] using hxval
      have hxj : x.val ≠ m := by
        intro hxval
        apply hx.2.1
        apply Fin.ext
        simpa [j] using hxval
      have hxu : x.val ≠ m + 1 := by
        intro hxval
        apply hx.2.2.1
        apply Fin.ext
        simpa [u] using hxval
      have hxv : x.val ≠ m + 2 := by
        intro hxval
        apply hx.2.2.2
        apply Fin.ext
        simpa [v] using hxval
      have hadj : ¬(
          (x.val + 1 = j.val ∧ j.val + 2 < m + 3) ∨
          (j.val + 1 = x.val ∧ x.val + 2 < m + 3) ∨
          (x.val + 3 = m + 3 ∧
            (j.val + 2 = m + 3 ∨ j.val + 1 = m + 3)) ∨
          (j.val + 3 = m + 3 ∧
            (x.val + 2 = m + 3 ∨ x.val + 1 = m + 3))) := by
        simp [j]
        omega
      rw [dynkinCartanEntry, if_neg hx.2.1, if_neg hadj]
      simp
    have hpj : p ≠ j := by intro h; have := congrArg Fin.val h; simp [p, j] at this; omega
    have hpu : p ≠ u := by intro h; have := congrArg Fin.val h; simp [p, u] at this
    have hpv : p ≠ v := by intro h; have := congrArg Fin.val h; simp [p, v] at this; omega
    have hju : j ≠ u := by intro h; have := congrArg Fin.val h; simp [j, u] at this
    have hjv : j ≠ v := by intro h; have := congrArg Fin.val h; simp [j, v] at this
    have huv : u ≠ v := by intro h; have := congrArg Fin.val h; simp [u, v] at this
    rw [hsupp, Finset.prod_insert (by simp [hpj, hpu, hpv]),
      Finset.prod_insert (by simp [hju, hjv]), Finset.prod_pair huv] at hj
    have hep : dynkinCartanEntry ⟨.D, m + 3⟩ p j = -1 := by
      simp [dynkinCartanEntry, p, j]
      omega
    have hej : dynkinCartanEntry ⟨.D, m + 3⟩ j j = 2 := by simp [dynkinCartanEntry]
    have heu : dynkinCartanEntry ⟨.D, m + 3⟩ u j = -1 := by
      simp [dynkinCartanEntry, u, j]
    have hev : dynkinCartanEntry ⟨.D, m + 3⟩ v j = -1 := by
      simp [dynkinCartanEntry, v, j]
    rw [hep, hej, heu, hev] at hj
    have heq : (t p)⁻¹ * (t j) ^ 2 * ((t u)⁻¹ * (t v)⁻¹) = 1 := by
      simpa [zpow_ofNat, mul_assoc] using hj
    have hcoord : (t j) ^ 2 = t p * t u * t v := by
      have hmul := congrArg (fun z : kˣ => t p * z * t u * t v) heq
      group at hmul
      rw [zpow_neg_one, zpow_neg_one] at hmul
      calc
        (t j) ^ 2 = (t j) ^ 2 * ((t u)⁻¹ * t u) * ((t v)⁻¹ * t v) := by simp
        _ = (t j) ^ 2 * (t u)⁻¹ * (t v)⁻¹ * t u * t v := by ac_rfl
        _ = t p * t u * t v := hmul
    have htj : tn m = t j := by
      simp only [tn, dif_pos (by omega : m < m + 1)]
      apply congrArg t
      apply Fin.ext
      rfl
    have htnp : tn (m - 1) = t p := by
      simp only [tn, dif_pos (by omega : m - 1 < m + 1)]
      apply congrArg t
      apply Fin.ext
      rfl
    rw [htj, htnp]
    exact hcoord
  have hu : (t u) ^ 2 = tn m := by
    have huEq := h u
    have hsupp :
        (∏ x, t x ^ dynkinCartanEntry ⟨.D, m + 3⟩ x u) =
          ∏ x ∈ ({j, u} : Finset (Fin (m + 3))),
            t x ^ dynkinCartanEntry ⟨.D, m + 3⟩ x u := by
      apply prod_eq_support
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      have hxj : x.val ≠ m := by
        intro hxval
        apply hx.1
        apply Fin.ext
        simpa [j] using hxval
      have hxu : x.val ≠ m + 1 := by
        intro hxval
        apply hx.2
        apply Fin.ext
        simpa [u] using hxval
      have hadj : ¬(
          (x.val + 1 = u.val ∧ u.val + 2 < m + 3) ∨
          (u.val + 1 = x.val ∧ x.val + 2 < m + 3) ∨
          (x.val + 3 = m + 3 ∧
            (u.val + 2 = m + 3 ∨ u.val + 1 = m + 3)) ∨
          (u.val + 3 = m + 3 ∧
            (x.val + 2 = m + 3 ∨ x.val + 1 = m + 3))) := by
        simp [u]
        omega
      rw [dynkinCartanEntry, if_neg hx.2, if_neg hadj]
      simp
    rw [hsupp, Finset.prod_pair (by simp [j, u])] at huEq
    have hej : dynkinCartanEntry ⟨.D, m + 3⟩ j u = -1 := by
      simp [dynkinCartanEntry, j, u]
    have heu : dynkinCartanEntry ⟨.D, m + 3⟩ u u = 2 := by simp [dynkinCartanEntry]
    rw [hej, heu] at huEq
    have heq : (t j)⁻¹ * (t u) ^ 2 = 1 := by simpa [zpow_ofNat] using huEq
    have hcoord : (t u) ^ 2 = t j := by symm; exact inv_mul_eq_one.mp heq
    have htj : tn m = t j := by
      simp only [tn, dif_pos (by omega : m < m + 1)]
      apply congrArg t
      apply Fin.ext
      rfl
    rw [htj]
    exact hcoord
  have hv : (t v) ^ 2 = tn m := by
    have hvEq := h v
    have hsupp :
        (∏ x, t x ^ dynkinCartanEntry ⟨.D, m + 3⟩ x v) =
          ∏ x ∈ ({j, v} : Finset (Fin (m + 3))),
            t x ^ dynkinCartanEntry ⟨.D, m + 3⟩ x v := by
      apply prod_eq_support
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      have hxj : x.val ≠ m := by
        intro hxval
        apply hx.1
        apply Fin.ext
        simpa [j] using hxval
      have hxv : x.val ≠ m + 2 := by
        intro hxval
        apply hx.2
        apply Fin.ext
        simpa [v] using hxval
      have hadj : ¬(
          (x.val + 1 = v.val ∧ v.val + 2 < m + 3) ∨
          (v.val + 1 = x.val ∧ x.val + 2 < m + 3) ∨
          (x.val + 3 = m + 3 ∧
            (v.val + 2 = m + 3 ∨ v.val + 1 = m + 3)) ∨
          (v.val + 3 = m + 3 ∧
            (x.val + 2 = m + 3 ∨ x.val + 1 = m + 3))) := by
        simp [v]
        omega
      rw [dynkinCartanEntry, if_neg hx.2, if_neg hadj]
      simp
    rw [hsupp, Finset.prod_pair (by simp [j, v])] at hvEq
    have hej : dynkinCartanEntry ⟨.D, m + 3⟩ j v = -1 := by
      simp [dynkinCartanEntry, j, v]
    have hev : dynkinCartanEntry ⟨.D, m + 3⟩ v v = 2 := by simp [dynkinCartanEntry]
    rw [hej, hev] at hvEq
    have heq : (t j)⁻¹ * (t v) ^ 2 = 1 := by simpa [zpow_ofNat] using hvEq
    have hcoord : (t v) ^ 2 = t j := by symm; exact inv_mul_eq_one.mp heq
    have htj : tn m = t j := by
      simp only [tn, dif_pos (by omega : m < m + 1)]
      apply congrArg t
      apply Fin.ext
      rfl
    rw [htj]
    exact hcoord
  obtain ⟨ω, hω, ht, hu', hv'⟩ :=
    typeDForkCartanKernel m hm tn (t u) (t v) hchain hbranch hu hv
  refine ⟨ω, hω, ?_, hu', ?_⟩
  · intro i
    have hitn : tn i.val = t ⟨i.val, by omega⟩ := by
      simp only [tn, dif_pos i.isLt]
    simpa [hitn] using ht i.val (by omega)
  · simpa [u, v] using hv'

open scoped BigOperators

/-- The common multiplicative kernel of the standard type `E6` Cartan
relations, with coordinates arranged as `0—1—2—3` and `2—4—5`. -/
public theorem dynkinCartanRelationKernel_E6
    {k : Type*} [Field k] (t : Fin 6 → kˣ)
    (h : ∀ j, (∏ i, t i ^ dynkinCartanEntry ⟨.E6, 6⟩ i j) = 1) :
    ∃ ω : kˣ, ω ^ 3 = 1 ∧
      t 0 = ω ∧ t 1 = ω ^ 2 ∧ t 2 = 1 ∧ t 3 = 1 ∧
      t 4 = ω ∧ t 5 = ω ^ 2 := by
  have h0 := h (0 : Fin 6)
  have h1 := h (1 : Fin 6)
  have h2 := h (2 : Fin 6)
  have h3 := h (3 : Fin 6)
  have h4 := h (4 : Fin 6)
  have h5 := h (5 : Fin 6)
  simp [dynkinCartanEntry, Fin.prod_univ_succ] at h0 h1 h2 h3 h4 h5
  have ht1 : t 1 = t 0 ^ 2 := by
    exact (mul_inv_eq_one.mp h0).symm
  have h1' : t 0 ^ 3 * (t 2)⁻¹ = 1 := by
    calc
      t 0 ^ 3 * (t 2)⁻¹ = (t 0)⁻¹ * (t 1 ^ 2 * (t 2)⁻¹) := by
        rw [ht1]
        group
      _ = 1 := h1
  have ht2 : t 2 = t 0 ^ 3 := (mul_inv_eq_one.mp h1').symm
  have ht3sq : t 3 ^ 2 = t 0 ^ 3 := by
    have h3' : t 3 ^ 2 = t 2 := (inv_mul_eq_one.mp h3).symm
    exact h3'.trans ht2
  have h2' : t 0 ^ 4 * (t 3)⁻¹ * (t 4)⁻¹ = 1 := by
    calc
      t 0 ^ 4 * (t 3)⁻¹ * (t 4)⁻¹ =
          (t 1)⁻¹ * (t 2 ^ 2 * ((t 3)⁻¹ * (t 4)⁻¹)) := by
        rw [ht1, ht2]
        group
      _ = 1 := h2
  have ht4 : t 4 = t 0 ^ 4 * (t 3)⁻¹ := (mul_inv_eq_one.mp h2').symm
  have h4' : t 4 ^ 2 * (t 2)⁻¹ * (t 5)⁻¹ = 1 := by
    calc
      t 4 ^ 2 * (t 2)⁻¹ * (t 5)⁻¹ =
          (t 2)⁻¹ * (t 4 ^ 2 * (t 5)⁻¹) := by ac_rfl
      _ = 1 := h4
  have ht5 : t 5 = t 4 ^ 2 * (t 2)⁻¹ := (mul_inv_eq_one.mp h4').symm
  have ht5a : t 5 = t 0 ^ 2 := by
    calc
      t 5 = t 4 ^ 2 * (t 2)⁻¹ := ht5
      _ = (t 0 ^ 4 * (t 3)⁻¹) ^ 2 * (t 0 ^ 3)⁻¹ := by rw [ht4, ht2]
      _ = t 0 ^ 8 * ((t 3) ^ 2)⁻¹ * (t 0 ^ 3)⁻¹ := by
        simp [mul_pow]
        group
      _ = t 0 ^ 8 * (t 0 ^ 3)⁻¹ * (t 0 ^ 3)⁻¹ := by rw [ht3sq]
      _ = t 0 ^ 2 := by group
  have h5' : t 5 ^ 2 = t 4 := (inv_mul_eq_one.mp h5).symm
  have h3inv : (t 3)⁻¹ = 1 := by
    have heq : t 0 ^ 4 = t 0 ^ 4 * (t 3)⁻¹ := by
      calc
        t 0 ^ 4 = t 5 ^ 2 := by rw [ht5a]; group
        _ = t 4 := h5'
        _ = t 0 ^ 4 * (t 3)⁻¹ := ht4
    apply mul_left_cancel (a := t 0 ^ 4)
    simpa using heq.symm
  have ht3 : t 3 = 1 := inv_eq_one.mp h3inv
  have ht0 : t 0 ^ 3 = 1 := by
    have := ht3sq
    simp [ht3] at this
    exact this.symm
  refine ⟨t 0, ht0, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact ht1
  · rw [ht2, ht0]
  · exact ht3
  · rw [ht4, ht3]
    simp only [inv_one, mul_one]
    calc
      t 0 ^ 4 = t 0 ^ 3 * t 0 := by group
      _ = t 0 := by rw [ht0]; simp
  · exact ht5a

open scoped BigOperators

/-! The `G₂` Cartan relation matrix has trivial multiplicative kernel over a
field.  This is the first concrete type-specific kernel calculation needed by
the center table; the group-model and torus-generation hypotheses remain
separate interfaces. -/
public theorem dynkinCartanRelationKernel_G2
    {k : Type*} [Field k] (t : Fin 2 → kˣ)
    (h : ∀ j, (∏ i, t i ^ dynkinCartanEntry ⟨.G2, 2⟩ i j) = 1) :
    ∀ i, t i = 1 := by
  have h0 := h (0 : Fin 2)
  have h1 := h (1 : Fin 2)
  simp [dynkinCartanEntry] at h0 h1
  have hx : t 0 = t 1 ^ (2 : ℤ) := by
    apply inv_mul_eq_one.mp
    simpa [mul_comm] using h1
  have hy : t 1 = 1 := by
    have h0' := h0
    rw [hx] at h0'
    have hrel : t 1 ^ (4 : ℤ) * t 1 ^ (-3 : ℤ) = 1 := by
      calc
        t 1 ^ (4 : ℤ) * t 1 ^ (-3 : ℤ) =
            (t 1 ^ (2 : ℤ)) ^ (2 : ℤ) * (t 1 ^ (3 : ℤ))⁻¹ := by
              rw [← zpow_mul, ← zpow_neg]
              norm_num
        _ = 1 := by simpa [zpow_neg] using h0'
    have hrel' : t 1 ^ ((4 : ℤ) + (-3 : ℤ)) = 1 := by
      rw [zpow_add]
      exact hrel
    norm_num at hrel'
    simpa using hrel'
  intro i
  fin_cases i
  · simpa [hy] using hx
  · exact hy

open scoped BigOperators
open Matrix

private lemma linComb_mul
    {n : ℕ} {G : Type*} [CommGroup G]
    (A : Matrix (Fin n) (Fin n) ℤ) (B : Matrix (Fin n) (Fin n) ℤ)
    (v : Fin n → Additive G) (k : Fin n) :
    (∑ l, B k l • (∑ i, A i l • v i)) =
      ∑ i, (∑ l, B k l * A i l) • v i := by
  classical
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [smul_smul]
  rw [← Finset.sum_smul]

private lemma zero_of_left_inverse_cartan_relation
    {n : ℕ} {G : Type*} [CommGroup G]
    (A B : Matrix (Fin n) (Fin n) ℤ)
    (hBA : B * A.transpose = 1)
    (v : Fin n → Additive G)
    (h : ∀ j, (∑ i, A i j • v i) = 0) :
    ∀ k, v k = 0 := by
  intro k
  have hzero : (∑ l, B k l • (∑ i, A i l • v i)) = 0 := by
    simp_rw [h]
    simp
  rw [linComb_mul A B v k] at hzero
  have hcoeff : ∀ i, (∑ l, B k l * A i l) = if k = i then 1 else 0 := by
    intro i
    have hi := congrFun (congrFun hBA k) i
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hi
  simp_rw [hcoeff] at hzero
  simpa using hzero

open scoped BigOperators
open Matrix

private def cartanE8 : Matrix (Fin 8) (Fin 8) ℤ :=
  fun i j => dynkinCartanEntry ⟨.E8, 8⟩ i j

private def inverseTransposeE8 : Matrix (Fin 8) (Fin 8) ℤ :=
  !![4, 7, 10, 5, 8, 6, 4, 2;
     7, 14, 20, 10, 16, 12, 8, 4;
     10, 20, 30, 15, 24, 18, 12, 6;
     5, 10, 15, 8, 12, 9, 6, 3;
     8, 16, 24, 12, 20, 15, 10, 5;
     6, 12, 18, 9, 15, 12, 8, 4;
     4, 8, 12, 6, 10, 8, 6, 3;
     2, 4, 6, 3, 5, 4, 3, 2]

set_option maxHeartbeats 800000 in
private lemma inverseTransposeE8_mul_cartanE8_transpose :
    inverseTransposeE8 * cartanE8.transpose = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [inverseTransposeE8, cartanE8, dynkinCartanEntry,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> simp

public theorem dynkinCartanRelationKernel_E8
    {k : Type*} [Field k] (t : Fin 8 → kˣ)
    (h : ∀ j, (∏ i, t i ^ dynkinCartanEntry ⟨.E8, 8⟩ i j) = 1) :
    ∀ i, t i = 1 := by
  let v : Fin 8 → Additive kˣ := fun i => Additive.ofMul (t i)
  have hv : ∀ j, (∑ i, cartanE8 i j • v i) = 0 := by
    intro j
    have hj := congrArg Additive.ofMul (h j)
    fin_cases j <;>
      convert hj using 1 <;>
        simp [v, cartanE8, dynkinCartanEntry, Fin.sum_univ_succ] <;> rfl
  have hz := zero_of_left_inverse_cartan_relation cartanE8 inverseTransposeE8
    inverseTransposeE8_mul_cartanE8_transpose v hv
  intro i
  have hi := hz i
  exact Additive.ofMul.injective (by simpa [v] using hi)

open scoped BigOperators
open Matrix

private def cartanF4 : Matrix (Fin 4) (Fin 4) ℤ :=
  fun i j => dynkinCartanEntry ⟨.F4, 4⟩ i j

private def inverseTransposeF4 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, 3, 2, 1; 3, 6, 4, 2; 4, 8, 6, 3; 2, 4, 3, 2]

private lemma inverseTransposeF4_mul_cartanF4_transpose :
    inverseTransposeF4 * cartanF4.transpose = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [inverseTransposeF4, cartanF4, dynkinCartanEntry,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> simp

public theorem dynkinCartanRelationKernel_F4
    {k : Type*} [Field k] (t : Fin 4 → kˣ)
    (h : ∀ j, (∏ i, t i ^ dynkinCartanEntry ⟨.F4, 4⟩ i j) = 1) :
    ∀ i, t i = 1 := by
  let v : Fin 4 → Additive kˣ := fun i => Additive.ofMul (t i)
  have hv : ∀ j, (∑ i, cartanF4 i j • v i) = 0 := by
    intro j
    have hj := congrArg Additive.ofMul (h j)
    fin_cases j <;>
      convert hj using 1 <;>
        simp [v, cartanF4, dynkinCartanEntry, Fin.sum_univ_succ] <;> rfl
  have hz := zero_of_left_inverse_cartan_relation cartanF4 inverseTransposeF4
    inverseTransposeF4_mul_cartanF4_transpose v hv
  intro i
  have hi := hz i
  exact Additive.ofMul.injective (by simpa [v] using hi)

open scoped BigOperators
open Matrix

public theorem smul_zero_of_left_inverse_cartan_relation
    {n : ℕ} {G : Type*} [CommGroup G]
    (d : ℤ) (A B : Matrix (Fin n) (Fin n) ℤ)
    (hBA : B * A.transpose = d • (1 : Matrix (Fin n) (Fin n) ℤ))
    (v : Fin n → Additive G)
    (h : ∀ j, (∑ i, A i j • v i) = 0) :
    ∀ k, d • v k = 0 := by
  intro k
  have hzero : (∑ l, B k l • (∑ i, A i l • v i)) = 0 := by
    simp_rw [h]
    simp
  have hlin : (∑ l, B k l • (∑ i, A i l • v i)) =
      ∑ i, (∑ l, B k l * A i l) • v i := by
    classical
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    simp_rw [smul_smul]
    rw [← Finset.sum_smul]
  rw [hlin] at hzero
  have hcoeff : ∀ i, (∑ l, B k l * A i l) =
      if k = i then d else 0 := by
    intro i
    have hi := congrFun (congrFun hBA k) i
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hi
  simp_rw [hcoeff] at hzero
  simpa using hzero

open scoped BigOperators
open Matrix

private def cartanE6 : Matrix (Fin 6) (Fin 6) ℤ :=
  fun i j => dynkinCartanEntry ⟨.E6, 6⟩ i j

private def inverseTransposeE6 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![4, 5, 6, 3, 4, 2;
     5, 10, 12, 6, 8, 4;
     6, 12, 18, 9, 12, 6;
     3, 6, 9, 6, 6, 3;
     4, 8, 12, 6, 10, 5;
     2, 4, 6, 3, 5, 4]

private lemma inverseTransposeE6_mul_cartanE6_transpose :
    inverseTransposeE6 * cartanE6.transpose = (3 : ℤ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [inverseTransposeE6, cartanE6, dynkinCartanEntry,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> simp

public theorem dynkinCartanRelationKernel_E6_cube
    {k : Type*} [Field k] (t : Fin 6 → kˣ)
    (h : ∀ j, (∏ i, t i ^ dynkinCartanEntry ⟨.E6, 6⟩ i j) = 1) :
    ∀ i, t i ^ (3 : ℤ) = 1 := by
  let v : Fin 6 → Additive kˣ := fun i => Additive.ofMul (t i)
  have hv : ∀ j, (∑ i, cartanE6 i j • v i) = 0 := by
    intro j
    have hj := congrArg Additive.ofMul (h j)
    fin_cases j <;>
      convert hj using 1 <;>
        simp [v, cartanE6, dynkinCartanEntry, Fin.sum_univ_succ,
          Fin.prod_univ_succ] <;> rfl
  have hz := smul_zero_of_left_inverse_cartan_relation 3 cartanE6
    inverseTransposeE6 inverseTransposeE6_mul_cartanE6_transpose v hv
  intro i
  have hi := hz i
  have hi' := congrArg Additive.toMul hi
  simpa [v] using hi'

open scoped BigOperators
open Matrix

private def cartanE7 : Matrix (Fin 7) (Fin 7) ℤ :=
  fun i j => dynkinCartanEntry ⟨.E7, 7⟩ i j

private def inverseTransposeE7 : Matrix (Fin 7) (Fin 7) ℤ :=
  !![4, 6, 8, 4, 6, 4, 2;
     6, 12, 16, 8, 12, 8, 4;
     8, 16, 24, 12, 18, 12, 6;
     4, 8, 12, 7, 9, 6, 3;
     6, 12, 18, 9, 15, 10, 5;
     4, 8, 12, 6, 10, 8, 4;
     2, 4, 6, 3, 5, 4, 3]

private lemma inverseTransposeE7_mul_cartanE7_transpose :
    inverseTransposeE7 * cartanE7.transpose = (2 : ℤ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [inverseTransposeE7, cartanE7, dynkinCartanEntry,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> simp

public theorem dynkinCartanRelationKernel_E7_square
    {k : Type*} [Field k] (t : Fin 7 → kˣ)
    (h : ∀ j, (∏ i, t i ^ dynkinCartanEntry ⟨.E7, 7⟩ i j) = 1) :
    ∀ i, t i ^ (2 : ℤ) = 1 := by
  let v : Fin 7 → Additive kˣ := fun i => Additive.ofMul (t i)
  have hv : ∀ j, (∑ i, cartanE7 i j • v i) = 0 := by
    intro j
    have hj := congrArg Additive.ofMul (h j)
    fin_cases j <;>
      convert hj using 1 <;>
        simp [v, cartanE7, dynkinCartanEntry, Fin.sum_univ_succ,
          Fin.prod_univ_succ] <;> rfl
  have hz := smul_zero_of_left_inverse_cartan_relation 2 cartanE7
    inverseTransposeE7 inverseTransposeE7_mul_cartanE7_transpose v hv
  intro i
  have hi := hz i
  have hi' := congrArg Additive.toMul hi
  simpa [v] using hi'

open scoped BigOperators

/-- The common multiplicative kernel of the standard type `E7` Cartan
relations, with its nontrivial parameter in coordinates 3, 4, and 6. -/
public theorem dynkinCartanRelationKernel_E7
    {k : Type*} [Field k] (t : Fin 7 → kˣ)
    (h : ∀ j, (∏ i, t i ^ dynkinCartanEntry ⟨.E7, 7⟩ i j) = 1) :
    ∃ ω : kˣ, ω ^ 2 = 1 ∧
      ∀ i, t i = if i.val = 3 ∨ i.val = 4 ∨ i.val = 6 then ω else 1 := by
  let v : Fin 7 → Additive kˣ := fun i => Additive.ofMul (t i)
  have hv : ∀ j,
      (∑ i, dynkinCartanEntry ⟨.E7, 7⟩ i j • v i) = 0 := by
    intro j
    have hj := congrArg Additive.ofMul (h j)
    fin_cases j <;>
      convert hj using 1 <;>
        simp [v, dynkinCartanEntry, Fin.sum_univ_succ] <;> rfl
  have htwo : ∀ i, (2 : ℤ) • v i = 0 := by
    intro i
    have hi := congrArg Additive.ofMul (dynkinCartanRelationKernel_E7_square t h i)
    convert hi using 1 <;> simp [v]
    rfl
  have h1 : v 1 = 0 := by
    have hcol := hv 0
    simp [dynkinCartanEntry, Fin.sum_univ_succ, htwo] at hcol
    exact hcol
  have h02 : v 0 + v 2 = 0 := by
    have hcol := hv 1
    simp [dynkinCartanEntry, Fin.sum_univ_succ, htwo] at hcol
    calc
      v 0 + v 2 = v 2 + v 0 := add_comm _ _
      _ = 0 := by simpa using congrArg Neg.neg hcol
  have h2 : v 2 = 0 := by
    have hcol := hv 3
    simp [dynkinCartanEntry, Fin.sum_univ_succ, htwo] at hcol
    exact hcol
  have h0 : v 0 = 0 := by
    rw [h2, add_zero] at h02
    exact h02
  have h34 : v 3 + v 4 = 0 := by
    have hcol := hv 2
    simp [dynkinCartanEntry, Fin.sum_univ_succ, htwo, h1] at hcol
    calc
      v 3 + v 4 = v 4 + v 3 := add_comm _ _
      _ = 0 := by simpa using congrArg Neg.neg hcol
  have h5 : v 5 = 0 := by
    have hcol := hv 4
    simp [dynkinCartanEntry, Fin.sum_univ_succ, htwo, h2] at hcol
    exact hcol
  have h46 : v 4 + v 6 = 0 := by
    have hcol := hv 5
    simp [dynkinCartanEntry, Fin.sum_univ_succ, htwo] at hcol
    calc
      v 4 + v 6 = v 6 + v 4 := add_comm _ _
      _ = 0 := by simpa using congrArg Neg.neg hcol
  have h4 : v 4 = v 3 := by
    have ht3 := htwo (3 : Fin 7)
    rw [two_zsmul] at ht3
    calc
      v 4 = -v 3 := eq_neg_of_add_eq_zero_right h34
      _ = v 3 := neg_eq_of_add_eq_zero_right ht3
  have h6 : v 6 = v 3 := by
    rw [h4] at h46
    have ht3 := htwo (3 : Fin 7)
    rw [two_zsmul] at ht3
    calc
      v 6 = -v 3 := eq_neg_of_add_eq_zero_right h46
      _ = v 3 := neg_eq_of_add_eq_zero_right ht3
  refine ⟨t 3, ?_, ?_⟩
  · have ht3 := htwo (3 : Fin 7)
    apply Additive.ofMul.injective
    simpa [v, two_zsmul, pow_two] using ht3
  · intro i
    fin_cases i <;>
      apply Additive.ofMul.injective <;>
      simp [v, h0, h1, h2, h4, h5, h6]

end Theory.AlgebraicGroup
