module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.GeneralizedRows.PowerData
public import Theory.GroupTheory.PrimeCyclicCoverage

/-!
# Powers on the actual ordinary conjugacy classes

Transport through the supplied class enumeration gives a power action on its
fifteen indices. Its multiplication law uses conjugacy of representatives,
not equality of the chosen group elements. Sylow conjugacy and the census show
that squaring fixes no class of order five or nineteen: otherwise the primitive
residue two would fuse every element of that prime order into a single class.

This is the group-theoretic input to compatible labels for Janko's ordinary
character calculation (J. Algebra 3 (1966), 147–186; Gorenstein, printed p.482).
No characters, recognition theorem, or model of the group are used.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
namespace PowerLabelConstruction
variable {G : Type*} [Group G] [Finite G] (c : OrdinaryClassData G)

@[expose] public noncomputable def idx (g : G) : Fin 15 := c.classes.symm (ConjClasses.mk g)
@[expose] public noncomputable def power (j : Fin 15) (n : ℕ) : Fin 15 := idx c (c.representatives j ^ n)

private theorem idx_rep (j : Fin 15) : idx c (c.representatives j) = j := by
  simp [idx, ← c.classes_eq]

private theorem rep_conj (g : G) : IsConj (c.representatives (idx c g)) g := by
  apply ConjClasses.mk_eq_mk_iff_isConj.mp
  rw [← c.classes_eq]
  exact c.classes.apply_symm_apply _

private theorem idx_conj {g h : G} (hc : IsConj g h) : idx c g = idx c h :=
  congrArg c.classes.symm (ConjClasses.mk_eq_mk_iff_isConj.mpr hc)

private theorem idx_order (g : G) : classOrder (idx c g) = orderOf g := by
  rw [← c.orders]
  obtain ⟨a, ha⟩ := rep_conj c g
  exact SemiconjBy.orderOf_eq (a : G) ha

private theorem idx_pow (g : G) (n : ℕ) : power c (idx c g) n = idx c (g ^ n) :=
  idx_conj c (IsConj.pow n (rep_conj c g))

public theorem power_order (j : Fin 15) (n : ℕ) :
    classOrder (power c j n) = classOrder j / Nat.gcd (classOrder j) n := by
  rw [power, idx_order, orderOf_pow, c.orders]

public theorem power_mul (j : Fin 15) (m n : ℕ) :
    power c (power c j m) n = power c j (m * n) := by
  change power c (idx c (c.representatives j ^ m)) n = _
  rw [idx_pow, ← pow_mul]
  rfl

public theorem power_mod (j : Fin 15) (n : ℕ) :
    power c j (n % classOrder j) = power c j n := by
  unfold power
  rw [← c.orders, pow_mod_orderOf]

@[simp] public theorem power_one (j : Fin 15) : power c j 1 = j := by
  simp [power, idx_rep]

@[simp] public theorem power_zero (j : Fin 15) : power c j 0 = 0 := by
  simpa [power, c.identity] using idx_rep c 0

private theorem power_two_pow_of_fixed (j : Fin 15) (hj : power c j 2 = j) (k : ℕ) :
    power c j (2 ^ k) = j := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← power_mul, ih, hj]

private theorem prime_coverage (horder : Nat.card G = 175560) (p : ℕ)
    (hp : p = 5 ∨ p = 19) (i j : Fin 15)
    (hi : classOrder i = p) (hj : classOrder j = p) :
    ∃ k : Fin p, power c i k = j := by
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> decide
  have hsq : ¬p ^ 2 ∣ Nat.card G := by
    rw [horder]
    rcases hp with rfl | rfl <;> decide
  obtain ⟨n, g, he⟩ := PrimeCyclicCoverage.exists_conjugate_pow_of_prime_sq_not_dvd
    hprime hsq ((c.orders i).trans hi) ((c.orders j).trans hj)
  refine ⟨⟨n % p, Nat.mod_lt _ hprime.pos⟩, ?_⟩
  change power c i (n % p) = j
  rw [← hi, power_mod]
  exact (idx_conj c (isConj_iff.mpr ⟨g, he.symm⟩)).trans (idx_rep c j)

public theorem square_ne (horder : Nat.card G = 175560) (j : Fin 15)
    (hj : classOrder j = 5 ∨ classOrder j = 19) : power c j 2 ≠ j := by
  intro he
  have hfixed := power_two_pow_of_fixed c j he
  have hgen5 : ∀ n : Fin 5, n ≠ 0 → ∃ k : Fin 4, 2 ^ (k : ℕ) % 5 = (n : ℕ) := by decide +kernel
  have hgen19 : ∀ n : Fin 19, n ≠ 0 → ∃ k : Fin 18, 2 ^ (k : ℕ) % 19 = (n : ℕ) := by decide +kernel
  have hfull (p : ℕ) (hp : p = 5 ∨ p = 19) (ho : classOrder j = p)
      (hgen : ∀ n : Fin p, (n : ℕ) ≠ 0 → ∃ k : ℕ, 2 ^ k % p = n)
      (i : Fin 15) (hi : classOrder i = p) : i = j := by
    obtain ⟨n, hn⟩ := prime_coverage c horder p hp j i ho hi
    have hn0 : (n : ℕ) ≠ 0 := by
      intro hn0
      have hz : i = 0 := by simpa [hn0] using hn.symm
      rw [hz] at hi
      rcases hp with rfl | rfl <;> norm_num [classOrder] at hi
    obtain ⟨k, hk⟩ := hgen n hn0
    rw [← hn, ← hk, ← ho, power_mod, hfixed]
  rcases hj with hj | hj
  · have hall := hfull 5 (Or.inl rfl) hj (fun n hn => by
      obtain ⟨k, hk⟩ := hgen5 n (by simpa using hn)
      exact ⟨k, hk⟩)
    have h3 := hall 3 rfl
    have h4 := hall 4 rfl
    exact (by decide : (3 : Fin 15) ≠ 4) (h3.trans h4.symm)
  · have hall := hfull 19 (Or.inr rfl) hj (fun n hn => by
      obtain ⟨k, hk⟩ := hgen19 n (by simpa using hn)
      exact ⟨k, hk⟩)
    have h12 := hall 12 rfl
    have h13 := hall 13 rfl
    exact (by decide : (12 : Fin 15) ≠ 13) (h12.trans h13.symm)
end PowerLabelConstruction
end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
