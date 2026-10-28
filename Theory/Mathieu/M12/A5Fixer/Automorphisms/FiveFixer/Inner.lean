module

public import Theory.Mathieu.M12.A5Fixer.Automorphisms.LocalInputs
public import Theory.Mathieu.M12.Properties.Transitivity
public import Theory.GroupTheory.SharpSetStabilizer

/-!
# The centralizer of the marked element of order five in M₁₂

Sharp five-transitivity makes evaluation at a moved point injective on the
centralizer: commuting elements with the same value there agree on its
five-element orbit. A concrete word of order ten commutes with the marked
five-element, and its powers reach all ten moved points. These powers therefore
exhaust the inner centralizer. The word's sixth power is the five-element, so
an automorphism fixing that element must fix the word and the whole centralizer.

The permutation identities and orbit checks are checked in the kernel. The
marked actors and their attribution come from `M12.SmallParabolicPair.Seeds`.
This is the inner part of the full-automorphism fixer calculation used for
Aschbacher–Smith 16.3.5, with source context 16.1.5(4) and 16.1.7(3f),
combined manuscript of 1 March 2004, printed pp.1171–1173 and 1178–1179.
It makes no assertion that the full fixer already has exponent ten.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12A5Fixer.Automorphisms
open M12SmallPair
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

/-- A concrete cyclic generator for the inner centralizer of `fiveElement`. -/
noncomputable def fiveCentralizerGenerator : M12 :=
  fiveElement * (cubicActor * rightI * cubicActor * movingActor * movingActor *
    cubicActor * movingActor * cubicActor * movingActor * rightI * cubicActor)

private theorem generator_commute : Commute fiveCentralizerGenerator fiveElement := by
  change fiveCentralizerGenerator * fiveElement = fiveElement * fiveCentralizerGenerator
  decide +kernel

/-- The centralizer generator has tenth power one. -/
theorem fiveCentralizerGenerator_pow_ten : fiveCentralizerGenerator ^ 10 = 1 := by
  decide +kernel

/-- Its sixth power is the marked five-element. -/
theorem fiveCentralizerGenerator_pow_six : fiveCentralizerGenerator ^ 6 = fiveElement := by
  decide +kernel

private theorem centralizer_ext {g h : M12}
    (hg : Commute g fiveElement) (hh : Commute h fiveElement)
    (h0 : g • (0 : Fin 12) = h • (0 : Fin 12)) : g = h := by
  let e : Fin 5 ↪ Fin 12 :=
    ⟨fun i => (fiveElement ^ i.val) • (0 : Fin 12), by decide +kernel⟩
  obtain ⟨k, _, hk⟩ := m12_isSharplyFivePretransitive.existsUnique_smul_eq e (h • e)
  apply (hk g ?_).trans (hk h rfl).symm
  apply Function.Embedding.ext
  intro i
  change g • ((fiveElement ^ i.val) • (0 : Fin 12)) =
    h • ((fiveElement ^ i.val) • (0 : Fin 12))
  rw [← mul_smul, (hg.pow_right i.val).eq, mul_smul, h0,
    ← mul_smul, ← (hh.pow_right i.val).eq, mul_smul]

/-- Every element of the inner centralizer is one of these ten powers. -/
theorem fiveCentralizer_eq_power {g : M12} (hg : Commute g fiveElement) :
    ∃ n : Fin 10, g = fiveCentralizerGenerator ^ n.val := by
  have hm : fiveElement • (g • (0 : Fin 12)) ≠ g • (0 : Fin 12) := by
    rw [← mul_smul, hg.symm.eq, mul_smul]
    exact (MulAction.injective g).ne (by decide +kernel)
  have hc : ∀ x : Fin 12, fiveElement • x ≠ x →
      ∃ n : Fin 10, (fiveCentralizerGenerator ^ n.val) • (0 : Fin 12) = x := by
    decide +kernel
  obtain ⟨n, hn⟩ := hc (g • (0 : Fin 12)) hm
  exact ⟨n, centralizer_ext hg (generator_commute.pow_left n.val) hn.symm⟩

/-- The inner centralizer has exponent dividing ten. -/
theorem fiveCentralizer_pow_ten {g : M12} (hg : Commute g fiveElement) :
    g ^ 10 = 1 := by
  obtain ⟨n, rfl⟩ := fiveCentralizer_eq_power hg
  rw [← pow_mul, Nat.mul_comm, pow_mul, fiveCentralizerGenerator_pow_ten, one_pow]

/-- The full automorphism fixer of `fiveElement` fixes its inner centralizer pointwise. -/
theorem fiveCentralizer_fixed (a : MulAut M12) (ha : a fiveElement = fiveElement)
    {g : M12} (hg : Commute g fiveElement) : a g = g := by
  have hc : Commute (a fiveCentralizerGenerator) fiveElement := by
    simpa only [ha] using generator_commute.map a
  obtain ⟨n, hn⟩ := fiveCentralizer_eq_power hc
  have h6 : (fiveCentralizerGenerator ^ n.val) ^ 6 = fiveElement := by
    rw [← hn, ← map_pow, fiveCentralizerGenerator_pow_six, ha]
  have h5 : (fiveCentralizerGenerator ^ n.val) ^ 5 ≠ 1 := by
    rw [← hn, ← map_pow]
    intro he
    have hbad : fiveCentralizerGenerator ^ 5 ≠ 1 := by decide +kernel
    exact hbad (a.injective (he.trans (map_one a).symm))
  have ht : ∀ i : Fin 10, (fiveCentralizerGenerator ^ i.val) ^ 6 = fiveElement →
      (fiveCentralizerGenerator ^ i.val) ^ 5 ≠ 1 →
        fiveCentralizerGenerator ^ i.val = fiveCentralizerGenerator := by
    decide +kernel
  have hgen : a fiveCentralizerGenerator = fiveCentralizerGenerator := hn.trans (ht n h6 h5)
  obtain ⟨i, rfl⟩ := fiveCentralizer_eq_power hg
  rw [map_pow, hgen]

end Sporadic.Mathieu.M12A5Fixer.Automorphisms
