module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Odd-prime extraction and ambient transport for the outer actor

The r-th power kernel in a cyclic group of order p+1 has order r whenever
r divides p+1. For p > 1 congruent to one modulo four, the odd number
(p+1)/2 has a prime divisor. Its prime kernel is preserved by every
normalizer of the cyclic group and inherits inversion.

The second lemma transports a model subgroup through an actual isomorphism
from a normal subgroup of G. It retains the entire ambient normalizing
action, including elements outside the normal subgroup. These are the
extraction steps for Aschbacher--Smith E.1.14(7), printed p.214; the matrix
subgroups and actor placement are separate inputs.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup

variable {G : Type*} [Group G] [Finite G]

/-- Extract a nontrivial odd-prime subgroup with the same normalization and inversion. -/
theorem odd_subgroup_of_cyclic (D R : Subgroup G) [IsCyclic D]
    {p : ℕ} (hp : 1 < p) (hm : p % 4 = 1) (hc : Nat.card D = p + 1)
    (z : G) (hinv : ∀ x ∈ D, z * x * z⁻¹ = x⁻¹)
    (hn : R ≤ normalizer (D : Set G)) :
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ ∃ X : Subgroup G,
      IsPGroup r X ∧ X ≠ ⊥ ∧ R ≤ normalizer (X : Set G) ∧
        ∀ x ∈ X, z * x * z⁻¹ = x⁻¹ := by
  have hhalf : 1 < (p + 1) / 2 := by omega
  obtain ⟨r, hr, hd⟩ := Nat.exists_prime_and_dvd (by omega : (p + 1) / 2 ≠ 1)
  have ho : Odd r := Odd.of_dvd_nat (show Odd ((p + 1) / 2) from ⟨p / 4, by omega⟩) hd
  have hd' : r ∣ p + 1 := hd.trans (Nat.div_dvd_of_dvd (by omega : 2 ∣ p + 1))
  let := IsCyclic.commGroup (α := D)
  let K : Subgroup D := (powMonoidHom r : D →* D).ker
  have hK : Nat.card K = r := by
    rw [IsCyclic.card_powMonoidHom_ker, hc, Nat.gcd_eq_right hd']
  let X := K.map D.subtype
  have hXcard : Nat.card X = r := (Nat.card_congr
    (K.equivMapOfInjective D.subtype D.subtype_injective).toEquiv).symm.trans hK
  have hX : IsPGroup r X := IsPGroup.of_card (n := 1) (by simpa using hXcard)
  have hXD : X ≤ D := map_subtype_le K
  refine ⟨r, hr, ho, X, hX, ?_, ?_, fun x hx => hinv x (hXD hx)⟩
  · intro he
    have he' : Nat.card X = 1 := (eq_bot_iff_card X).mp he
    have := hr.two_le
    omega
  · apply le_normalizer_iff.mpr
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hym : g * (y : G) * g⁻¹ ∈ D := (mem_normalizer_iff.mp (hn hg) y).mp y.property
    refine ⟨⟨g * (y : G) * g⁻¹, hym⟩, ?_, rfl⟩
    change (⟨g * (y : G) * g⁻¹, hym⟩ : D) ^ r = 1
    apply Subtype.ext
    change (g * (y : G) * g⁻¹) ^ r = 1
    have hy' : (y : G) ^ r = 1 := congrArg Subtype.val (show y ^ r = 1 from hy)
    simpa only [map_pow, map_one, MulAut.conj_apply] using congrArg (MulAut.conj g) hy'

omit [Finite G] in
/-- Transport through the literal normal-subgroup model, retaining outer actions. -/
theorem transport_subgroup {M : Type*} [Group M]
    (L : Subgroup G) [L.Normal] (e : L ≃* M) (R : Subgroup G)
    (D : Subgroup M) (z : L)
    (hinv : ∀ x ∈ D, e z * x * (e z)⁻¹ = x⁻¹)
    (hpres : ∀ g ∈ R, ∀ x ∈ D, e (MulAut.conjNormal g (e.symm x)) ∈ D) :
    ∃ X : Subgroup G, Nonempty (D ≃* X) ∧
      R ≤ normalizer (X : Set G) ∧ ∀ x ∈ X, (z : G) * x * (z : G)⁻¹ = x⁻¹ := by
  let f : M →* G := L.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp e.symm.injective
  let X := D.map f
  have hez : f (e z) = (z : G) := by simp [f]
  refine ⟨X, ⟨D.equivMapOfInjective f hf⟩, ?_, ?_⟩
  · apply le_normalizer_iff.mpr
    rintro g hg x ⟨y, hy, rfl⟩
    refine ⟨e (MulAut.conjNormal g (e.symm y)), hpres g hg y hy, ?_⟩
    simp only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      e.symm_apply_apply, Subgroup.subtype_apply, MulAut.conjNormal_apply]
  · rintro x ⟨y, hy, rfl⟩
    simpa only [map_mul, map_inv, hez] using congrArg f (hinv y hy)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup
