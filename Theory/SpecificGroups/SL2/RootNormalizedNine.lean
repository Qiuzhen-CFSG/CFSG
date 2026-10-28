module

public import Theory.SpecificGroups.SL2.RootNormalizedNine.Torus

/-!
# Borel normalization from a root-normalized E₉ quotient

Let C be a subgroup of SL₂(F) × SL₂(F), where F is a finite field of
characteristic two with more than two elements. If the full upper root
product normalizes C and C/O₂(C) is elementary abelian of order nine, then
the product Borel normalizes C.

Sylow maximality puts O₂(C) in the root product. Cubes therefore lie in the
root product, and a matrix commutator calculation puts C in the Borel.
The two diagonal coordinates must both be nontrivial, since E₉ cannot
embed in the cyclic group Fˣ. Commuting with the two root factors then
puts the full root product in C. Finally the Borel modulo its root product
is abelian, so it normalizes C.

The final theorem retains the even-degree, degree-at-least-four and
nontrivial-core hypotheses of the intended application, although the
matrix argument proves the stronger statement above.

Source application: Aschbacher–Smith, `refs/quasithin.pdf`, printed p.1164,
proof of 15.4.20, ordinary even-field component case. This is a conditional
matrix lemma; the source theorem's coordinate construction and assembly
belong to its Chapter 15 consumer.
-/

open Matrix
open scoped MatrixGroups commutatorElement
namespace Matrix.SpecialLinearGroup.RootNormalizedNine
variable {F : Type*} [Field F]
local notation "E" => SL(2, F) × SL(2, F)
local notation "S" => Subgroup.prod (upperUnipotent F) (upperUnipotent F)
local notation "B" => Subgroup.prod (rankOneBorel F) (rankOneBorel F)
local notation "u" => transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one

private theorem triangular_commutator_upper {g : SL(2, F)}
    (hg : g.val 1 0 = 0) (t : F) :
    ⁅g, u t⁆ = u ((g.val 0 0 ^ 2 - 1) * t) := by
  rw [commutatorElement_def, triangular_conj_upper hg, transvection_inv, ← transvection_add]
  congr 1
  ring

variable [Finite F] [CharP F 2]

omit [Finite F] in
public theorem root_le_of_diagonal_nontrivial (C : Subgroup E) (hB : C ≤ B)
    (hn : S ≤ Subgroup.normalizer (C : Set E))
    (hfirst : ∃ c ∈ C, c.1.val 0 0 ≠ 1)
    (hsecond : ∃ c ∈ C, c.2.val 0 0 ≠ 1) : S ≤ C := by
  have hcomm {c s : E} (hc : c ∈ C) (hs : s ∈ S) : ⁅c, s⁆ ∈ C :=
    (Subgroup.le_normalizer_iff_commutator_le_left.mp hn)
      (Subgroup.commutator_mem_commutator hc hs)
  have hsq {a : F} (ha : a ≠ 1) : a^2 - 1 ≠ 0 := by
    intro h
    apply ha
    exact (frobenius_inj F 2) (by simpa [frobenius_def] using sub_eq_zero.mp h)
  have hrootFirst (t : F) : (u t, 1) ∈ C := by
    obtain ⟨c, hc, ha⟩ := hfirst
    let z := t / (c.1.val 0 0 ^ 2 - 1)
    have hm : ⁅c, (u z, 1)⁆ ∈ C := hcomm hc
      ⟨(mem_upperUnipotent F _).mpr ⟨z, rfl⟩, (upperUnipotent F).one_mem⟩
    have he : ⁅c, ((u z, 1) : E)⁆ = (u t, 1) := by
      apply Prod.ext
      · change ⁅c.1, u z⁆ = u t
        rw [triangular_commutator_upper ((mem_rankOneBorel_iff _).mp (hB hc).1)]
        congr 1
        exact mul_div_cancel₀ t (hsq ha)
      · change ⁅c.2, (1 : SL(2, F))⁆ = 1
        simp
    rwa [he] at hm
  have hrootSecond (t : F) : (1, u t) ∈ C := by
    obtain ⟨c, hc, ha⟩ := hsecond
    let z := t / (c.2.val 0 0 ^ 2 - 1)
    have hm : ⁅c, (1, u z)⁆ ∈ C := hcomm hc
      ⟨(upperUnipotent F).one_mem, (mem_upperUnipotent F _).mpr ⟨z, rfl⟩⟩
    have he : ⁅c, ((1, u z) : E)⁆ = (1, u t) := by
      apply Prod.ext
      · change ⁅c.1, (1 : SL(2, F))⁆ = 1
        simp
      · change ⁅c.2, u z⁆ = u t
        rw [triangular_commutator_upper ((mem_rankOneBorel_iff _).mp (hB hc).2)]
        congr 1
        exact mul_div_cancel₀ t (hsq ha)
    rwa [he] at hm
  intro x hx
  obtain ⟨s, hs⟩ := (mem_upperUnipotent F _).mp hx.1
  obtain ⟨t, ht⟩ := (mem_upperUnipotent F _).mp hx.2
  have he : x = (u s, 1) * (1, u t) := by ext <;> simp [hs, ht]
  rw [he]
  exact C.mul_mem (hrootFirst s) (hrootSecond t)

/-- An actual E₉ core quotient forces Borel normalization over any such field. -/
public theorem borel_le_normalizer_of_card_gt_two (C : Subgroup E) (hq : 2 < Nat.card F)
    (hn : S ≤ Subgroup.normalizer (C : Set E))
    (e : (C ⧸ pCore 2 C) ≃* Multiplicative (ZMod 3 × ZMod 3)) :
    B ≤ Subgroup.normalizer (C : Set E) := by
  have hB := subgroup_le_borel C hq hn e
  obtain ⟨hfirst, hsecond⟩ := exists_diagonal_ne_one C hB hn e
  exact borel_normalizes_of_root_le C
    (root_le_of_diagonal_nontrivial C hB hn hfirst hsecond) hB

/-- Borel normalization with the exact hypotheses of the even-field application. -/
public theorem borel_le_normalizer (C : Subgroup E) (n : ℕ)
    (hcard : Nat.card F = 2^n) (_heven : Even n) (hn4 : 4 ≤ n)
    (hn : S ≤ Subgroup.normalizer (C : Set E)) (_hcore : C.pCoreIn 2 ≠ ⊥)
    (e : (C ⧸ pCore 2 C) ≃* Multiplicative (ZMod 3 × ZMod 3)) :
    B ≤ Subgroup.normalizer (C : Set E) := by
  apply borel_le_normalizer_of_card_gt_two C _ hn e
  rw [hcard]
  have hpow : 2^4 ≤ 2^n := Nat.pow_le_pow_right (by decide) hn4
  omega

end Matrix.SpecialLinearGroup.RootNormalizedNine
