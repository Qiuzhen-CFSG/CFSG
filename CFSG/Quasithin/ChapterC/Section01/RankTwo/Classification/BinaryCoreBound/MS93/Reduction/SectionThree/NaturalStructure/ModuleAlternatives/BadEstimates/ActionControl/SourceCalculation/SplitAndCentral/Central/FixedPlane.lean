module
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.RestrictionComparison
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas

/-!
# Fixed planes in a four-dimensional binary action

Suppose every nontrivial involution moves at least two dimensions. An actor
of two-power order fixing a subspace of dimension at least two has all its
displacements in that subspace. Indeed its displacement has rank two. If
its square were nontrivial, the first two kernels of the nilpotent
displacement operator would have equal dimension; kernel stabilization
would then make the operator zero. Thus the actor is an involution and
its displacement image is contained in its two-dimensional kernel.

This is the linear calculation for the central-extension case of
Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.2)(iv) and (3.3), printed pp.863,866–868.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.SourceCalculation.Central

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem codim_pow_le (ρ : Representation (ZMod 2) G V) (g : G) (n : ℕ) :
    fixedCodim ρ (Subgroup.zpowers (g ^ n)) ≤ fixedCodim ρ (Subgroup.zpowers g) := by
  have h := Submodule.finrank_mono (fixedSpace_antitone ρ
    (Subgroup.zpowers_le.mpr ((Subgroup.zpowers g).pow_mem (Subgroup.mem_zpowers g) n)))
  have h₁ := fixedCodim_add_finrank ρ (Subgroup.zpowers (g ^ n))
  have h₂ := fixedCodim_add_finrank ρ (Subgroup.zpowers g)
  omega

private theorem two_le_codim (ρ : Representation (ZMod 2) G V)
    (hm : ∀ g : G, g ^ 2 = 1 → g ≠ 1 → 2 ≤ fixedCodim ρ (Subgroup.zpowers g))
    (n : ℕ) (g : G) (hp : g ^ (2 ^ n) = 1) (hne : g ≠ 1) :
    2 ≤ fixedCodim ρ (Subgroup.zpowers g) := by
  induction n generalizing g with
  | zero => simp only [pow_zero, pow_one] at hp; exact (hne hp).elim
  | succ n ih =>
    by_cases h : g ^ 2 = 1
    · exact hm g h hne
    · have hp' : (g ^ 2) ^ (2 ^ n) = 1 := by
        rw [← pow_mul, ← pow_succ']; exact hp
      exact (ih (g ^ 2) hp' h).trans (codim_pow_le ρ g 2)

/-- In degree four, a two-element fixing a plane has its displacement in
that plane if the representation has no transvections. -/
theorem displacement_le_fixed_plane (ρ : Representation (ZMod 2) G V)
    (hdim : Module.finrank (ZMod 2) V = 4)
    (hm : ∀ g : G, g ^ 2 = 1 → g ≠ 1 → 2 ≤ fixedCodim ρ (Subgroup.zpowers g))
    (W : Submodule (ZMod 2) V) (hW : 2 ≤ Module.finrank (ZMod 2) W)
    (g : G) (hp : ∃ n : ℕ, g ^ (2 ^ n) = 1)
    (hfix : W ≤ fixedSpace ρ (Subgroup.zpowers g)) :
    LinearMap.range (ρ g - LinearMap.id) ≤ W := by
  by_cases hg : g = 1
  · subst g
    simp [Module.End.one_eq_id]
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (M := V) (by omega)
  let : CharP (Module.End (ZMod 2) V) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (Module.End (ZMod 2) V)).injective 2
  obtain ⟨n, hn⟩ := hp
  let N : Module.End (ZMod 2) V := ρ g - 1
  have hker : N.ker = fixedSpace ρ (Subgroup.zpowers g) := by
    ext v
    rw [mem_fixedSpace_zpowers_iff]
    exact sub_eq_zero
  have hlow := two_le_codim ρ hm n g hn hg
  have hcod := fixedCodim_add_finrank ρ (Subgroup.zpowers g)
  have hmono := Submodule.finrank_mono hfix
  have hcodim : fixedCodim ρ (Subgroup.zpowers g) = 2 := by omega
  have hrank : Module.finrank (ZMod 2) N.range = 2 := by
    simpa only [fixedCodim_zpowers_eq_displacement_rank, N, Module.End.one_eq_id] using hcodim
  have hnil : N ^ (2 ^ n) = 0 := by
    dsimp only [N]
    rw [sub_pow_char_pow_of_commute 2 n (Commute.one_right _),
      ← map_pow, hn, map_one, one_pow, sub_self]
  have hN2 : N ^ 2 = ρ (g ^ 2) - 1 := by
    dsimp only [N]
    rw [sub_pow_char_of_commute 2 (Commute.one_right _), ← map_pow, one_pow]
  have hg2 : g ^ 2 = 1 := by
    by_contra hg2
    have hp2 : (g ^ 2) ^ (2 ^ n) = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hn, one_pow]
    have hlow2 := two_le_codim ρ hm n (g ^ 2) hp2 hg2
    rw [fixedCodim_zpowers_eq_displacement_rank] at hlow2
    have hkerle : N.ker ≤ (N ^ 2).ker := by
      simpa only [pow_two, Module.End.mul_eq_comp] using LinearMap.ker_le_ker_comp N N
    have hk1 := N.finrank_range_add_finrank_ker
    have hk2 := (N ^ 2).finrank_range_add_finrank_ker
    have hkmono := Submodule.finrank_mono hkerle
    have heq : N.ker = (N ^ 2).ker := by
      apply Submodule.eq_of_le_of_finrank_eq hkerle
      change 2 ≤ Module.finrank (ZMod 2) (ρ (g ^ 2) - 1).range at hlow2
      rw [← hN2] at hlow2
      omega
    have he := Module.End.ker_pow_constant (f := N) (k := 1) (by simpa using heq)
      (2 ^ n - 1)
    have hpos : 0 < 2 ^ n := by positivity
    rw [show 1 + (2 ^ n - 1) = 2 ^ n by omega, hnil, LinearMap.ker_zero,
      pow_one] at he
    have hz := LinearMap.ker_eq_top.mp he
    rw [hz, LinearMap.range_zero, finrank_bot] at hrank
    omega
  have hsq : N ^ 2 = 0 := by rw [hN2, hg2, map_one, sub_self]
  have heq : W = N.ker := by
    rw [hker]
    exact Submodule.eq_of_le_of_finrank_eq hfix (by omega)
  rw [heq]
  rintro v ⟨w, rfl⟩
  change N (N w) = 0
  have hh := LinearMap.congr_fun hsq w
  exact hh

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.SourceCalculation.Central
