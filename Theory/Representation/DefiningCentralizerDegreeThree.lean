module
public import Theory.Representation.NoncyclicDegreeThree
public import Theory.GroupTheory.CentralCoprimePrimeLift
public import Theory.GroupTheory.PrimeRankElementary
public import Mathlib.Algebra.CharP.Lemmas

/-!
# Defining-prime exclusion in degree-three four-group centralizers

A faithful noncyclic abelian determinant-one action in degree three has
three distinct character lines over the algebraic closure. A centralizing
operator preserves these lines. In characteristic p an operator of p-power
order acts trivially on each line, hence is trivial. A four-group lifts
through a central odd kernel with its full centralizer, so this calculation
also applies to the actual projective quotient.

Source: the signed-three two-local calculation in Aschbacher–Smith A.2.12,
printed p.36, and the degree-three weight argument of A.3.21(c).
-/

public section
open Module Subgroup
namespace Representation

variable {F G V : Type*} [Field F] [IsAlgClosed F] [Group G]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- In defining characteristic a centralizing prime-order element is trivial
when all occurring character spaces are lines. -/
theorem eq_one_of_centralizes_character_lines
    {p : ℕ} [Fact p.Prime] [CharP F p]
    (rho : Representation F G V) (A : Subgroup G) [IsMulCommutative A]
    (hrho : Function.Injective rho) (horder : (Nat.card A : F) ≠ 0)
    (hlines : ∀ chi : CharacterWeight (rho.comp A.subtype),
      Module.finrank F (characterWeightSpace (rho.comp A.subtype) chi.val) = 1)
    (g : G) (hg : g ∈ centralizer (A : Set G)) (hgp : g ^ p = 1) : g = 1 := by
  have hpres (chi : CharacterWeight (rho.comp A.subtype)) (v : V)
      (hv : v ∈ characterWeightSpace (rho.comp A.subtype) chi.val) :
      rho g v ∈ characterWeightSpace (rho.comp A.subtype) chi.val := by
    simp only [characterWeightSpace, Submodule.mem_iInf,
      Module.End.mem_eigenspace_iff] at hv ⊢
    intro a
    change rho (a : G) (rho g v) = (chi.val a : F) • rho g v
    have hc : (a : G) * g = g * a := hg a a.property
    rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]
    change rho g ((rho.comp A.subtype) a v) = _
    rw [hv a, map_smul]
  apply hrho
  rw [map_one]
  apply LinearMap.eqLocus_eq_top.mp
  apply top_unique
  rw [← iSup_characterWeightSpace_eq_top (rho.comp A.subtype) horder]
  refine iSup_le fun chi v hv => ?_
  change rho g v = v
  by_cases hv0 : v = 0
  · simp [hv0]
  let w : characterWeightSpace (rho.comp A.subtype) chi.val := ⟨v,hv⟩
  have hw : w ≠ 0 := fun he => hv0 (congrArg Subtype.val he)
  obtain ⟨a,ha⟩ := exists_smul_eq_of_finrank_eq_one (hlines chi) hw
    (⟨rho g v,hpres chi v hv⟩ : characterWeightSpace (rho.comp A.subtype) chi.val)
  have hav : rho g v = a • v := (congrArg Subtype.val ha).symm
  have hpv : ∀ n : ℕ, (rho g ^ n) v = a ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hav, smul_smul, pow_succ]
  have hap : a ^ p = 1 := by
    have hh := hpv p
    rw [← map_pow,hgp,map_one,Module.End.one_apply] at hh
    exact (smul_left_injective F hv0) (hh.symm.trans (one_smul F v).symm)
  have ha1 : a = 1 := by
    have hz : (a - 1) ^ p = 0 := by rw [sub_pow_char,hap,one_pow,sub_self]
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz)
  simpa only [ha1,one_smul] using hav

/-- The degree-three determinant-one hypotheses produce all the character
line assumptions internally. -/
theorem eq_one_of_centralizes_noncyclic_det_one_three
    {p : ℕ} [Fact p.Prime] [CharP F p]
    (rho : Representation F G V) (A : Subgroup G) [Finite A] [IsMulCommutative A]
    (hrho : Function.Injective rho) (horder : (Nat.card A : F) ≠ 0)
    (hdim : Module.finrank F V = 3) (hn : ¬ IsCyclic A)
    (hdet : ∀ a : A, LinearMap.det (rho a.val) = 1)
    (g : G) (hg : g ∈ centralizer (A : Set G)) (hgp : g ^ p = 1) : g = 1 := by
  apply eq_one_of_centralizes_character_lines rho A hrho horder ?_ g hg hgp
  intro chi
  apply characterWeight_finrank_one_of_card_eq_finrank (rho.comp A.subtype) horder
  rw [hdim]
  exact characterWeight_card_eq_three_of_noncyclic_det_one (rho.comp A.subtype) horder hdim
    (hrho.comp A.subtype_injective) hn hdet

end Representation

