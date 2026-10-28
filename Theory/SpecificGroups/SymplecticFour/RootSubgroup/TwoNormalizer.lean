module
public import Theory.SpecificGroups.SymplecticFour.RootDisplacement
public import Theory.SpecificGroups.SymplecticFour.RootTori
public import Mathlib.Algebra.CharP.Reduced

/-!
# Two-subgroups normalizing a full symplectic root

Conjugation on a matrix root is multiplication of its parameter by a field
unit. A two-power-order element has trivial such scalar in characteristic
two. Thus every two-subgroup normalizing a full root centralizes it.
A quadratic actor with field-sized order and a displacement line is an
actual conjugate of the full long root, so the same assertion applies to it.

The critical-pair application in NonbinarySymplectic.CriticalReduction.NoncentralPair
forces a noncentral radius commutator to have image of order at least q².
Source: MS93 (5.2)(ii), printed p.914, using (3.3), printed p.867.
-/

public noncomputable section
open Subgroup Representation
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [CharP F 2]

/-- A two-subgroup normalizing a full matrix root fixes it pointwise. -/
theorem two_subgroup_normalizing_root_centralizes
    (P : Subgroup (Sp F)) (hP : IsPGroup 2 P) (r : Fin 8)
    (hn : P ≤ normalizer (RootSubgroup.group (F := F) r : Set (Sp F))) :
    P ≤ centralizer (RootSubgroup.group (F := F) r : Set (Sp F)) := by
  intro x hx
  obtain ⟨c,hc⟩ := RootTori.normalizer_scalar r x (hn hx)
  have hpow (k : ℕ) (t : F) : x^k * rootElement r t * (x^k)⁻¹ =
      rootElement r ((c : F)^k*t) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ',mul_inv_rev]
      calc
        x * x ^ k * rootElement r t * ((x ^ k)⁻¹ * x⁻¹) =
            x * (x ^ k * rootElement r t * (x ^ k)⁻¹) * x⁻¹ := by group
        _ = rootElement r ((c : F)^(k+1)*t) := by
          rw [ih,hc,pow_succ']
          simp only [mul_assoc]
  obtain ⟨k,hk⟩ := hP ⟨x,hx⟩
  have hxpow : x^(2^k)=1 := congrArg Subtype.val hk
  have hcpow : (c : F)^(2^k)=1 := by
    have hh := hpow (2^k) 1
    rw [hxpow,one_mul,inv_one,mul_one,mul_one] at hh
    exact (RootSubgroup.element_injective r hh).symm
  have hc1 : (c : F)=1 := by
    apply iterateFrobenius_inj F 2 k
    simpa only [iterateFrobenius_def,map_one] using hcpow
  intro y hy
  obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff r y).mp hy
  have hh := hc t
  rw [hc1,one_mul,mul_inv_eq_iff_eq_mul] at hh
  exact hh.symm

variable [Finite F]

/-- The same conclusion holds for a full field-sized quadratic actor with
one-dimensional displacement, with no root marking assumed. -/
theorem two_subgroup_normalizing_displacement_line_centralizes
    (A P : Subgroup (Sp F)) (hP : IsPGroup 2 P)
    (hn : P ≤ normalizer (A : Set (Sp F)))
    (hc : Nat.card A = Nat.card F)
    (hd : Module.finrank F (displacementSpace A) = 1)
    (hq : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v) :
    P ≤ centralizer (A : Set (Sp F)) := by
  obtain ⟨g,hg⟩ := FourLongRoots.exists_conjugate_root_of_displacement_one A hc hd hq
  have hn' : P.map (MulAut.conj g).toMonoidHom ≤
      normalizer (RootSubgroup.group (F := F) 0 : Set (Sp F)) := by
    rw [←hg]
    intro x hx
    exact le_normalizer_map (MulAut.conj g).toMonoidHom ((map_mono hn) hx)
  have hh := two_subgroup_normalizing_root_centralizes
    (P.map (MulAut.conj g).toMonoidHom) (hP.map _) 0 hn'
  rw [←hg] at hh
  intro x hx y hy
  have he := hh (mem_map_of_mem _ hx) _ (mem_map_of_mem _ hy)
  apply (MulAut.conj g).injective
  exact (map_mul (MulAut.conj g).toMonoidHom y x).trans
    (he.trans (map_mul (MulAut.conj g).toMonoidHom x y).symm)

end Theory.SpecificGroups.SymplecticFour
