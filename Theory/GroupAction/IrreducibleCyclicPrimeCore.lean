module
public import Theory.GroupAction.IrreducibleSmallLinear
public import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Cyclic prime cores and irreducible noncyclic actors

The automorphism group of a cyclic odd-prime group is cyclic. Its image
under an ambient action of a noncyclic subgroup with irreducible Frattini
normalizer action is therefore trivial. This is the cyclic-core case of
the Fitting argument in Aschbacher--Smith 13.1.12, printed pp.873--874.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem IsNormalizerFrattiniIrreducible.le_centralizer_of_cyclic_odd_pGroup
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (P R : Subgroup G) [R.Normal]
    [IsCyclic R] (hR : IsPGroup p R)
    (hirr : IsNormalizerFrattiniIrreducible P) (hnc : ¬ IsCyclic P) :
    P ≤ centralizer (R : Set G) := by
  obtain ⟨n,hn⟩ := hR.exists_card_eq
  let : IsCyclic (ZMod (Nat.card R))ˣ := by
    rw [hn]
    exact ZMod.isCyclic_units_of_prime_pow p Fact.out (by rintro rfl; exact ho.not_two_dvd_nat (dvd_refl 2)) n
  let : IsCyclic (MulAut R) := (IsCyclic.mulAutMulEquiv R).isCyclic.mpr inferInstance
  have h := hirr.comp_eq_one_of_cyclic_range hnc
    (MulAut.conjNormal : G →* MulAut R) inferInstance
  intro x hx r hr
  have he := congrArg (fun a : MulAut R => ((a ⟨r,hr⟩ : R) : G))
    (DFunLike.congr_fun h ⟨x,hx⟩)
  change x*r*x⁻¹=r at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm
end Subgroup
