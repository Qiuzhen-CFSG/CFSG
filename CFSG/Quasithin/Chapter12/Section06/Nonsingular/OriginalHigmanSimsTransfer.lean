module

public import Theory.GroupTheory.PResidual.PrimeToTransport
public import Theory.GroupTheory.PerfectCentralSupplement
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Transfer through the full cover in the HS common-residual comparison

A central covering map carries the prime-to-three residual onto the
native residual. If the native residual quotient is cyclic, the quotient
upstairs is central-by-cyclic and hence commutative. Transfer in the full
perfect ambient group then puts every central two-subgroup in the embedded
prime-to-three residual of an odd-index overgroup.

The covering kernel is retained throughout: its containment in the
residual is a conclusion of transfer, not a premise of the quotient map.
This is the full-cover transfer step needed for the paired components
in the original 12.6.12 HS case. The native cyclic-quotient calculation
remains a separate model theorem.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSims
variable {A B : Type*} [Group A] [Group B] [Finite A]

/-- A cyclic native residual quotient lifts to a commutative quotient
through a central cover, without first discarding its kernel. -/
theorem residual_quotient_commutative_of_central_cover
    (f : A →* B) (hf : Function.Surjective f) (hk : f.ker ≤ center A)
    [IsCyclic (B ⧸ primeToResidual 3 B)] :
    IsMulCommutative (A ⧸ primeToResidual 3 A) := by
  let R := primeToResidual 3 A
  let S := primeToResidual 3 B
  let π := QuotientGroup.mk' R
  let q := QuotientGroup.mk' S
  have hmap : R.map f = S := map_primeToResidual_of_surjective 3 f hf
  let g : A ⧸ R →* B ⧸ S := QuotientGroup.lift R (q.comp f) (by
    intro r hr
    exact (QuotientGroup.eq_one_iff _).mpr (hmap ▸ mem_map_of_mem f hr))
  apply g.isMulCommutative_of_isCyclic_of_ker_le_center
  intro x hx
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective R x
  have ha : f a ∈ S := (QuotientGroup.eq_one_iff _).mp hx
  obtain ⟨r,hr,he⟩ := hmap.symm ▸ ha
  have hc : a*r⁻¹ ∈ center A := hk (by
    change f (a*r⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel])
  have hπ : π (a*r⁻¹) = π a := by
    have hrπ : π r = 1 := (QuotientGroup.eq_one_iff _).mpr hr
    rw [map_mul,map_inv,hrπ,inv_one,mul_one]
  rw [←hπ]
  apply mem_center_iff.mpr
  intro y
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective R y
  simpa only [map_mul] using congrArg π (mem_center_iff.mp hc b)

/-- Perfect-group transfer puts the whole central two-subgroup in the
same embedded residual of the odd-index subgroup. -/
theorem central_two_subgroup_le_residual
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (M Z : Subgroup E) (hZM : Z ≤ M) (hZ : Z ≤ center E)
    (h2 : IsPGroup 2 Z) (hi : ¬ 2 ∣ M.index)
    (f : M →* B) (hf : Function.Surjective f) (hk : f.ker ≤ center M)
    [IsCyclic (B ⧸ primeToResidual 3 B)] :
    Z ≤ (primeToResidual 3 M).map M.subtype := by
  let := residual_quotient_commutative_of_central_cover f hf hk
  have hderived : _root_.commutator M ≤ primeToResidual 3 M :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).mp inferInstance
  have hz := central_pSubgroup_le_commutator M Z hZM hZ h2 hi
  rw [←map_subtype_commutator] at hz
  exact hz.trans (map_mono hderived)

end CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSims
