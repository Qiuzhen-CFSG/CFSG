module

public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.PResidual.PrimeToTransport
public import Theory.GroupTheory.PCoreActionSplitting

/-!
# Primary solvable radicals through the original solvable quotient

A surjection with solvable kernel carries the solvable radical onto the
solvable radical. Functoriality of O^{p′} then gives the exact image of
its embedded primary residual. If that image has trivial q-core and the
original kernel is a q-group, the restricted kernel is the primary
residual's own q-core. The resulting quotient equivalence is induced by
the original map.

Source: the original I_p/O₂(I_p) identification in Aschbacher--Smith
3.2.14, p.585.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

/-- The actual embedded primary residual of the solvable radical. -/
@[expose] def primarySolvableResidual (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  (primeToResidual p (solvableRadical G)).map (solvableRadical G).subtype

/-- The original quotient map carries primary solvable radicals onto one
another, with no choice of an unrelated group model. -/
theorem primarySolvableResidual_map (p : ℕ) [Fact p.Prime]
    (f : G →* H) (hf : Function.Surjective f) [Group.IsSolvable f.ker] :
    (primarySolvableResidual p G).map f = primarySolvableResidual p H := by
  have hr : (solvableRadical G).map f = solvableRadical H := by
    rw [← comap_solvableRadical_eq_of_solvable_ker f hf,map_comap_eq_self_of_surjective hf]
  rw [primarySolvableResidual,map_embedded_primeToResidual_of_hom,hr]
  rfl

/-- The primary solvable residual is characteristic in the original group. -/
instance primarySolvableResidual_characteristic (p : ℕ) :
    (primarySolvableResidual p G).Characteristic :=
  characteristic_of_characteristic_of_characteristic

/-- An original q-kernel and q-core-free primary image identify the quotient
of the original primary radical, via the original map. -/
def primarySolvableResidualQuotientEquiv (p q : ℕ) [Fact p.Prime]
    (f : G →* H) (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    (hk : IsPGroup q f.ker) (hcore : pCore q (primarySolvableResidual p H) = ⊥) :
    (primarySolvableResidual p G ⧸ pCore q (primarySolvableResidual p G)) ≃*
      primarySolvableResidual p H := by
  let I := primarySolvableResidual p G
  let fi := f.comp I.subtype
  have hr : fi.range = primarySolvableResidual p H := by
    rw [MonoidHom.range_comp,range_subtype,primarySolvableResidual_map p f hf]
  have hki : IsPGroup q fi.ker := by
    rw [← MonoidHom.comap_ker]
    exact hk.comap_of_injective I.subtype I.subtype_injective
  have hc : pCore q fi.range = ⊥ := by rw [hr]; exact hcore
  exact (QuotientGroup.quotientMulEquivOfEq
    (fi.ker_eq_pCore_of_range_core_eq_bot q hki hc).symm).trans
      ((QuotientGroup.quotientKerEquivRange fi).trans (MulEquiv.subgroupCongr hr))

/-- On representatives the quotient equivalence is the original homomorphism. -/
theorem primarySolvableResidualQuotientEquiv_apply_mk (p q : ℕ) [Fact p.Prime]
    (f : G →* H) (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    (hk : IsPGroup q f.ker) (hcore : pCore q (primarySolvableResidual p H) = ⊥)
    (x : primarySolvableResidual p G) :
    (primarySolvableResidualQuotientEquiv p q f hf hk hcore
      (QuotientGroup.mk' (pCore q (primarySolvableResidual p G)) x) : H) = f x := by
  unfold primarySolvableResidualQuotientEquiv
  rfl

end Subgroup
