module
public import Theory.GroupTheory.SolvableResidual.Transport
public import Theory.GroupTheory.GeneralizedFitting.CentralCoverLift

/-!
# Prime-core quotients of preimage residuals

A surjection restricts to the full preimage of any subgroup, then to its
solvable residual. A prime-group kernel stays a prime-group kernel under
both restrictions. Removing the prime cores gives a canonical isomorphism,
with the original map on representatives. Generalized Fitting bounds lift
along the same map. Source application: the parabolic residuals of
Aschbacher--Smith 15.1.20(2), printed p.1095.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace MonoidHom
variable {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
variable (f : X →* Y) (P : Subgroup Y)

/-- The original map restricted to both literal solvable residuals. -/
def preimageResidualMap : solvableResidual (P.comap f) →* solvableResidual P :=
  (f.subgroupComap P).solvableResidualMap

omit [Finite Y] in
theorem preimageResidualMap_surjective (hf : Function.Surjective f) :
    Function.Surjective (f.preimageResidualMap P) :=
  (f.subgroupComap P).solvableResidualMap_surjective
    (f.subgroupComap_surjective_of_surjective P hf)

omit [Finite X] [Finite Y] in
theorem preimageResidualMap_ker_isPGroup {p : ℕ} (hk : IsPGroup p f.ker) :
    IsPGroup p (f.preimageResidualMap P).ker := by
  have he : (f.subgroupComap P).ker = f.ker.comap (P.comap f).subtype := by
    ext x
    exact Subtype.ext_iff
  apply (f.subgroupComap P).solvableResidualMap_ker_isPGroup
  rw [he]
  exact hk.comap_of_injective _ (P.comap f).subtype_injective

/-- The canonical core quotient equivalence for the literal preimage residual. -/
noncomputable def preimageResidualCoreEquiv {p : ℕ} [Fact p.Prime]
    (hf : Function.Surjective f) (hk : IsPGroup p f.ker) :
    (solvableResidual (P.comap f) ⧸ pCore p (solvableResidual (P.comap f))) ≃*
      (solvableResidual P ⧸ pCore p (solvableResidual P)) :=
  (f.preimageResidualMap P).pCoreQuotientEquiv
    (f.preimageResidualMap_surjective P hf) (f.preimageResidualMap_ker_isPGroup P hk)

@[simp] theorem preimageResidualCoreEquiv_mk {p : ℕ} [Fact p.Prime]
    (hf : Function.Surjective f) (hk : IsPGroup p f.ker)
    (x : solvableResidual (P.comap f)) :
    f.preimageResidualCoreEquiv P hf hk (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (f.preimageResidualMap P x) := rfl

/-- Characteristic-p generalized Fitting structure lifts through a p-kernel. -/
theorem preimageResidual_generalizedFitting {p : ℕ} [Fact p.Prime]
    (hf : Function.Surjective f) (hk : IsPGroup p f.ker)
    (hfit : generalizedFitting (solvableResidual P) = pCore p (solvableResidual P)) :
    generalizedFitting (solvableResidual (P.comap f)) =
      pCore p (solvableResidual (P.comap f)) := by
  let g := f.preimageResidualMap P
  have hg := f.preimageResidualMap_surjective P hf
  have hgk := f.preimageResidualMap_ker_isPGroup P hk
  apply le_antisymm _ ((pCore_le_fitting _ p).trans (fitting_le_generalizedFitting _))
  have hh := map_generalizedFitting_le_of_surjective g hg
  rw [hfit] at hh
  have he := map_le_iff_le_comap.mp hh
  rwa [g.comap_pCore_of_ker_isPGroup hg hgk] at he
end MonoidHom
