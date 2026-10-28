module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Definitions
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection

/-!
# The intrinsic two-core kernel of an external component

Relative subnormality in H identifies the kernel of K → H/O₂(H) with
O₂(K). Transport through K.subgroupOf H then gives the actual equivalence
K/O₂(K) ≃ K*, with K* the source star image. No ambient normality of K
is required, and no classification of its quotient is asserted here.

This is the kernel calculation needed in Aschbacher–Smith 13.8.21(1),
combined manuscript of 1 March 2004, printed p.956. The proof uses the
general subnormal p-core theorem in NormalDirectPowerSection.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ExternalComponentAction
variable {G : Type*} [Group G] [Finite G]

/-- The kernel for the relative subgroup K inside H is its intrinsic two-core. -/
theorem starProjection_kernel (H K : Subgroup G)
    (hK : (K.subgroupOf H).IsSubnormal) :
    ((QuotientGroup.mk' (pCore 2 H)).comp (K.subgroupOf H).subtype).ker =
      pCore 2 (K.subgroupOf H) := by
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  exact hK.pCore_subgroupOf 2

/-- Identify the intrinsic quotient with the literal source image K*. -/
noncomputable def quotientStarEquiv (H K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsSubnormal) :
    (K ⧸ pCore 2 K) ≃* Source.starImage H K :=
  let e := (subgroupOfEquivOfLe hKH).symm
  (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    (hK.quotientCoreImageEquiv 2)

/-- The actual inclusion K → H followed by the quotient H → H/O₂(H). -/
def sourceProjection (H K : Subgroup G) (hKH : K ≤ H) : K →* Source.Hstar H :=
  (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hKH)

/-- On the original carrier K, the projection kernel is exactly O₂(K). -/
theorem sourceProjection_kernel (H K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsSubnormal) :
    (sourceProjection H K hKH).ker = pCore 2 K := by
  let e := subgroupOfEquivOfLe hKH
  change (((QuotientGroup.mk' (pCore 2 H)).comp (K.subgroupOf H).subtype).comp
    e.symm.toMonoidHom).ker = _
  rw [← MonoidHom.comap_ker, starProjection_kernel H K hK]
  rw [comap_equiv_eq_map_symm']
  exact pCore_map_iso 2 e

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ExternalComponentAction
