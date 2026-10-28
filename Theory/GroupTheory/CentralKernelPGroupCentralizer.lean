module
public import Theory.GroupTheory.CentralQuotientPGroupCentralizer
/-!
# Element centralizers under a surjection with central prime-power kernel

This transports the central-quotient centralizer theorem through the first
isomorphism theorem, retaining an arbitrary specified surjective map. If the
original centralizer and the central kernel are p-groups, the full centralizer
of the image is a p-group. Source application: Parrott (1972), printed p.683.
-/

open Subgroup
namespace MonoidHom
variable {G H : Type*} [Group G] [Group H] {p : ℕ}
public theorem isPGroup_centralizer_of_central_kernel
    (q : G →* H) (hq : Function.Surjective q) (hk : q.ker ≤ center G)
    (hkp : IsPGroup p q.ker) (t : G) (ht : IsPGroup p (centralizer ({t} : Set G))) :
    IsPGroup p (centralizer ({q t} : Set H)) := by
  have hp := isPGroup_centralizer_quotient_of_central_kernel q.ker hk hkp t ht
  let e := QuotientGroup.quotientKerEquivOfSurjective q hq
  have het : e.symm (q t) = QuotientGroup.mk' q.ker t := by
    apply e.injective
    rw [e.apply_symm_apply]
    rfl
  let j : centralizer ({q t} : Set H) →* centralizer ({QuotientGroup.mk' q.ker t} : Set (G ⧸ q.ker)) :=
    (e.symm.toMonoidHom.comp (centralizer ({q t} : Set H)).subtype).codRestrict _ (by
      intro x
      apply mem_centralizer_singleton_iff.mpr
      rw [← het]
      simpa only [map_mul, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype] using congrArg e.symm (mem_centralizer_singleton_iff.mp x.property))
  apply hp.of_injective j
  intro x y hxy
  apply Subtype.ext
  apply e.symm.injective
  exact congrArg (centralizer ({QuotientGroup.mk' q.ker t} : Set (G ⧸ q.ker))).subtype hxy
end MonoidHom
