module
public import BenderSuzuki.SE.Proposition84Torus
public import Theory.GroupTheory.CyclicQuotientEmbedding
/-!
# The actual inverted cyclic subgroup of an odd central cover

Transport the model torus to the quotient by the actual kernel and apply
the proved central odd-kernel inversion theorem. The same lifted element
inverts the resulting cyclic subgroup, whose order equals the model torus.
This strengthens mere cyclic-order lifting for the E.6.27 application.
Source: Aschbacher–Smith E.2.2 and E.6.27, pp.215–216,257.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

omit [Finite H] in
theorem cyclic_inverted_lift_of_central_odd_kernel
    (q : G →* H) (hq : Function.Surjective q) (hc : q.ker ≤ center G)
    (ho : Odd (Nat.card q.ker)) (C : Subgroup H) [IsCyclic C]
    (w : G) (hw : ∀ x ∈ C, q w*x*(q w)⁻¹=x⁻¹) :
    ∃ D : Subgroup G, D ≤ C.comap q ∧ IsCyclic D ∧ Nat.card D=Nat.card C ∧
      ∀ x ∈ D, w*x*w⁻¹=x⁻¹ := by
  let e := QuotientGroup.quotientKerEquivOfSurjective q hq
  let Cq := C.map e.symm.toMonoidHom
  let : IsCyclic Cq := isCyclic_of_surjective _ (e.symm.toMonoidHom.subgroupMap_surjective C)
  have hqc : Nat.card Cq = Nat.card C := card_map_of_injective e.symm.injective
  have hinv : ∀ x ∈ Cq,
      BenderSuzuki.PFAppendixIII.rightConjugateElem x (QuotientGroup.mk' q.ker w⁻¹) = x⁻¹ := by
    rintro _ ⟨c,hcC,rfl⟩
    apply e.injective
    change e ((QuotientGroup.mk' q.ker w⁻¹)⁻¹ * e.symm c * QuotientGroup.mk' q.ker w⁻¹) = e ((e.symm c)⁻¹)
    simp only [map_mul,map_inv,e.apply_symm_apply]
    change (q w)⁻¹⁻¹*c*(q w)⁻¹=c⁻¹
    simpa only [inv_inv] using hw c hcC
  obtain ⟨D,hD,hcyc,hcard⟩ := BenderSuzuki.invertedTorus_lift_of_central_odd_kernel
    q.ker hc ho w⁻¹ Cq inferInstance hinv
  refine ⟨D,?_,hcyc,hcard.trans hqc,?_⟩
  · intro x hx
    have hxD : QuotientGroup.mk' q.ker x ∈ Cq := ((Set.ext_iff.mp hD x).mp hx).1
    obtain ⟨c,hcC,he⟩ := hxD
    have hh := congrArg e he
    change e (e.symm c) = q x at hh
    rw [e.apply_symm_apply] at hh
    change q x ∈ C
    exact hh ▸ hcC
  · intro x hx
    have hxD := ((Set.ext_iff.mp hD x).mp hx).2
    change w⁻¹⁻¹*x*w⁻¹=x⁻¹ at hxD
    simpa only [inv_inv] using hxD
end CFSG.Quasithin.ChapterE
