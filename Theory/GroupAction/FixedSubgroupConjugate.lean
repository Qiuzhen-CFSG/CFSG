module
public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# Fixed groups of conjugate automorphisms with marked subgroup transport

The conjugating automorphism carries fixed points to fixed points. Its
pointwise equation lets consumers restrict this map to marked subgroups.
No membership of the conjugator in an extension is needed.

Application: the diagonal-conjugated graph actors in Aschbacher--Smith
F.4.29(2) and F.4.37, printed pp.289,293 of refs/quasithin.pdf.
-/

public noncomputable section
namespace MulAut
variable {G : Type*} [Group G]

/-- Conjugation of an actor transports its fixed group by the conjugating automorphism. -/
def fixedConjugateEquiv (a b : MulAut G) :
    a.fixedSubgroup ≃* (b*a*b⁻¹).fixedSubgroup where
  toFun x := ⟨b x.val, by
    rw [mem_fixedSubgroup]
    change b (a (b.symm (b x.val))) = b x.val
    rw [b.symm_apply_apply,(mem_fixedSubgroup _ _).mp x.property]⟩
  invFun x := ⟨b.symm x.val,by
    apply (mem_fixedSubgroup _ _).mpr
    apply b.injective
    have hx := (mem_fixedSubgroup _ _).mp x.property
    change b (a (b.symm x.val))=x.val at hx
    rw [hx,b.apply_symm_apply]⟩
  left_inv x := Subtype.ext (b.symm_apply_apply x.val)
  right_inv x := Subtype.ext (b.apply_symm_apply x.val)
  map_mul' x y := Subtype.ext (b.map_mul x.val y.val)

theorem fixedConjugateEquiv_apply (a b : MulAut G) (x : a.fixedSubgroup) :
    (fixedConjugateEquiv a b x).val=b x.val := by rfl

theorem fixedConjugateEquiv_symm_apply (a b : MulAut G)
    (x : (b*a*b⁻¹).fixedSubgroup) :
    ((fixedConjugateEquiv a b).symm x).val=b.symm x.val := by rfl

end MulAut
