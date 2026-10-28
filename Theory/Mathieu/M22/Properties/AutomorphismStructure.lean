module
public import Mathlib.GroupTheory.SemidirectProduct
public import Theory.Mathieu.M22.Properties.Automorphisms
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
namespace Sporadic.Mathieu
noncomputable section
public abbrev M22OuterC2 := Multiplicative (ZMod 2)
@[expose] public def m22OuterC2Generator : M22OuterC2 :=
  Multiplicative.ofAdd 1
@[expose] public def m22ToDesignAut : M22 →* m22DesignAut where
  toFun h := ⟨h.1, h.property.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl
public theorem m22OuterDesignAut_sq :
    m22OuterDesignAut ^ 2 = 1 := by
  rw [← m22OuterDesignAut_order]
  exact pow_orderOf_eq_one _
@[expose] public noncomputable def m22OuterC2ToDesignAut :
    M22OuterC2 →* m22DesignAut where
  toFun x := if x = m22OuterC2Generator then m22OuterDesignAut else 1
  map_one' := by decide +kernel
  map_mul' := by
    intro x y
    fin_cases x <;> fin_cases y <;> decide +kernel
@[simp] public theorem m22OuterC2ToDesignAut_generator :
    m22OuterC2ToDesignAut m22OuterC2Generator = m22OuterDesignAut := by
  simp [m22OuterC2ToDesignAut]
@[expose] public noncomputable def m22OuterC2Action :
    M22OuterC2 →* MulAut M22 :=
  m22DesignAutToAut.comp m22OuterC2ToDesignAut
public theorem m22OuterC2_compatibility (g : M22OuterC2) :
    m22ToDesignAut.comp (m22OuterC2Action g).toMonoidHom =
      (MulAut.conj (m22OuterC2ToDesignAut g)).toMonoidHom.comp m22ToDesignAut := by
  apply MonoidHom.ext
  intro h
  apply Subtype.ext
  change ((m22DesignAutToAut (m22OuterC2ToDesignAut g)) h : Equiv.Perm (Fin 22)) =
    ((m22OuterC2ToDesignAut g : m22DesignAut) : Equiv.Perm (Fin 22)) *
      ((m22ToDesignAut h : m22DesignAut) : Equiv.Perm (Fin 22)) *
      (((m22OuterC2ToDesignAut g : m22DesignAut) : Equiv.Perm (Fin 22)))⁻¹
  rw [m22DesignAutToAut_apply_perm]
  rfl
@[expose] public noncomputable def m22SemidirectToDesignAut :
    M22 ⋊[m22OuterC2Action] M22OuterC2 →* m22DesignAut :=
  SemidirectProduct.lift m22ToDesignAut m22OuterC2ToDesignAut
    m22OuterC2_compatibility
public theorem m22SemidirectToDesignAut_surjective :
    Function.Surjective m22SemidirectToDesignAut := by
  intro g
  rcases m22DesignAut_normalForm g with ⟨h, hh | hh⟩
  · refine ⟨⟨h, 1⟩, ?_⟩
    apply Subtype.ext
    simpa [m22SemidirectToDesignAut, m22ToDesignAut] using hh.symm
  · refine ⟨⟨h, m22OuterC2Generator⟩, ?_⟩
    apply Subtype.ext
    simpa [m22SemidirectToDesignAut, m22ToDesignAut, m22OuterDesignAut] using hh.symm
public noncomputable instance :
    Finite (M22 ⋊[m22OuterC2Action] M22OuterC2) :=
  Finite.of_equiv (M22 × M22OuterC2) SemidirectProduct.equivProd.symm
public theorem m22Semidirect_card :
    Nat.card (M22 ⋊[m22OuterC2Action] M22OuterC2) = 887040 := by
  rw [SemidirectProduct.card, m22_order]
  norm_num [M22OuterC2]
public noncomputable def m22DesignAutSemidirectEquiv :
    M22 ⋊[m22OuterC2Action] M22OuterC2 ≃* m22DesignAut := by
  letI := Fintype.ofFinite (M22 ⋊[m22OuterC2Action] M22OuterC2)
  letI := Fintype.ofFinite m22DesignAut
  apply MulEquiv.ofBijective m22SemidirectToDesignAut
  rw [Fintype.bijective_iff_surjective_and_card]
  refine ⟨m22SemidirectToDesignAut_surjective, ?_⟩
  simpa only [Fintype.card_eq_nat_card, m22Semidirect_card, m22DesignAut_order]

public instance m22ConcreteOuterQuotient_normal : (M22.subgroupOf m22DesignAut).Normal := M22_normal_in_m22DesignAut

/-- The quotient of the concrete design automorphism group by its even
M22 subgroup has exactly two elements. -/
public abbrev M22ConcreteOuterQuotient :=
  m22DesignAut ⧸ (M22.subgroupOf m22DesignAut)

public theorem m22ConcreteOuterQuotient_card :
    Nat.card M22ConcreteOuterQuotient = 2 := by
  have heq :
      M22.subgroupOf m22DesignAut = m22EvenDesignAut := by
    ext g
    simp [M22, m22EvenDesignAut]
  change Nat.card (m22DesignAut ⧸ (M22.subgroupOf m22DesignAut)) = 2
  rw [← (M22.subgroupOf m22DesignAut).index_eq_card, heq,
    m22EvenDesignAut_index]

/-- The nontrivial coset in the concrete outer quotient is represented by
the odd design involution. -/
@[expose] public noncomputable def m22ConcreteOuterQuotientClass :
    M22ConcreteOuterQuotient :=
  QuotientGroup.mk' (M22.subgroupOf m22DesignAut) m22OuterDesignAut

public theorem m22ConcreteOuterQuotientClass_ne_one :
    m22ConcreteOuterQuotientClass ≠ 1 := by
  intro h
  apply m22OddPairSwap_not_mem_M22
  have hm : m22OuterDesignAut ∈ M22.subgroupOf m22DesignAut := by
    apply (QuotientGroup.eq_one_iff
      (N := M22.subgroupOf m22DesignAut)
      (m22OuterDesignAut : m22DesignAut)).mp
    simpa [m22ConcreteOuterQuotientClass] using h
  exact hm

public theorem m22ConcreteOuterQuotient_nontrivial :
    Nontrivial M22ConcreteOuterQuotient :=
  nontrivial_iff.mpr
    ⟨m22ConcreteOuterQuotientClass, 1,
      m22ConcreteOuterQuotientClass_ne_one⟩
end
end Sporadic.Mathieu

