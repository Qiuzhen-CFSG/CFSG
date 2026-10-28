module
public import Theory.GroupTheory.QuaternionCentralProductInvertingAction
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.FactorCoordinates
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.ResidualAlgebra
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.SingularInvolutionPairs
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent
public import Theory.GroupTheory.QuaternionCentralProductDiagonal

/-!
# Singular actors exchange the residual SL2(3) factors

In a quaternion central product, a nontrivial outer action whose displacements
are all singular must exchange the two intrinsic quaternion factors. Each
SL2(3) residual factor is the centralizer of the opposite quaternion factor
inside the two-residual. The same actor therefore exchanges the actual residual
factors, retaining their embeddings and their common center. For an involution,
its fixed subgroup in the core is the diagonal elementary eight.

The source application is the elementary module actor in Aschbacher--Smith
13.5.17, printed p.922. The proof uses the square-form geometry of F.9.5(6)
and the residual factor calculation of 14.2.21.
-/

public section
open Subgroup
namespace Subgroup.QuaternionCentralProductData
variable {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)

theorem swap_factors_of_singular_nontrivial (a : MulAut Q)
    (hs : BinaryFourPlus.SingularDisplacements (d.quotientWreathAction a))
    (hne : d.quotientWreathAction a ≠ 1) :
    d.left.map a.toMonoidHom = d.right ∧ d.right.map a.toMonoidHom = d.left := by
  have hlne : d.left.map a.toMonoidHom ≠ d.left := by
    intro he
    exact hne (BinaryFourPlus.eq_one_of_singular_preserving _ hs
      ((d.quotientWreathAction_right_eq_one_iff a).mpr he))
  have hl : d.left.map a.toMonoidHom=d.right :=
    ((d.quaternion_subgroup_iff _).mp
      ⟨(a.subgroupMap d.left).symm.trans d.left_model.some⟩).resolve_left hlne
  refine ⟨hl,?_⟩
  apply ((d.quaternion_subgroup_iff _).mp
    ⟨(a.subgroupMap d.right).symm.trans d.right_model.some⟩).resolve_right
  intro hr
  exact d.factors_ne (map_injective a.injective (hl.trans hr.symm))
end Subgroup.QuaternionCentralProductData

namespace Subgroup.QuaternionResidualCentralProduct
variable {G : Type*} [Group G] [Finite G]
  {Q : Subgroup G} [Q.Normal] {d : QuaternionCentralProductData Q}
  (c : QuaternionResidualCentralProduct Q d)

theorem swap_factors_of_singular_actor (v : G)
    (hs : BinaryFourPlus.SingularDisplacements
      (d.quotientWreathAction (MulAut.conjNormal v)))
    (hcent : centralizer (Q : Set G) ≤ Q) (hv : v ∉ Q) :
    c.left.map (MulAut.conj v).toMonoidHom = c.right ∧
    c.right.map (MulAut.conj v).toMonoidHom = c.left := by
  have hne : d.quotientWreathAction (MulAut.conjNormal v) ≠ 1 := by
    intro he
    apply hv
    rw [←d.normalWreathAction_ker Q hcent]
    exact he
  obtain ⟨hl,hr⟩ := d.swap_factors_of_singular_nontrivial (MulAut.conjNormal v) hs hne
  have hm (B : Subgroup Q) :
      (B.map (MulAut.conjNormal v).toMonoidHom).map Q.subtype =
        (B.map Q.subtype).map (MulAut.conj v).toMonoidHom := by
    rw [map_map,map_map]
    rfl
  have hl' := congrArg (Subgroup.map Q.subtype) hl
  have hr' := congrArg (Subgroup.map Q.subtype) hr
  rw [hm] at hl' hr'
  have hR : (pResidual 2 G).map (MulAut.conj v).toMonoidHom = pResidual 2 G :=
    map_pResidual 2 (MulAut.conj v)
  have hc (B : Subgroup G) :
      (centralizer (B : Set G)).map (MulAut.conj v).toMonoidHom =
        centralizer ((B.map (MulAut.conj v).toMonoidHom) : Set G) :=
    Theory.GroupTheory.map_centralizer_equiv (B : Set G) (MulAut.conj v)
  constructor
  · rw [c.centralizer_descriptions.1,map_inf _ _ _ (MulAut.conj v).injective,
      hR,hc,hr',←c.centralizer_descriptions.2]
  · rw [c.centralizer_descriptions.2,map_inf _ _ _ (MulAut.conj v).injective,
      hR,hc,hl',←c.centralizer_descriptions.1]
end Subgroup.QuaternionResidualCentralProduct

namespace Subgroup.QuaternionCentralProductData
variable {G : Type*} [Group G] [Finite G]

theorem fixed_core_card_of_singular_involution (Q : Subgroup G) [Q.Normal]
    (d : QuaternionCentralProductData Q) (v : G) (hv2 : v^2=1)
    (hs : BinaryFourPlus.SingularDisplacements
      (d.quotientWreathAction (MulAut.conjNormal v)))
    (hcent : centralizer (Q : Set G) ≤ Q) (hv : v ∉ Q) :
    Nat.card (Q ⊓ centralizer ({v} : Set G) : Subgroup G) = 8 := by
  have hne : d.quotientWreathAction (MulAut.conjNormal v) ≠ 1 := by
    intro he
    apply hv
    rw [←d.normalWreathAction_ker Q hcent]
    exact he
  have hl := (d.swap_factors_of_singular_nontrivial (MulAut.conjNormal v) hs hne).1
  let B := d.left.map Q.subtype
  let C := d.right.map Q.subtype
  have hB : B.map (MulAut.conj v).toMonoidHom = C := by
    have hh := congrArg (Subgroup.map Q.subtype) hl
    change (d.left.map Q.subtype).map (MulAut.conj v).toMonoidHom = d.right.map Q.subtype
    have hcomp : Q.subtype.comp (MulAut.conjNormal v).toMonoidHom =
        (MulAut.conj v).toMonoidHom.comp Q.subtype := by
      ext x
      rfl
    simpa only [map_map,hcomp] using hh
  let θ : B ≃* C := ((MulAut.conj v).subgroupMap B).trans (MulEquiv.subgroupCongr hB)
  have hθ (b : B) : v*(b : G)*v⁻¹=(θ b : G) := rfl
  have hinter : Nat.card (B ⊓ C : Subgroup G)=2 := by
    change Nat.card (d.left.map Q.subtype ⊓ d.right.map Q.subtype : Subgroup G)=2
    rw [←map_inf _ _ Q.subtype Q.subtype_injective,
      card_map_of_injective Q.subtype_injective,d.intersection_card]
  have hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b := by
    rintro _ ⟨b,hb,rfl⟩ _ ⟨c,hc,rfl⟩
    exact congrArg Subtype.val (d.commute b hb c hc)
  have hj : B ⊔ C=Q := by
    change d.left.map Q.subtype ⊔ d.right.map Q.subtype=Q
    rw [←map_sup,d.span,←MonoidHom.range_eq_map,range_subtype]
  have he := quaternion_diagonal_eq_inf_centralizer_of_swap B C θ hinter hcomm v hv2 hθ
  rw [hj] at he
  rw [he]
  exact (quaternion_diagonal_elementary_eight B C
    ((d.left.equivMapOfInjective Q.subtype Q.subtype_injective).symm.trans d.left_model.some)
    θ hinter hcomm).2.1
end Subgroup.QuaternionCentralProductData
