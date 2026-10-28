module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.HSWitnesses.CoverLayers.AlternatingLift
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.HSWitnesses.Inputs
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic

/-!
# The marked alternating components in the two HS quotient rows

The symmetric row has its usual alternating component; the product row has
the normal inner A₆. Component calculus proves uniqueness as actual embedded
subgroups. Each row is equipped with a specified double transposition,
transported through the supplied fixed-subgroup equivalence to the actual
HS carrier. Its order is proved here. Its 2-centrality in HS remains a
separate model obligation and is not asserted by this module.

The product uniqueness proof strengthens the isomorphism result in
`HSInner.Components` while retaining its component-calculus argument.
Source: Aschbacher–Smith 16.1.5(10), p.1172, and I.2.2 proof, p.411.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses.CoverLayers
open Subgroup Theory.GroupTheory
open OtherPreliminaries.JankoTwoHigmanSims

/-- The alternating component of the symmetric row. -/
def symmetricEmbedding : A8 →* S8 := (alternatingGroup (Fin 8)).subtype

theorem symmetricEmbedding_injective : Function.Injective symmetricEmbedding :=
  Subtype.val_injective

theorem symmetricEmbedding_range : symmetricEmbedding.range = alternatingGroup (Fin 8) :=
  range_subtype _

theorem symmetricEmbedding_normal : symmetricEmbedding.range.Normal := by
  rw [symmetricEmbedding_range]
  infer_instance

theorem symmetricEmbedding_isComponent : IsComponent S8 symmetricEmbedding.range := by
  let : IsQuasisimple A8 := GLS3.Chapter5.SchurPresentation.alternatingGroup_isQuasisimple 3
  exact ⟨symmetricEmbedding_normal.isSubnormal,
    IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective symmetricEmbedding_injective)⟩

theorem symmetric_component_unique (K : Subgroup S8) (hK : IsComponent S8 K) :
    K = symmetricEmbedding.range := by
  rw [symmetricEmbedding_range]
  exact HSOuter.symmetric_component_eq K hK

/-- The inner alternating component of the product row. -/
def productEmbedding : A6 →* C2 × MulAut A6 :=
  (1 : A6 →* C2).prod MulAut.conj

theorem productEmbedding_injective : Function.Injective productEmbedding := by
  intro a b h
  exact AlternatingSix.ShadowLocal.inner_injective (congrArg Prod.snd h)

theorem productEmbedding_normal : productEmbedding.range.Normal := by
  constructor
  rintro _ ⟨a, rfl⟩ g
  refine ⟨g.2 a, ?_⟩
  apply Prod.ext
  · simp [productEmbedding]
  · change MulAut.conj (g.2 a) = g.2 * MulAut.conj a * g.2⁻¹
    ext x
    simp

theorem productEmbedding_isComponent :
    IsComponent (C2 × MulAut A6) productEmbedding.range := by
  let : IsQuasisimple A6 := GLS3.Chapter5.SchurPresentation.alternatingGroup_isQuasisimple 1
  exact ⟨productEmbedding_normal.isSubnormal,
    IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective productEmbedding_injective)⟩

/-- This retains the actual subgroup, strengthening the existing isomorphism
statement `HSInner.product_component_equiv`. -/
theorem product_component_unique (K : Subgroup (C2 × MulAut A6))
    (hK : IsComponent (C2 × MulAut A6) K) : K = productEmbedding.range := by
  let : productEmbedding.range.Normal := productEmbedding_normal
  rcases hK.normal_dichotomy productEmbedding.range with hle | hc
  · exact hK.eq_of_le productEmbedding_isComponent hle
  · have hsnd (k : K) : k.val.2 = 1 := by
      apply MulEquiv.ext
      intro a
      apply AlternatingSix.ShadowLocal.inner_injective
      have hm := (commutator_eq_bot_iff_le_centralizer.mp hc) k.property
        (productEmbedding a) ⟨a, rfl⟩
      have hma : MulAut.conj a * k.val.2 = k.val.2 * MulAut.conj a := congrArg Prod.snd hm
      calc
        MulAut.conj (k.val.2 a) = k.val.2 * MulAut.conj a * k.val.2⁻¹ := by
          ext x
          simp
        _ = MulAut.conj a := by rw [← hma]; simp [mul_assoc]
    let f : K →* C2 := (MonoidHom.fst C2 (MulAut A6)).comp K.subtype
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      exact Prod.ext h ((hsnd x).trans (hsnd y).symm)
    let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective hf
    let := hK.2
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
    exact (Group.IsPerfect.not_isSolvable K inferInstance).elim

/-- The marked double transposition in the symmetric fixed subgroup. -/
def symmetricRoot (r : MulAut Sporadic.LeechRelated.HS.Carrier)
    (v : r.fixedSubgroup ≃* S8) : Sporadic.LeechRelated.HS.Carrier :=
  v.symm (symmetricEmbedding (rootInvolution 3))

/-- The marked double transposition in the inner A₆ of the product fixed subgroup. -/
def productRoot (r : MulAut Sporadic.LeechRelated.HS.Carrier)
    (v : r.fixedSubgroup ≃* C2 × MulAut A6) : Sporadic.LeechRelated.HS.Carrier :=
  v.symm (productEmbedding (rootInvolution 1))

theorem symmetricRoot_order (r : MulAut Sporadic.LeechRelated.HS.Carrier)
    (v : r.fixedSubgroup ≃* S8) : orderOf (symmetricRoot r v) = 2 := by
  change orderOf ((v.symm (symmetricEmbedding (rootInvolution 3)) : r.fixedSubgroup) :
    Sporadic.LeechRelated.HS.Carrier) = 2
  exact (orderOf_injective r.fixedSubgroup.subtype Subtype.val_injective _).trans
    ((v.symm.orderOf_eq _).trans
      ((orderOf_injective symmetricEmbedding symmetricEmbedding_injective _).trans
        (rootInvolution_order 3)))

theorem productRoot_order (r : MulAut Sporadic.LeechRelated.HS.Carrier)
    (v : r.fixedSubgroup ≃* C2 × MulAut A6) : orderOf (productRoot r v) = 2 := by
  change orderOf ((v.symm (productEmbedding (rootInvolution 1)) : r.fixedSubgroup) :
    Sporadic.LeechRelated.HS.Carrier) = 2
  exact (orderOf_injective r.fixedSubgroup.subtype Subtype.val_injective _).trans
    ((v.symm.orderOf_eq _).trans
      ((orderOf_injective productEmbedding productEmbedding_injective _).trans
        (rootInvolution_order 1)))

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses.CoverLayers
