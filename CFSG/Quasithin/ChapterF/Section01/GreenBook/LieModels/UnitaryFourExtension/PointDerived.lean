module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourExtension.BinaryOrders
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPointQuotient
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuterPointLocal
public import Theory.GroupTheory.NormalSymmetricThreeMetabelian
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# The second derived subgroup of the binary extended point endpoint

The ordinary vector stabilizer is normal of index six in the actual
extended point group. Its order-32 Heisenberg core has quotient SL₂(F₂),
hence S₃. Modulo this core the normal S₃ splits off its centralizer of
order six, so the quotient is metabelian. Thus the second derived
subgroup of the literal projective endpoint is a two-group.

The injective-map corollary is the endpoint invariant used in the source
F.4.36 graph-involution exclusion. It applies to the original centralizer
once that centralizer is placed in the marked point endpoint.
Source: Aschbacher–Smith, F.4.36, printed p.292.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.Extension
open Theory.SpecificGroups.ClassicalUnitary
local notation "h1" => (Nat.le_refl 1)
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 h1
local notation "P" => UnitaryFourOuter.point F σ hσ
local notation "N" => UnitaryFourOuter.pointVector F σ hσ

/-- The actual binary ordinary vector-local two-core quotient is S₃. -/
def binaryVectorQuotientEquiv :
    (PointLocal.MatrixLocal 1 h1 ⧸ pCore 2 (PointLocal.MatrixLocal 1 h1)) ≃*
      Equiv.Perm (Fin 3) := by
  let : Fintype (PointLocal.FixedField 1) := Fintype.ofFinite _
  let eF : PointLocal.FixedField 1 ≃+* ZMod 2 :=
    (ZMod.ringEquiv (PointLocal.FixedField 1) (by
      rw [← Nat.card_eq_fintype_card, PointLocal.fixedField_card 1 h1]
      decide)).symm
  exact ((QuotientGroup.quotientMulEquivOfEq (PointLocal.radical_eq_twoCore 1 h1).symm).trans
    (PointLocal.quotientEquivSL 1 h1)).trans
      ((Atlas.fieldEquivSL 2 eF).trans (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three))

theorem binary_vector_card : Nat.card (PointLocal.MatrixLocal 1 h1) = 192 := by
  have hc := (pCore 2 (PointLocal.MatrixLocal 1 h1)).card_mul_index
  rw [PointLocal.twoCore_card 1 h1, index_eq_card,
    Nat.card_congr binaryVectorQuotientEquiv.toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_perm] at hc
  norm_num at hc ⊢
  omega

/-- The literal matrix extended point and projective extended point are equivalent. -/
def binaryPointMatrixEquiv : P ≃* point 1 h1 :=
  (UnitaryFourOuter.point F σ hσ).equivMapOfInjective
    (extensionProjection 1 h1) (extensionProjection_injective 1 h1)

theorem binary_vector_index : (N).index = 6 := by
  have hN : Nat.card N = 192 :=
    (Nat.card_congr (UnitaryFourOuter.pointVectorEquiv F σ hσ).toEquiv).symm.trans
      binary_vector_card
  have hP : Nat.card P = 1152 :=
    (Nat.card_congr binaryPointMatrixEquiv.toEquiv).trans binary_point_card
  have hi := (N).card_mul_index
  rw [hN,hP] at hi
  omega

/-- The actual binary extended point endpoint has two-group second derived subgroup. -/
theorem binary_point_secondDerived_isTwoGroup :
    IsPGroup 2 (derivedSeries (point 1 h1) 2) := by
  let : Finite P := Finite.of_injective binaryPointMatrixEquiv binaryPointMatrixEquiv.injective
  let e := UnitaryFourOuter.pointVectorEquiv F σ hσ
  let j : (N ⧸ pCore 2 N) ≃* Equiv.Perm (Fin 3) :=
    (QuotientGroup.congr _ _ e.symm (pCore_map_iso 2 e.symm)).trans binaryVectorQuotientEquiv
  have hp := Theory.GroupTheory.derivedTwo_isTwoGroup_of_normal_indexSix N binary_vector_index j
  rw [← map_derivedSeries_eq (f := binaryPointMatrixEquiv.toMonoidHom)
    binaryPointMatrixEquiv.surjective 2]
  exact hp.map binaryPointMatrixEquiv.toMonoidHom

/-- Literal F.4.36 endpoint application: an injected centralizer inherits the
binary extended point group's second-derived two-group invariant. -/
theorem binary_point_secondDerived_of_injective
    {H : Type*} [Group H] (f : H →* point 1 h1) (hf : Function.Injective f) :
    IsPGroup 2 (derivedSeries H 2) := by
  let j : derivedSeries H 2 →* derivedSeries (point 1 h1) 2 :=
    (f.comp (derivedSeries H 2).subtype).codRestrict _ (fun x =>
      map_derivedSeries_le_derivedSeries f 2 (mem_map_of_mem f x.property))
  apply binary_point_secondDerived_isTwoGroup.of_injective j
  intro x y hxy
  apply Subtype.ext
  apply hf
  exact congrArg Subtype.val hxy

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.Extension
