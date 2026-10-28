module

public import CFSG.Quasithin.ChapterI.Section03.InvolutionSource
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# Ordinary fixed components in the source-core quotient

When the two-layer is the whole group, GLS II B.5.22 carries an ordinary
component of an involution's fixed subgroup to a two-component in the fixed
subgroup of the literal O_{2',2} quotient. Its image is also quasisimple,
so it is ordinary. The quotient map has solvable kernel, hence the original
component and its image have isomorphic central quotients.

This preserves the original component and the actual fixed-subgroup map.
It supplies the covering-component comparison in Aschbacher--Smith 4.2.13,
printed p.612, following I.3.2, printed p.415.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.InvolutionSource

private theorem radical_eq_center (Q : Type*) [Group Q] [Finite Q] [IsQuasisimple Q] :
    solvableRadical Q = center Q := by
  exact le_antisymm IsQuasisimple.solvableRadical_le_center
    (le_solvableRadical (center Q) inferInstance
      (Group.isSolvable_of_comm fun x y => Subtype.ext (mem_center_iff.mp y.property x)))

/-- The original ordinary fixed component survives the literal source-core quotient,
with its central quotient unchanged. -/
theorem fixed_component_oddTwoCore_image
    {X : Type*} [Group X] [Finite X] (hX : twoComponentLayer X = ⊤)
    (a : MulAut X) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B) :
    IsComponent (MulAut.oddTwoCoreQuotientAut a).fixedSubgroup
      (B.map (MulAut.oddTwoCoreFixedMap a)) ∧
      Nonempty ((B ⧸ center B) ≃*
        ((B.map (MulAut.oddTwoCoreFixedMap a)) ⧸
          center (B.map (MulAut.oddTwoCoreFixedMap a)))) := by
  let f := MulAut.oddTwoCoreFixedMap a
  let E := B.map f
  have hE : E.IsTwoComponent := map_fixed_oddTwoCore_twoComponent
    hX a ha B (ChapterI.Balance.ordinary_isTwoComponent hB)
  let : Nontrivial E := (nontrivial_iff_ne_bot E).mpr hE.1.ne_bot
  let := hB.2
  let φ := f.subgroupMap B
  let : IsQuasisimple E := IsQuasisimple.of_surjective φ (f.subgroupMap_surjective B)
  let : Group.IsSolvable (pPrimeCore 2 X) := odd_order_theorem _
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  let : Group.IsSolvable (oddTwoCore X) := oddTwoCore_isSolvable
  let j : φ.ker →* oddTwoCore X := {
    toFun := fun k => ⟨k.val.val.val, (QuotientGroup.eq_one_iff _).mp (by
      have hk := congrArg (fun z : E => ((z : (MulAut.oddTwoCoreQuotientAut a).fixedSubgroup) :
        X ⧸ oddTwoCore X)) k.property
      exact hk)⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro k l he
    have hh : k.val.val.val = l.val.val.val :=
      congrArg (fun z : oddTwoCore X => (z : X)) he
    exact Subtype.ext (Subtype.ext (Subtype.ext hh))
  let : Group.IsSolvable φ.ker := Group.isSolvable_of_isSolvable_injective hj
  refine ⟨⟨hE.1.subnormal,inferInstance⟩,?_⟩
  have e := solvableRadicalQuotientEquiv φ (f.subgroupMap_surjective B)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (radical_eq_center B).symm).trans
    (e.trans (QuotientGroup.quotientMulEquivOfEq (radical_eq_center E)))⟩

end CFSG.Quasithin.ChapterI.InvolutionSource
