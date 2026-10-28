module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairResidualImages
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedFive.Module
public import Theory.Representation.BinaryConjugationSection.FiveObstruction
/-!
# A natural SL₂(4) section excludes a paired five-letter residual

The literal first residual image supplies five-letter core coordinates on
the component commutator. Comparing those with the original natural
section gives the cubic fixed-space contradiction, retaining both actor maps.
Source: Aschbacher–Smith E.2.3 and 10.2.3(4), pp.216–217 and746.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB.SourceInduction ChapterC.RankOne.ChiProduct.SelectedRankOne
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
variable {F : Type*} [Field F] [CharP F 2]
local instance fiveAxisNaturalFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
set_option backward.isDefEq.respectTransparency false in
theorem not_first_five_residual_of_natural_four
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q) (hk : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hk).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype))
    (c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)))
    (L : Subgroup G)
    (hL : L.map q = (factorResidual q
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)) d.first).map q)
    (hF : Nat.card F = 4) (r : L →* SL(2,F))
    (n : BinaryConjugationSection L ⁅U,L⁆ (⁅U,L⁆ ⊓ centralizer (L : Set G))
      (SL2.BinarySmall.natural.comp r)) : False := by
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let e := c.action.groupEquiv
  let j := ChapterC.SymmetricFive.Paired.leftFactorMap Y e
  have hi : L.map q = (alternatingGroup (Fin 5)).map j := by
    rw [hL,paired_symmetric_first_residual_image α q hq d c]
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      refine ⟨a.1,ha.1,?_⟩
      exact congrArg (fun a => ((e.symm a : Y) : H)) (Prod.ext rfl ha.2.symm)
    · rintro ⟨a,ha,rfl⟩
      exact ⟨(a,1),⟨ha,one_mem _⟩,rfl⟩
  let W := (⁅U,L⁆ : Subgroup G)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left U L)
  obtain ⟨f,_,hf⟩ := first_five_moved_coordinates U q hq hk d c L hi
  let eA := (alternatingGroup (Fin 5)).equivMapOfInjective j
    (ChapterC.SymmetricFive.Paired.leftFactorMap_injective Y e)
  let a : L →* alternatingGroup (Fin 5) := eA.symm.toMonoidHom.comp
    ((MulEquiv.subgroupCongr hi).toMonoidHom.comp (q.subgroupMap L))
  have ha : Function.Surjective a := eA.symm.surjective.comp
    ((MulEquiv.subgroupCongr hi).surjective.comp (q.subgroupMap_surjective L))
  have hqa (l : L) : j (a l) = q (l:G) := by
    exact congrArg Subtype.val (eA.apply_symm_apply ((MulEquiv.subgroupCongr hi) (q.subgroupMap L l)))
  have hla (l : L) : q (l:G) ∈ Y := by
    rw [←hqa]
    exact (e.symm ((a l:Equiv.Perm (Fin 5)),1)).property
  have hcoord (l : L) : (e ⟨q (l:G),hla l⟩).1 = (a l:Equiv.Perm (Fin 5)) := by
    have hz : (⟨q (l:G),hla l⟩:Y) = e.symm ((a l:Equiv.Perm (Fin 5)),1) :=
      Subtype.ext (hqa l).symm
    rw [hz,e.apply_symm_apply]
  apply BinaryConjugationSection.not_five_core_of_natural_four hF r n a ha f
  intro g v
  exact (hf g (hla g) (Additive.ofMul v) _).trans
    (congrArg (fun z => BinaryPermutation.coreRepresentation (Fin 5) z (f (Additive.ofMul v)))
      (hcoord g))
end CFSG.Quasithin.ChapterE.ThompsonAction
