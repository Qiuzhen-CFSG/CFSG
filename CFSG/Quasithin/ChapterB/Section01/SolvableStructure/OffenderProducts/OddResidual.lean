module
public import Theory.GroupTheory.PResidual.SymmetricThreeProducts
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Factors
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# Odd residuals in the actual solvable offender product

The internal factor coordinates embed every subgroup of the offender product
into a product of S₃ groups. Its two-residual is consequently a three-group.
This retains the supplied subgroup embedding and needs no bound on the number
of factors. It supplies the odd-by-two input in original 14.1.4 and the
ratio-one branch of 15.1.2.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableFFFactors
variable {G V H : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [Group H] {ρ : Representation (ZMod 2) G V}

theorem pResidual_threeGroup_of_embedding (d : SolvableFFFactors ρ)
    (f : H →* offenderSubgroup ρ) (hf : Function.Injective f) :
    IsPGroup 3 (pResidual 2 H) := by
  obtain ⟨eS⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let e := d.groupProduct.symm.trans
    (MulEquiv.piCongrRight fun i => (d.factorModel i).trans eS)
  exact Theory.GroupTheory.pResidual_threeGroup_of_injective_permThree_product
    (e.toMonoidHom.comp f) (e.injective.comp hf)

theorem odd_pResidual_of_embedding [Finite H] (d : SolvableFFFactors ρ)
    (f : H →* offenderSubgroup ρ) (hf : Function.Injective f) :
    Odd (Nat.card (pResidual 2 H)) := by
  obtain ⟨n,hn⟩ := (d.pResidual_threeGroup_of_embedding f hf).exists_card_eq
  rw [hn]
  exact (by decide : Odd 3).pow
end CFSG.Quasithin.ChapterB.SolvableFFFactors
