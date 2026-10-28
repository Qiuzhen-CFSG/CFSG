module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.OneAbelian.Rigidity
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.BothNonabelian.ThirtyTwo
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.MarkedCases
/-!
# Full marked recognition at common Sylow order thirty-two

The original faithful pair of characteristic-two vertices has an abelian core
at order thirty-two. The completed one-abelian family identifies both original
vertices and their compatible wreathed overlap with the G₂(2)′ parabolics.
Choosing its source orientation produces the literal marked amalgam. More
generally, the same endpoint closes every remaining branch with an abelian core.

Source: Aschbacher--Smith F.1.12(I)(8), printed p.263, and F.6.5, p.305.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}

theorem exceptional_marked_of_one_abelian
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    (S : Sylow 2 G) (hS : A⊓B=(S : Subgroup G)) (hlarge : 8<Nat.card S)
    (hns : ¬ Nonempty (S≃*Multiplicative (ZMod 2)×DihedralGroup 4))
    (hab : IsMulCommutative (pCore 2 A) ∨ IsMulCommutative (pCore 2 B)) :
    ExceptionalMarkedAmalgam A B ∨ ExceptionalMarkedAmalgam B A := by
  rcases hab with ha | hb
  · let := ha
    exact Or.inr (Or.inl (OneAbelian.derived_amalgam h hcore hA hB S hS hlarge hns))
  · let := hb
    exact Or.inl (Or.inl (OneAbelian.derived_amalgam h.symm hcore hB hA
      S ((inf_comm _ _).trans hS) hlarge hns))

theorem exceptional_marked_of_card_thirty_two
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    (S : Sylow 2 G) (hS : A⊓B=(S : Subgroup G)) (hc : Nat.card S=32) :
    ExceptionalMarkedAmalgam A B ∨ ExceptionalMarkedAmalgam B A := by
  have hns : ¬ Nonempty (S≃*Multiplicative (ZMod 2)×DihedralGroup 4) := by
    rintro ⟨e⟩
    have he := Nat.card_congr e.toEquiv
    norm_num [Nat.card_prod, Nat.card_zmod, Nat.card_eq_fintype_card, DihedralGroup.card, hc] at he
  exact exceptional_marked_of_one_abelian h hcore hA hB S hS (by omega) hns
    (BothNonabelian.one_core_abelian_of_card_thirty_two h hcore hA hB (hS ▸ hc))
end CFSG.Quasithin.ChapterF.SourceAssembly
