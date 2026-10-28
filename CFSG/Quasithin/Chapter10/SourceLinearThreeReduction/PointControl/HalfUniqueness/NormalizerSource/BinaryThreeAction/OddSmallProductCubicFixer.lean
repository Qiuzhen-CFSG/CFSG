module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallCubicFixer
public import Theory.GroupTheory.AutomorphismSquareRank
public import GorensteinWalter.SL2UniversalCover
public import Theory.GroupTheory.FourCubicKernel

/-!
# Product automorphisms fixing the actual cubic plane

Pointwise fixation of a marked cubic in each factor excludes interchange
in the automorphism-square normal form. The prime-field calculation then
forces both coordinate involutions to be inner. The original cubic plane
supplies these marks through its two cyclic projections and exact order.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.CubicFixer

/-- The marked coordinate cubics force an involutory product automorphism
into the actual inner subgroup, including the identity automorphism. -/
theorem square_one_product_cubic_fixer_inner {F : Type} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hF : Nat.card F = p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13)
    (a : MulAut (PSL(2,F) × PSL(2,F))) (ha : a ^ 2 = 1)
    (x y : PSL(2,F)) (hx : orderOf x = 3) (hy : orderOf y = 3)
    (hfx : a (x,1) = (x,1)) (hfy : a (1,y) = (1,y)) :
    a ∈ MulAut.innerSubgroup (PSL(2,F) × PSL(2,F)) := by
  have hlarge : 3 < Nat.card F := by have := Nat.mod_le p 24; omega
  let : Fact (3 < Nat.card F) := ⟨hlarge⟩
  let : IsQuasisimple PSL(2,F) := GorensteinWalter.PSL2Cover.psl_quasisimple F
  rcases AutomorphismSquare.normal_form (GorensteinWalter.psl2_center_eq_bot F) a with
    ⟨α,β,rfl⟩ | ⟨α,β,rfl⟩
  · have hα : α ^ 2 = 1 := by
      ext z
      exact congrArg Prod.fst (DFunLike.congr_fun ha (z,1))
    have hβ : β ^ 2 = 1 := by
      ext z
      exact congrArg Prod.snd (DFunLike.congr_fun ha (1,z))
    obtain ⟨u,hu⟩ := square_one_cubic_fixer_inner hp hF hmod α hα x hx
      (congrArg Prod.fst hfx)
    obtain ⟨v,hv⟩ := square_one_cubic_fixer_inner hp hF hmod β hβ y hy
      (congrArg Prod.snd hfy)
    refine ⟨(u,v),?_⟩
    rw [←hu,←hv]
    rfl
  · have hh : (1 : PSL(2,F)) = x := by
      have he : α 1 = x := congrArg Prod.fst hfx
      simpa only [map_one] using he
    rw [←hh,orderOf_one] at hx
    contradiction

/-- Both actual order-three coordinate marks exist in an elementary plane
whose two projections are cyclic. -/
theorem cubic_plane_coordinate_marks {Q : Type*} [Group Q] [Finite Q]
    (P : Subgroup (Q × Q)) [IsElementaryAbelian 3 P]
    [IsCyclic (P.map (MonoidHom.fst Q Q))]
    [IsCyclic (P.map (MonoidHom.snd Q Q))] (hP : Nat.card P = 9) :
    ∃ x y : Q, orderOf x = 3 ∧ orderOf y = 3 ∧ (x,1) ∈ P ∧ (1,y) ∈ P := by
  let X := P.map (MonoidHom.fst Q Q)
  let Y := P.map (MonoidHom.snd Q Q)
  obtain ⟨hX,hY⟩ := cubic_plane_projection_cards P hP
  have he : P = X.prod Y := eq_of_le_of_card_ge
    (fun z hz => ⟨mem_map_of_mem _ hz,mem_map_of_mem _ hz⟩) (by
      rw [Nat.card_congr (prodEquiv X Y).toEquiv,Nat.card_prod,hP]
      change 9 ≥ Nat.card X * Nat.card Y
      rw [hX,hY])
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' 3 (G := X) (by rw [hX])
  obtain ⟨y,hy⟩ := exists_prime_orderOf_dvd_card' 3 (G := Y) (by rw [hY])
  refine ⟨x,y,?_,?_,?_,?_⟩
  · exact (orderOf_injective X.subtype Subtype.val_injective x).trans hx
  · exact (orderOf_injective Y.subtype Subtype.val_injective y).trans hy
  · rw [he]; exact ⟨x.property,one_mem _⟩
  · rw [he]; exact ⟨one_mem _,y.property⟩

/-- Every elementary two-subgroup fixing the original elementary cubic
plane pointwise is inner on the product. No module-image placement is assumed. -/
theorem elementary_product_cubic_fixer_inner {F : Type} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hF : Nat.card F = p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13)
    (A : Subgroup (MulAut (PSL(2,F) × PSL(2,F)))) [IsElementaryAbelian 2 A]
    (P : Subgroup (PSL(2,F) × PSL(2,F))) [IsElementaryAbelian 3 P]
    [IsCyclic (P.map (MonoidHom.fst _ _))] [IsCyclic (P.map (MonoidHom.snd _ _))]
    (hP : Nat.card P = 9) (hfix : ∀ a ∈ A, ∀ z ∈ P, a z = z) :
    A ≤ MulAut.innerSubgroup (PSL(2,F) × PSL(2,F)) := by
  obtain ⟨x,y,hx,hy,hxp,hyp⟩ := cubic_plane_coordinate_marks P hP
  intro a ha
  exact square_one_product_cubic_fixer_inner hp hF hmod a
    (elemPow_eq_one_of_isElementaryAbelian a ha) x y hx hy
    (hfix a ha _ hxp) (hfix a ha _ hyp)

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.CubicFixer
