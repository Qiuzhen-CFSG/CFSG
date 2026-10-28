module
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.Model
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Theory.Representation.BinaryOffender.Basic

/-!
# A Sylow action on the deleted tensor square

A Sylow 2-subgroup of S₅ wr C₂ is D₈ wr C₂, acting on the sixteen pairs
of the four nonfixed letters. The three small checked counts below support
Burnside bounds for every elementary subgroup, without subgroup enumeration.

Source: Aschbacher--Smith, Appendix D, D.3.7, printed pp.197–199.
-/

@[expose] public section
namespace BinaryPermutation.FiveTensorSquare.Small
open Subgroup
abbrev D8 := DihedralGroup 4
abbrev P := RegularWreathProduct D8 C2
abbrev Point := ZMod 4 × ZMod 4

instance : Fintype P := Fintype.ofEquiv ((C2 → D8) × C2)
  (RegularWreathProduct.equivProd D8 C2).symm
instance : DecidableEq P := (RegularWreathProduct.equivProd D8 C2).injective.decidableEq

def dihedralPoint : D8 → ZMod 4 → ZMod 4
  | .r i, x => x-i
  | .sr i, x => i-x

theorem dihedralPoint_one : ∀x, dihedralPoint 1 x=x := by decide +kernel

theorem dihedralPoint_mul : ∀g h x,dihedralPoint (g*h) x=dihedralPoint g (dihedralPoint h x) := by
  decide +kernel

def point (g : P) (x : Point) : Point :=
  if g.right=1 then (dihedralPoint (g.left 1) x.1,dihedralPoint (g.left swapIndex) x.2)
  else (dihedralPoint (g.left 1) x.2,dihedralPoint (g.left swapIndex) x.1)

instance pointAction : MulAction P Point where
  smul := point
  one_smul x := by
    change point 1 x=x
    simp [point,dihedralPoint_one]
  mul_smul a b x := by
    change point (a*b) x=point a (point b x)
    rcases index_cases a.right with ha|ha <;> rcases index_cases b.right with hb|hb <;>
      simp [point,RegularWreathProduct.mul_left,RegularWreathProduct.mul_right,ha,hb,
        dihedralPoint_mul]

def pointFixed (g : P) : ℕ := (Finset.univ.filter fun x : Point => point g x=x).card

/-- The 128-element Sylow action: every nonidentity involution fixes at most eight grid points. -/
theorem fixed_bound : ∀g : P,g*g=1 → g≠1 → pointFixed g≤8 := by decide +kernel

def smallPoint (g : D8) (i : Fin 5) : Fin 5 :=
  if hi : i.val<4 then ⟨(dihedralPoint g (i.val : ZMod 4)).val,Nat.lt_trans (ZMod.val_lt _) (by decide)⟩ else 4

def dihedralPerm (g : D8) : Equiv.Perm (Fin 5) where
  toFun := smallPoint g
  invFun := smallPoint g⁻¹
  left_inv := (by decide +kernel : ∀g i,smallPoint g⁻¹ (smallPoint g i)=i) g
  right_inv := (by decide +kernel : ∀g i,smallPoint g (smallPoint g⁻¹ i)=i) g

def dihedralHom : D8 →* Sym where
  toFun := dihedralPerm
  map_one' := by apply Equiv.ext; intro i; exact (by decide +kernel : ∀i,smallPoint 1 i=i) i
  map_mul' g h := by
    apply Equiv.ext
    intro i
    exact (by decide +kernel : ∀g h i,smallPoint (g*h) i=smallPoint g (smallPoint h i)) g h i

theorem dihedralHom_injective : Function.Injective dihedralHom := by
  exact (by decide +kernel : ∀g h,dihedralPerm g=dihedralPerm h → g=h)

def embed : P →* Wreath where
  toFun g := ⟨fun i => dihedralHom (g.left i),g.right⟩
  map_one' := by ext i <;> simp
  map_mul' a b := by ext i <;> simp [RegularWreathProduct.mul_left,RegularWreathProduct.mul_right]

theorem embed_injective : Function.Injective embed := by
  intro a b h
  apply RegularWreathProduct.ext
  · funext i
    apply dihedralHom_injective
    exact congrArg (fun x : Wreath => x.left i) h
  · exact congrArg (fun x : Wreath => x.right) h

theorem card_P : Nat.card P=128 := by
  rw [RegularWreathProduct.card,DihedralGroup.nat_card]
  have hC : Nat.card C2=2 := by exact Nat.card_zmod 2
  rw [hC]
  decide

noncomputable def sylow : Sylow 2 Wreath := by
  have hc : Nat.card embed.range=128 :=
    (Nat.card_congr (MonoidHom.ofInjective embed_injective).toEquiv).symm.trans card_P
  have hw : Nat.card Wreath=28800 := by
    rw [RegularWreathProduct.card]
    have hS : Nat.card Sym=120 := by rw [Nat.card_eq_fintype_card,Fintype.card_perm];decide
    have hC : Nat.card C2=2 := by exact Nat.card_zmod 2
    rw [hS,hC]
    decide
  have hi : embed.range.index=225 := by
    have h:=embed.range.card_mul_index
    rw [hc,hw] at h
    omega
  exact (IsPGroup.of_card (p:=2) (n:=7) hc).toSylow (by rw [hi];decide)

theorem sylow_coe : (sylow : Subgroup Wreath)=embed.range := rfl


/-- Only 44 Sylow elements square to one, including the identity. -/
theorem square_one_card : (Finset.univ.filter fun g:P => g*g=1).card=44 := by
  decide +kernel

/-- Beyond the uniform fixed bound four, the entire involution set has only 28 excess fixed points. -/
theorem total_excess :
    ∑g ∈ (Finset.univ.filter fun g:P => g*g=1), (pointFixed g-4)=28 := by
  decide +kernel

end BinaryPermutation.FiveTensorSquare.Small
