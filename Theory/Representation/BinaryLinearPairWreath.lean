module

public import Theory.SpecificGroups.BinaryLinear.Parabolics
public import Mathlib.GroupTheory.RegularWreathProduct
import Mathlib.LinearAlgebra.Prod

/-!
# The full actor on two complementary binary summands

A faithful linear subgroup preserving or exchanging the two axes, containing
both full linear factors and moving one axis, is the literal regular wreath
product. The equivalence retains the coordinate action. Surjectivity follows
from the full base and an actual exchanging element.
-/

public noncomputable section
namespace BinaryLinear.PairWreath
open Subgroup
private abbrev C2 := Multiplicative (ZMod 2)
private def swapIndex : C2 := Multiplicative.ofAdd 1
private theorem index_cases (i : C2) : i = 1 ∨ i = swapIndex := by revert i; decide
private theorem swap_ne_one : swapIndex ≠ 1 := by decide
private theorem swap_inv : swapIndex⁻¹ = swapIndex := by decide
private theorem swap_mul : swapIndex * swapIndex = 1 := by decide
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
private abbrev Actor (W : Type*) [AddCommGroup W] [Module (ZMod 2) W] :=
  RegularWreathProduct (BinaryLinear.GL W) C2

private def pairMap (w : Actor W) : BinaryLinear.GL (W × W) :=
  if w.right = 1 then (w.left 1).prodCongr (w.left swapIndex)
  else (LinearEquiv.prodComm (ZMod 2) W W).trans
    ((w.left 1).prodCongr (w.left swapIndex))

private def pairHom : Actor W →* BinaryLinear.GL (W × W) where
  toFun := pairMap
  map_one' := by ext v <;> simp [pairMap]
  map_mul' a b := by
    apply LinearEquiv.ext
    intro v
    rcases index_cases a.right with ha | ha <;>
      rcases index_cases b.right with hb | hb <;>
      simp [pairMap,RegularWreathProduct.mul_left,RegularWreathProduct.mul_right,
        ha,hb,swap_inv,swap_mul,swap_ne_one,LinearEquiv.mul_apply]

private theorem pairHom_injective [Nontrivial W] : Function.Injective (pairHom (W := W)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro w hw
  have hf : pairMap w = 1 := hw
  rcases index_cases w.right with h | h
  · apply RegularWreathProduct.ext
    · funext i
      rcases index_cases i with rfl | rfl
      · apply LinearEquiv.ext
        intro v
        have hh := congrArg (fun f : BinaryLinear.GL (W × W) => f (v,0)) hf
        simpa [pairMap,h] using congrArg Prod.fst hh
      · apply LinearEquiv.ext
        intro v
        have hh := congrArg (fun f : BinaryLinear.GL (W × W) => f (0,v)) hf
        simpa [pairMap,h] using congrArg Prod.snd hh
    · exact h
  · obtain ⟨v,hv⟩ := exists_ne (0 : W)
    have hh := congrArg (fun f : BinaryLinear.GL (W × W) => f (v,0)) hf
    exact (hv (by simpa [pairMap,h,swap_ne_one] using (congrArg Prod.fst hh).symm)).elim

private theorem preserving (f : BinaryLinear.GL (W × W))
    (h0 : ∀ v : W, (f (v,0)).2 = 0)
    (h1 : ∀ v : W, (f (0,v)).1 = 0) :
    ∃ a b : BinaryLinear.GL W, f = a.prodCongr b := by
  let a : W →ₗ[ZMod 2] W := (LinearMap.fst _ _ _).comp
    (f.toLinearMap.comp (LinearMap.inl _ _ _))
  let b : W →ₗ[ZMod 2] W := (LinearMap.snd _ _ _).comp
    (f.toLinearMap.comp (LinearMap.inr _ _ _))
  have hf (v : W × W) : f v = (a v.1,b v.2) := by
    have hv : v = (v.1,0)+(0,v.2) := by ext <;> simp
    calc
      f v = f (v.1,0)+f (0,v.2) := by rw [←map_add,←hv]
      _ = (a v.1,b v.2) := by ext <;> simp [a,b,h0,h1]
  have ha : Function.Bijective a := by
    constructor
    · intro x y he
      have hh : f (x,0) = f (y,0) := by simp only [hf,he]
      exact congrArg Prod.fst (f.injective hh)
    · intro x
      obtain ⟨v,hv⟩ := f.surjective (x,0)
      exact ⟨v.1,by simpa [hf] using congrArg Prod.fst hv⟩
  have hb : Function.Bijective b := by
    constructor
    · intro x y he
      have hh : f (0,x) = f (0,y) := by simp only [hf,he]
      exact congrArg Prod.snd (f.injective hh)
    · intro x
      obtain ⟨v,hv⟩ := f.surjective (0,x)
      exact ⟨v.2,by simpa [hf] using congrArg Prod.snd hv⟩
  exact ⟨LinearEquiv.ofBijective a ha,LinearEquiv.ofBijective b hb,LinearEquiv.ext hf⟩

private theorem pair_exists (f : BinaryLinear.GL (W × W))
    (hp : ((∀v : W,(f (v,0)).2 = 0) ∧ (∀v : W,(f (0,v)).1 = 0)) ∨
      ((∀v : W,(f (v,0)).1 = 0) ∧ (∀v : W,(f (0,v)).2 = 0))) :
    ∃ w : Actor W, pairHom w = f := by
  rcases hp with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · obtain ⟨a,b,hf⟩ := preserving f h0 h1
    exact ⟨⟨fun i => if i=1 then a else b,1⟩,by simp [pairHom,pairMap,swap_ne_one,hf]⟩
  · let s := LinearEquiv.prodComm (ZMod 2) W W
    obtain ⟨a,b,hf⟩ := preserving (s.trans f) h1 h0
    refine ⟨⟨fun i => if i=1 then a else b,swapIndex⟩,?_⟩
    apply LinearEquiv.ext
    intro v
    have hh := congrArg (fun F : BinaryLinear.GL (W × W) => F (v.2,v.1)) hf
    simpa [pairHom,pairMap,swap_ne_one,s] using hh.symm

/-- Full independent factors and an actual interchange identify the whole
actor, with the original action on both coordinates retained. -/
theorem paired_full_linear_actor [Nontrivial W]
    (Q : Subgroup (BinaryLinear.GL (W × W)))
    (hp : ∀g : Q,
      ((∀v : W,(g.val (v,0)).2 = 0) ∧ (∀v : W,(g.val (0,v)).1 = 0)) ∨
      ((∀v : W,(g.val (v,0)).1 = 0) ∧ (∀v : W,(g.val (0,v)).2 = 0)))
    (hb : ∀a b : BinaryLinear.GL W, a.prodCongr b ∈ Q)
    (hm : ∃g : Q, ∃v : W, (g.val (v,0)).2 ≠ 0) :
    ∃ e : Q ≃* RegularWreathProduct (BinaryLinear.GL W) (Multiplicative (ZMod 2)),
      ∀g : Q, ∀v : W × W,
        g.val v = if (e g).right = 1 then
          ((e g).left 1 v.1,(e g).left (Multiplicative.ofAdd 1) v.2)
        else ((e g).left 1 v.2,(e g).left (Multiplicative.ofAdd 1) v.1) := by
  classical
  choose w hw using fun g : Q => pair_exists g.val (hp g)
  let f : Q →* Actor W := {
    toFun := w
    map_one' := pairHom_injective (by rw [hw,map_one]; rfl)
    map_mul' := fun a b => pairHom_injective (by rw [hw,map_mul,hw,hw]; rfl) }
  have hf (g : Q) : pairHom (f g) = g.val := hw g
  have hinj : Function.Injective f := by
    intro a b he
    exact Subtype.ext ((hf a).symm.trans ((congrArg pairHom he).trans (hf b)))
  have hbase (y : Actor W) (hy : y.right = 1) : ∃g : Q,f g = y := by
    let g : Q := ⟨(y.left 1).prodCongr (y.left swapIndex),hb _ _⟩
    refine ⟨g,pairHom_injective ?_⟩
    rw [hf]
    simp [g,pairHom,pairMap,hy]
  obtain ⟨g,v,hv⟩ := hm
  have hgr : (f g).right ≠ 1 := by
    intro he
    have hh := congrArg (fun F : BinaryLinear.GL (W × W) => (F (v,0)).2) (hf g)
    exact hv (by simpa [pairHom,pairMap,he] using hh.symm)
  have hsurj : Function.Surjective f := by
    intro y
    rcases index_cases y.right with hy | hy
    · exact hbase y hy
    · have hg : (f g).right = swapIndex := (index_cases _).resolve_left hgr
      obtain ⟨a,ha⟩ := hbase (y*(f g)⁻¹) (by
        simp [RegularWreathProduct.mul_right,RegularWreathProduct.inv_right,hy,hg,swap_inv,swap_mul])
      exact ⟨a*g,by rw [map_mul,ha]; simp⟩
  refine ⟨MulEquiv.ofBijective f ⟨hinj,hsurj⟩,?_⟩
  intro g v
  have hh := congrArg (fun F : BinaryLinear.GL (W × W) => F v) (hf g).symm
  change g.val v = if (f g).right = 1 then
    ((f g).left 1 v.1,(f g).left (Multiplicative.ofAdd 1) v.2)
    else ((f g).left 1 v.2,(f g).left (Multiplicative.ofAdd 1) v.1)
  by_cases hr : (f g).right = 1 <;>
    simpa [pairHom,pairMap,hr,swapIndex] using hh

end BinaryLinear.PairWreath
