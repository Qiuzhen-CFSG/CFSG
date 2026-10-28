module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CanonicalLabelElementary
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Syntheme.BlockCoordinates

/-!
# The actual six-point action at a cubic-tree vertex

A branch frame identifies the six distance-two vertices with three binary
pairs. Tree midpoint uniqueness makes this identification injective and
shows that the vertex stabilizer permutes its three blocks compatibly with
its action on the neighbors. The existing binary-block lift then places
this literal action in the syntheme wreath model.

Source: Goldschmidt (1980), (6.12.1)--(6.12.2), printed pp.403--404.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup SimpleGraph Theory.GroupAction.CubicTree
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

namespace BranchFrame
variable {a : RankTwo.Vertex F} (f : BranchFrame F a)

def point (x : Fin 3 × ZMod 2) : RankTwo.Vertex F :=
  if x.2 = 0 then f.c x.1 else f.d x.1

theorem point_adj (x : Fin 3 × ZMod 2) :
    (RankTwo.graph F).Adj (f.e x.1).val (f.point x) := by
  dsimp only [point]
  split_ifs <;> first | exact f.c_adj _ | exact f.d_adj _

theorem point_ne_center (x : Fin 3 × ZMod 2) : f.point x ≠ a := by
  dsimp only [point]
  split_ifs <;> first | exact f.c_ne_center _ | exact f.d_ne_center _

theorem point_dist (h : CubicTreeAction F) (x : Fin 3 × ZMod 2) :
    (RankTwo.graph F).dist a (f.point x) = 2 := by
  dsimp only [point]
  split_ifs <;> first | exact f.c_dist h _ | exact f.d_dist h _

theorem point_injective (h : CubicTreeAction F) : Function.Injective f.point := by
  rintro ⟨i,b⟩ ⟨j,c⟩ he
  have hij : (f.e i).val = (f.e j).val :=
    DistanceTwoGeometry.midpoint_unique h.tree.isAcyclic (f.point_ne_center (i,b)).symm
      (f.e i).property (f.point_adj (i,b)) (f.e j).property
      (he.symm ▸ f.point_adj (j,c))
  have hi : i = j := f.e.injective (Subtype.ext hij)
  subst j
  fin_cases b <;> fin_cases c
  · rfl
  · have hh : f.c i = f.d i := he
    exact ((f.c_ne_d i) hh).elim
  · have hh : f.d i = f.c i := he
    exact ((f.c_ne_d i) hh.symm).elim
  · rfl

def sphereSet (a : RankTwo.Vertex F) :
    SubMulAction (RankTwo.stabilizer F a) (RankTwo.Vertex F) where
  carrier := {w | (RankTwo.graph F).dist a w = 2}
  smul_mem' g w hw := by
    have he := RankTwo.dist_smul F g.val a w
    rw [show g.val • a = a from g.property] at he
    exact he.trans hw

abbrev neighborSet (a : RankTwo.Vertex F) :
    SubMulAction (RankTwo.stabilizer F a) (RankTwo.Vertex F) where
  carrier := (RankTwo.graph F).neighborSet a
  smul_mem' g w hw := by
    change (RankTwo.graph F).Adj a (g.val • w)
    have hw' : (RankTwo.graph F).Adj a w := hw
    have he := (translationGraphIso F g.val).toHom.map_adj hw'
    change (RankTwo.graph F).Adj (g.val • a) (g.val • w) at he
    simpa only [show g.val • a = a from g.property] using he

def sphereEquiv (h : CubicTreeAction F) : Fin 3 × ZMod 2 ≃ sphereSet a :=
  Equiv.ofBijective (fun x => ⟨f.point x, f.point_dist h x⟩) (by
    constructor
    · intro x y he
      exact f.point_injective h (congrArg Subtype.val he)
    · intro w
      have ht : w.val.type = a.type := by
        apply ((RankTwo.even_dist_iff F h.generated a w.val).mp ?_).symm
        rw [w.property]
        decide
      rcases f.radiusTwo_cases h ht (le_of_eq w.property) with hw | ⟨i, hw | hw⟩
      · have hh : (RankTwo.graph F).dist a w.val = 2 := w.property
        rw [hw, dist_self] at hh
        omega
      · exact ⟨(i,0), Subtype.ext (by simpa only [point, ↓reduceIte] using hw.symm)⟩
      · exact ⟨(i,1), Subtype.ext (by simpa only [point, one_ne_zero, ↓reduceIte] using hw.symm)⟩)

def branchAction : RankTwo.stabilizer F a →* Equiv.Perm (Fin 3) :=
  (Equiv.permCongrHom (show Fin 3 ≃ neighborSet a from f.e).symm).toMonoidHom.comp
    (MulAction.toPermHom (RankTwo.stabilizer F a) (neighborSet a))

def sphereAction (h : CubicTreeAction F) :
    RankTwo.stabilizer F a →* Equiv.Perm (Fin 3 × ZMod 2) :=
  (Equiv.permCongrHom (f.sphereEquiv h).symm).toMonoidHom.comp
    (MulAction.toPermHom (RankTwo.stabilizer F a) (sphereSet a))

theorem branchAction_eval (g : RankTwo.stabilizer F a) (i : Fin 3) :
    (f.e (f.branchAction g i)).val = g.val • (f.e i).val := by
  change (f.e (f.e.symm (g • (show neighborSet a from f.e i)))).val = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem sphereAction_eval (h : CubicTreeAction F)
    (g : RankTwo.stabilizer F a) (x : Fin 3 × ZMod 2) :
    f.point (f.sphereAction h g x) = g.val • f.point x := by
  change ((f.sphereEquiv h) ((f.sphereEquiv h).symm (g • (f.sphereEquiv h x)))).val = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem sphereAction_block (h : CubicTreeAction F)
    (g : RankTwo.stabilizer F a) (x : Fin 3 × ZMod 2) :
    (f.sphereAction h g x).1 = f.branchAction g x.1 := by
  apply f.e.injective
  apply Subtype.ext
  rw [f.branchAction_eval]
  apply DistanceTwoGeometry.midpoint_unique h.tree.isAcyclic
    (f.point_ne_center (f.sphereAction h g x)).symm
    (f.e (f.sphereAction h g x).1).property (f.point_adj _)
  · have he := (translationGraphIso F g.val).toHom.map_adj (f.e x.1).property
    change (RankTwo.graph F).Adj (g.val • a) (g.val • (f.e x.1).val) at he
    simpa only [show g.val • a = a from g.property] using he
  · rw [f.sphereAction_eval]
    exact (translationGraphIso F g.val).toHom.map_adj (f.point_adj x)

open Theory.SpecificGroups.SymmetricSix.SynthemeCalculation

def blockAction (h : CubicTreeAction F) : RankTwo.stabilizer F a →* Model :=
  blockActionHom (f.sphereAction h) f.branchAction (fun g i b => f.sphereAction_block h g (i,b))

theorem blockAction_coordinates (h : CubicTreeAction F) (g : RankTwo.stabilizer F a) :
    coordinateHom (f.blockAction h g) = f.sphereAction h g :=
  coordinateHom_blockActionHom _ _ _ g

theorem blockAction_right (h : CubicTreeAction F) (g : RankTwo.stabilizer F a) :
    (f.blockAction h g).right = f.branchAction g := rfl

end BranchFrame
end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
