module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.GlobalRelations

/-!
# GlobalPresentation

The universal group is defined on local root, full Cartan and dihedral parameters with explicit finite relators. Evaluation in any realization is constructed from those equations.

Source: GLS3 2.3.5--8 and Table 2.4; Steinberg, section 11, Lemmas 62--64.
The source fields, local equations and exhaustive row selection remain source
producer obligations; binary type tags do not supply these data.
-/

@[expose] public noncomputable section

namespace ReeF4.RootPresentationRecognition.Global.Presentation
open Subgroup Theory.GroupTheory OrderedRootPresentation
open SignedGeometry WeylPresentation CentralCovers.TwoPrimary
open CentralCovers.OddPrimary.Order
open LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData

/-- Local parameters only: sixteen roots, the full torus, and sixteen Weyl words. -/
abbrev Letter (m : ℕ) :=
  (Bool × ((i : PositiveTables.Root) × AngularPresentation.Parameter m i)) ⊕
    (Parabolics.fixedTorus m ⊕ Weyl)

def Letter.root {m : ℕ} (p : Bool) (i : PositiveTables.Root)
    (a : AngularPresentation.Parameter m i) : Letter m := .inl ⟨p,⟨i,a⟩⟩
def Letter.torus {m : ℕ} (t : Parabolics.fixedTorus m) : Letter m := .inr (.inl t)
def Letter.weyl {m : ℕ} (w : Weyl) : Letter m := .inr (.inr w)

def freeRoot {m : ℕ} (p : Bool) (i : PositiveTables.Root) (a : AngularPresentation.Parameter m i) :
    FreeGroup (Letter m) := FreeGroup.of (Letter.root p i a)
def freeTorus {m : ℕ} (t : Parabolics.fixedTorus m) : FreeGroup (Letter m) := FreeGroup.of (Letter.torus t)
def freeWeyl {m : ℕ} (w : Weyl) : FreeGroup (Letter m) := FreeGroup.of (Letter.weyl w)
def freePair {m : ℕ} (r : Index) (a : CoefficientField m) : FreeGroup (Letter m) :=
  freeRoot r.1 (.inl r.2) (PositiveTables.rootChartEquiv m (.inl r.2) a)
def freeQuartet {m : ℕ} (r : Index) (a b : CoefficientField m) : FreeGroup (Letter m) :=
  freeRoot r.1 (.inr r.2) (PositiveTables.rootChartEquiv m (.inr r.2) (a,b))

/-- Exactly local group laws and the fixed finite tables; there is no
multiplication table for arbitrary elements of the full model. -/
inductive Relator (m : ℕ) : FreeGroup (Letter m) → Prop
  | root_one p i : Relator m (freeRoot p i 1)
  | root_mul p i a b : Relator m (freeRoot p i a * freeRoot p i b * (freeRoot p i (a*b))⁻¹)
  | torus_one : Relator m (freeTorus 1)
  | torus_mul a b : Relator m (freeTorus a * freeTorus b * (freeTorus (a*b))⁻¹)
  | weyl_one : Relator m (freeWeyl 1)
  | weyl_mul a b : Relator m (freeWeyl a * freeWeyl b * (freeWeyl (a*b))⁻¹)
  | angular i j hj a b : Relator m
      (freeRoot true i a * freeRoot true j b * (freeRoot true i a)⁻¹ *
        (word (AngularPresentation.Parameter m) (freeRoot true) (tail sourceOrder i)
          ((AngularPresentation.table m).conjugate i j hj a b))⁻¹)
  | torus_root t i a : Relator m
      (freeTorus t * freeRoot true i a * (freeTorus t)⁻¹ *
        (freeRoot true i (SourceBorel.rootAction t i a))⁻¹)
  | weyl_torus s t : Relator m
      (freeWeyl (simple s) * freeTorus t * (freeWeyl (simple s))⁻¹ *
        (freeTorus (NormalizerPresentation.action m (simple s) t))⁻¹)
  | pair s r a : Relator m (freeWeyl (simple s) * freePair r a * (freeWeyl (simple s))⁻¹ *
      (freePair (step false s r) a)⁻¹)
  | quartet s r a b : Relator m (freeWeyl (simple s) * freeQuartet r a b * (freeWeyl (simple s))⁻¹ *
      (freeQuartet (step true s r) a b)⁻¹)
  | linear_gauss (a : (CoefficientField m)ˣ) : Relator m
      (freeWeyl (simple false) * freePair (false,0) a *
        (freePair (false,0) (a⁻¹ : (CoefficientField m)ˣ) * freeTorus (fixedTorusEquiv m (linearTau a)) *
          freePair (true,0) (a⁻¹ : (CoefficientField m)ˣ))⁻¹)
  | suzuki_gauss a b (hn : norm a b ≠ 0) : Relator m
      (freeWeyl (simple true) * freeQuartet (false,0) a b *
        (freeQuartet (false,0) (negativeFirst a b) (negativeSecond a b) *
          freeTorus (fixedTorusEquiv m (suzukiTau (Units.mk0 (norm a b) hn))) *
            freeQuartet (true,0) (positiveFirst a b) (positiveSecond a b))⁻¹)

abbrev Group (m : ℕ) := PresentedGroup {w | Relator m w}

def root (m : ℕ) (p : Bool) (i : PositiveTables.Root) : AngularPresentation.Parameter m i →* Group m where
  toFun a := PresentedGroup.of (Letter.root p i a)
  map_one' := PresentedGroup.one_of_mem (Relator.root_one p i)
  map_mul' a b := (mul_inv_eq_one.mp (PresentedGroup.one_of_mem (Relator.root_mul p i a b))).symm

def torus (m : ℕ) : Parabolics.fixedTorus m →* Group m where
  toFun t := PresentedGroup.of (Letter.torus t)
  map_one' := PresentedGroup.one_of_mem Relator.torus_one
  map_mul' a b := (mul_inv_eq_one.mp (PresentedGroup.one_of_mem (Relator.torus_mul a b))).symm

def weyl (m : ℕ) : Weyl →* Group m where
  toFun w := PresentedGroup.of (Letter.weyl w)
  map_one' := PresentedGroup.one_of_mem Relator.weyl_one
  map_mul' a b := (mul_inv_eq_one.mp (PresentedGroup.one_of_mem (Relator.weyl_mul a b))).symm

/-- The abstract alphabet has the required local homomorphisms by its relators. -/
def generators (m : ℕ) : Data m (Group m) where
  x := root m
  h := torus m
  n := weyl m

/-- The abstract equations are consequences of the explicitly displayed relators. -/
theorem relations (m : ℕ) : (generators m).Relations where
  positive i j hj a b := by
    have h := PresentedGroup.one_of_mem (rels := {w | Relator m w}) (Relator.angular i j hj a b)
    rw [map_mul,map_mul,map_mul,map_inv,map_inv,map_word] at h
    exact mul_inv_eq_one.mp h
  torus_root t i a := mul_inv_eq_one.mp (PresentedGroup.one_of_mem (Relator.torus_root t i a))
  weyl_torus s t := mul_inv_eq_one.mp (PresentedGroup.one_of_mem (Relator.weyl_torus s t))
  pair s r a := mul_inv_eq_one.mp (PresentedGroup.one_of_mem (Relator.pair s r a))
  quartet s r a b := mul_inv_eq_one.mp (PresentedGroup.one_of_mem (Relator.quartet s r a b))
  linear_gauss a := mul_inv_eq_one.mp (PresentedGroup.one_of_mem (Relator.linear_gauss a))
  suzuki_gauss a b hn := mul_inv_eq_one.mp (PresentedGroup.one_of_mem (Relator.suzuki_gauss a b hn))

variable {m : ℕ} {G : Type*} [_root_.Group G] (d : Data m G) (R : d.Relations)

def letter : Letter m → G
  | .inl ⟨p,⟨i,a⟩⟩ => d.x p i a
  | .inr (.inl t) => d.h t
  | .inr (.inr w) => d.n w

include R in
theorem relator_eval {w : FreeGroup (Letter m)} (hw : Relator m w) :
    FreeGroup.lift (letter d) w = 1 := by
  cases hw with
  | root_one p i => simp [freeRoot,Letter.root,letter]
  | root_mul p i a b => simp [freeRoot,Letter.root,letter]
  | torus_one => simp [freeTorus,Letter.torus,letter]
  | torus_mul a b => simp [freeTorus,Letter.torus,letter]
  | weyl_one => simp [freeWeyl,Letter.weyl,letter]
  | weyl_mul a b => simp [freeWeyl,Letter.weyl,letter]
  | angular i j hj a b =>
    simpa only [map_mul,map_inv,map_word,freeRoot,FreeGroup.lift_apply_of,Letter.root,Letter.torus,Letter.weyl,letter,mul_inv_eq_one] using R.positive i j hj a b
  | torus_root t i a =>
    simpa only [map_mul,map_inv,freeRoot,freeTorus,FreeGroup.lift_apply_of,Letter.root,Letter.torus,Letter.weyl,letter,mul_inv_eq_one] using R.torus_root t i a
  | weyl_torus s t =>
    simpa only [map_mul,map_inv,freeTorus,freeWeyl,FreeGroup.lift_apply_of,Letter.root,Letter.torus,Letter.weyl,letter,mul_inv_eq_one] using R.weyl_torus s t
  | pair s r a =>
    simpa only [map_mul,map_inv,freePair,freeRoot,freeWeyl,FreeGroup.lift_apply_of,Letter.root,Letter.torus,Letter.weyl,letter,mul_inv_eq_one,Data.pair] using R.pair s r a
  | quartet s r a b =>
    simpa only [map_mul,map_inv,freeQuartet,freeRoot,freeWeyl,FreeGroup.lift_apply_of,Letter.root,Letter.torus,Letter.weyl,letter,mul_inv_eq_one,Data.quartet] using R.quartet s r a b
  | linear_gauss a =>
    simpa only [map_mul,map_inv,freePair,freeRoot,freeTorus,freeWeyl,FreeGroup.lift_apply_of,Letter.root,Letter.torus,Letter.weyl,letter,mul_inv_eq_one,Data.pair,Data.torus] using R.linear_gauss a
  | suzuki_gauss a b hn =>
    simpa only [map_mul,map_inv,freeQuartet,freeRoot,freeTorus,freeWeyl,FreeGroup.lift_apply_of,Letter.root,Letter.torus,Letter.weyl,letter,mul_inv_eq_one,Data.quartet,Data.torus] using R.suzuki_gauss a b hn

/-- Evaluation is constructed from the finite equations. -/
def eval : Group m →* G := PresentedGroup.toGroup (fun _ hw => relator_eval d R hw)

@[simp] theorem eval_root (p : Bool) (i : PositiveTables.Root) (a : AngularPresentation.Parameter m i) :
    eval d R (root m p i a) = d.x p i a := PresentedGroup.toGroup.of _
@[simp] theorem eval_torus (t : Parabolics.fixedTorus m) :
    eval d R (torus m t) = d.h t := PresentedGroup.toGroup.of _
@[simp] theorem eval_weyl (w : Weyl) : eval d R (weyl m w) = d.n w := PresentedGroup.toGroup.of _

end ReeF4.RootPresentationRecognition.Global.Presentation
