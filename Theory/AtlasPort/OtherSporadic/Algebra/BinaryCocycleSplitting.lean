/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/BinaryCocycleSplitting.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.Abel

/-!
# Splitting symmetric binary cocycles

The twisted extension of a normalized symmetric binary cocycle with zero
diagonal is a vector space over the binary field. A linear section of its
projection gives a correcting sign function; differences of corrections are
linear functionals.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/BinaryCocycleSplitting.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Definitions remain exposed for downstream coordinate calculations.
-/

@[expose] public section

namespace Atlas.Algebra

variable {V : Type*} [AddCommGroup V] [hV : Module (ZMod 2) V]

/-- A normalized symmetric binary cocycle with trivial diagonal. These are
explicit cocycle identities, not an assumed splitting. -/
structure SymmetricBinaryCocycle (V : Type*) [AddCommGroup V] where
  toFun : V → V → ZMod 2
  zero_left : ∀ v, toFun 0 v=0
  symmetric : ∀ v w, toFun v w=toFun w v
  diagonal : ∀ v, toFun v v=0
  cocycle : ∀ u v w, toFun u v + toFun (u+v) w = toFun v w + toFun u (v+w)

namespace SymmetricBinaryCocycle

variable (c : SymmetricBinaryCocycle V)

/-- The actual twisted extension associated with the binary cocycle. -/
@[ext] structure Extension (c : SymmetricBinaryCocycle V) where
  vector : V
  sign : ZMod 2

instance : Zero c.Extension := ⟨⟨0,0⟩⟩
instance : Add c.Extension := ⟨fun x y =>
  ⟨x.vector+y.vector,x.sign+y.sign+c.toFun x.vector y.vector⟩⟩
instance : Neg c.Extension := ⟨id⟩

-- Retain the source module parameter in these four public projection identities.
set_option linter.unusedSectionVars false in
@[simp] theorem vector_zero : (0 : c.Extension).vector=0 := rfl
set_option linter.unusedSectionVars false in
@[simp] theorem sign_zero : (0 : c.Extension).sign=0 := rfl
set_option linter.unusedSectionVars false in
@[simp] theorem vector_add (x y : c.Extension) : (x+y).vector=x.vector+y.vector := rfl
set_option linter.unusedSectionVars false in
@[simp] theorem sign_add (x y : c.Extension) :
    (x+y).sign=x.sign+y.sign+c.toFun x.vector y.vector := rfl

lemma vector_add_self (v : V) : v+v=0 := by
  rw [← two_nsmul,← Nat.cast_smul_eq_nsmul (ZMod 2)]
  change (2 : ZMod 2) • v=0
  rw [show (2 : ZMod 2)=0 from rfl, zero_smul]

instance : AddCommGroup c.Extension where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  add_assoc x y z := by
    apply Extension.ext
    · exact add_assoc _ _ _
    · change (x.sign+y.sign+c.toFun x.vector y.vector)+z.sign+
          c.toFun (x.vector+y.vector) z.vector =
        x.sign+(y.sign+z.sign+c.toFun y.vector z.vector)+
          c.toFun x.vector (y.vector+z.vector)
      calc
        _ = x.sign+y.sign+z.sign+
            (c.toFun x.vector y.vector+c.toFun (x.vector+y.vector) z.vector) := by abel
        _ = x.sign+y.sign+z.sign+
            (c.toFun y.vector z.vector+c.toFun x.vector (y.vector+z.vector)) := by
              rw [c.cocycle]
        _ = _ := by abel
  zero_add x := by
    apply Extension.ext <;> simp [c.zero_left]
  add_zero x := by
    apply Extension.ext
    · exact add_zero _
    · change x.sign+0+c.toFun x.vector 0=x.sign
      rw [c.symmetric,c.zero_left]
      simp
  add_comm x y := by
    apply Extension.ext
    · exact add_comm _ _
    · change x.sign+y.sign+c.toFun x.vector y.vector =
        y.sign+x.sign+c.toFun y.vector x.vector
      rw [c.symmetric x.vector y.vector,add_comm x.sign y.sign]
  neg_add_cancel x := by
    apply Extension.ext
    · exact vector_add_self x.vector
    · change x.sign+x.sign+c.toFun x.vector x.vector=0
      rw [c.diagonal,CharTwo.add_self_eq_zero,add_zero]
  nsmul := nsmulRec
  zsmul := zsmulRec

lemma twice_eq_zero (x : c.Extension) : 2 • x=0 := by
  rw [two_nsmul]
  exact neg_add_cancel x

instance : Module (ZMod 2) c.Extension := AddCommGroup.zmodModule (twice_eq_zero c)

/-- Projection of the twisted extension is an actual linear surjection. -/
def projection : c.Extension →ₗ[ZMod 2] V :=
  (show c.Extension →+ V from {
    toFun := Extension.vector
    map_zero' := rfl
    map_add' := fun _ _ => rfl }).toZModLinearMap 2

lemma projection_surjective : Function.Surjective c.projection :=
  fun v => ⟨⟨v,0⟩,rfl⟩

include hV in
/-- Splitting the elementary abelian extension produces the correcting sign
function. This uses only linear splitting over the binary field. -/
theorem exists_correction : ∃ η : V → ZMod 2, η 0=0 ∧
    ∀ u v, η (u+v)+η u+η v=c.toFun u v := by
  obtain ⟨s,hs⟩ := c.projection.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr c.projection_surjective)
  have hsv (v : V) : (s v).vector=v := LinearMap.congr_fun hs v
  refine ⟨fun v => (s v).sign,?_,?_⟩
  · change (s 0).sign=0
    rw [map_zero]
    rfl
  · intro u v
    change (s (u+v)).sign+(s u).sign+(s v).sign=c.toFun u v
    have he := congrArg Extension.sign (s.map_add u v)
    change (s (u+v)).sign=(s u).sign+(s v).sign+c.toFun (s u).vector (s v).vector at he
    rw [hsv,hsv] at he
    rw [he]
    have hc := CharTwo.add_self_eq_zero ((s u).sign+(s v).sign)
    calc
      _ = c.toFun u v + (((s u).sign+(s v).sign)+((s u).sign+(s v).sign)) := by abel
      _ = c.toFun u v := by rw [hc,add_zero]

end SymmetricBinaryCocycle

include hV in
/-- Every normalized symmetric binary cocycle with zero diagonal is the
coboundary of a normalized sign function, in arbitrary dimension. -/
theorem binary_cocycle_exists_correction (δ : V → V → ZMod 2)
    (hzero : ∀ v, δ 0 v=0) (hsymm : ∀ u v, δ u v=δ v u)
    (hdiag : ∀ v, δ v v=0)
    (hcocycle : ∀ u v w, δ u v+δ (u+v) w+δ v w+δ u (v+w)=0) :
    ∃ η : V → ZMod 2, η 0=0 ∧ ∀ u v, η (u+v)+η u+η v=δ u v := by
  let c : SymmetricBinaryCocycle V := {
    toFun := δ
    zero_left := hzero
    symmetric := hsymm
    diagonal := hdiag
    cocycle := by
      intro u v w
      have h := hcocycle u v w
      have he : (δ u v+δ (u+v) w)+(δ v w+δ u (v+w))=0 := by
        simpa only [add_assoc] using h
      exact (eq_neg_of_add_eq_zero_left he).trans (CharTwo.neg_eq _) }
  exact c.exists_correction

/-- Any two normalized sign corrections differ by an actual binary linear
functional. Thus the freedom in the lift is precisely linear, not arbitrary. -/
theorem binary_corrections_differ_by_linear (δ : V → V → ZMod 2)
    (η θ : V → ZMod 2) (hηzero : η 0=0) (hθzero : θ 0=0)
    (hη : ∀ u v, η (u+v)+η u+η v=δ u v)
    (hθ : ∀ u v, θ (u+v)+θ u+θ v=δ u v) :
    ∃ l : V →ₗ[ZMod 2] ZMod 2, ∀ v, l v=η v+θ v := by
  let f : V →+ ZMod 2 := {
    toFun := fun v => η v+θ v
    map_zero' := by rw [hηzero,hθzero,add_zero]
    map_add' := by
      intro u v
      have he : (η (u+v)+θ (u+v))+((η u+θ u)+(η v+θ v))=0 := by
        calc
          _ = (η (u+v)+η u+η v)+(θ (u+v)+θ u+θ v) := by abel
          _ = δ u v+δ u v := by rw [hη,hθ]
          _ = 0 := CharTwo.add_self_eq_zero _
      exact (eq_neg_of_add_eq_zero_left he).trans (CharTwo.neg_eq _) }
  exact ⟨f.toZModLinearMap 2,fun _ => rfl⟩

/-- Adding any binary linear functional preserves the correcting equation. -/
theorem binary_correction_add_linear (δ : V → V → ZMod 2) (η : V → ZMod 2)
    (hηzero : η 0=0) (hη : ∀ u v, η (u+v)+η u+η v=δ u v)
    (l : V →ₗ[ZMod 2] ZMod 2) :
    (η 0+l 0=0) ∧ ∀ u v,
      (η (u+v)+l (u+v))+(η u+l u)+(η v+l v)=δ u v := by
  constructor
  · rw [hηzero,map_zero,add_zero]
  · intro u v
    rw [map_add]
    calc
      _ = (η (u+v)+η u+η v)+((l u+l v)+(l u+l v)) := by abel
      _ = δ u v := by rw [hη,CharTwo.add_self_eq_zero,add_zero]

end Atlas.Algebra
