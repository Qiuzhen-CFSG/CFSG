module

public import Theory.SpecificGroups.BinaryLinear.AffineThree.Heisenberg
public import Theory.SpecificGroups.BinaryLinear.AffinePointCore
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Coordinates of the binary affine three-space point centralizer

Projection to the lower two-dimensional block is onto SL₂(2). Its kernel
is the concrete five-coordinate Heisenberg group, embedded with its literal
translation and upper-row coordinates. This identifies the intrinsic two-core,
its extraspecial structure and order 32, and the actual S₃ quotient.

Source: Aschbacher–Smith 12.2.27(2) and I.4.6, printed pp.807,417.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

open Subgroup Matrix
namespace BinaryLinear.Affine.ThreeLocal
open ThreeCore Theory.GroupTheory.TranslationCentralizer
abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
abbrev SL3 := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
def e0 : Multiplicative (Fin 3 → ZMod 2) := Multiplicative.ofAdd ![1,0,0]
abbrev H := centralizer (action 3) e0
instance : Finite (Model 3) := Finite.of_injective
  (fun x => (x.left, x.right)) (fun _ _ h => SemidirectProduct.ext
    (congrArg Prod.fst h) (congrArg Prod.snd h))

theorem first_column (x : H) (i : Fin 3) :
    (x.val.right : Matrix (Fin 3) (Fin 3) (ZMod 2)) i 0 = (![1,0,0] : Fin 3 → ZMod 2) i := by
  have h := (mem_iff (action 3) e0 x.val).mp x.property
  have hh := congrArg (fun v : Multiplicative (Fin 3 → ZMod 2) => v.toAdd i) h
  change ((x.val.right : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec ![1,0,0]) i = _ at hh
  simpa [e0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using hh

def tailMatrix (x : H) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  fun i j => (x.val.right : Matrix (Fin 3) (Fin 3) (ZMod 2)) i.succ j.succ

theorem tail_det (x : H) : (tailMatrix x).det = 1 := by
  have h := x.val.right.property
  change (x.val.right : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 at h
  rw [Matrix.det_fin_three] at h
  rw [first_column x 0, first_column x 1, first_column x 2] at h
  simpa [tailMatrix, Matrix.det_fin_two] using h

def projection : H →* SL2 where
  toFun x := ⟨tailMatrix x, tail_det x⟩
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_mul' x y := by
    apply Subtype.ext
    ext i j
    change ((x.val.right : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      (y.val.right : Matrix (Fin 3) (Fin 3) (ZMod 2))) i.succ j.succ =
        (tailMatrix x * tailMatrix y) i j
    simp only [Matrix.mul_apply, Fin.sum_univ_succ]
    fin_cases i <;> fin_cases j <;>
      simp [tailMatrix, first_column, Fin.sum_univ_succ]

def upper (a b : ZMod 2) : SL3 :=
  ⟨!![1,a,b; 0,1,0; 0,0,1], by simp [Matrix.det_fin_three]⟩

def embed : Q →* H where
  toFun q := ⟨⟨Multiplicative.ofAdd ![q.z,q.c,q.d], upper q.a q.b⟩,
    (mem_iff (action 3) e0 _).mpr (by
      change Multiplicative.ofAdd ((upper q.a q.b).val.mulVec ![1,0,0]) = e0
      congr 1
      ext i
      fin_cases i <;> simp [upper, e0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ])⟩
  map_one' := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd ![0,0,0] = Multiplicative.ofAdd 0
      congr 1
      ext i
      fin_cases i <;> rfl
    · apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
  map_mul' q r := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd ![(q*r).z,(q*r).c,(q*r).d] =
        Multiplicative.ofAdd (![q.z,q.c,q.d] + (upper q.a q.b).val.mulVec ![r.z,r.c,r.d])
      congr 1
      ext i
      change ![q.z+r.z+q.a*r.c+q.b*r.d,q.c+r.c,q.d+r.d] i = _
      fin_cases i <;> simp [upper, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      ring
    · apply Subtype.ext
      ext i j
      change (upper (q*r).a (q*r).b).val i j =
        ((upper q.a q.b).val * (upper r.a r.b).val) i j
      fin_cases i <;> fin_cases j <;>
        simp [upper, Matrix.mul_apply, Fin.sum_univ_succ]
      all_goals exact add_comm _ _

theorem embed_injective : Function.Injective embed := by
  intro q r h
  have ht := congrArg (fun x : H => x.val.left.toAdd) h
  have ha := congrArg (fun x : H => (x.val.right : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 1) h
  have hb := congrArg (fun x : H => (x.val.right : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 2) h
  exact Q.ext (congrFun ht 0) ha hb (congrFun ht 1) (congrFun ht 2)



def liftMatrix (g : SL2) : SL3 :=
  ⟨!![1,0,0; 0,g.val 0 0,g.val 0 1; 0,g.val 1 0,g.val 1 1], by
    have h : g.val.det = 1 := g.property
    rw [Matrix.det_fin_two] at h
    simpa [Matrix.det_fin_three] using h⟩

def lift (g : SL2) : H :=
  ⟨⟨1,liftMatrix g⟩, (mem_iff (action 3) e0 _).mpr (by
    change Multiplicative.ofAdd ((liftMatrix g).val.mulVec ![1,0,0]) = e0
    congr 1
    ext i
    fin_cases i <;> simp [liftMatrix, e0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ])⟩

theorem projection_lift (g : SL2) : projection (lift g) = g := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem projection_surjective : Function.Surjective projection :=
  fun g => ⟨lift g, projection_lift g⟩

theorem range_embed : embed.range = projection.ker := by
  ext x
  constructor
  · rintro ⟨q,rfl⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro hx
    have hm : tailMatrix x = 1 := congrArg Subtype.val hx
    let q : Q := ⟨x.val.left.toAdd 0,
      x.val.right.val 0 1, x.val.right.val 0 2,
      x.val.left.toAdd 1, x.val.left.toAdd 2⟩
    refine ⟨q, ?_⟩
    apply Subtype.ext
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd ![q.z,q.c,q.d] = x.val.left
      apply congrArg Multiplicative.ofAdd
      ext i
      fin_cases i <;> rfl
    · apply Subtype.ext
      ext i j
      change (upper q.a q.b).val i j = x.val.right.val i j
      have hh (i j : Fin 2) := congrFun (congrFun hm i) j
      fin_cases i <;> fin_cases j
      all_goals first
        | simpa [upper] using (first_column x 0).symm
        | simpa [upper] using (first_column x 1).symm
        | simpa [upper] using (first_column x 2).symm
        | rfl
        | exact (hh 0 0).symm
        | exact (hh 0 1).symm
        | exact (hh 1 0).symm
        | exact (hh 1 1).symm

noncomputable def kernelEquiv : Q ≃* projection.ker :=
  (MonoidHom.ofInjective embed_injective).trans (MulEquiv.subgroupCongr range_embed)

theorem kernel_isPGroup : IsPGroup 2 projection.ker := by
  apply IsPGroup.of_card (n := 5)
  rw [← Nat.card_congr kernelEquiv.toEquiv, card_Q]
  norm_num

theorem kernel_eq_core : projection.ker = pCore 2 H := by
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  have hk : (e.toMonoidHom.comp projection).ker = projection.ker :=
    MonoidHom.ker_comp_of_injective projection e.toMonoidHom e.injective
  have he := ker_eq_twoCore_of_surjective_perm_three (e.toMonoidHom.comp projection)
    (e.surjective.comp projection_surjective) (hk ▸ kernel_isPGroup)
  exact hk.symm.trans he

noncomputable def coreEquiv : Q ≃* pCore 2 H :=
  kernelEquiv.trans (MulEquiv.subgroupCongr kernel_eq_core)

theorem core_extraspecial : IsExtraspecial 2 (pCore 2 H) :=
  IsExtraspecial.of_mulEquiv coreEquiv extraspecial

theorem core_card : Nat.card (pCore 2 H) = 32 :=
  (Nat.card_congr coreEquiv.toEquiv).symm.trans card_Q

noncomputable def quotientEquiv : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3) :=
  (QuotientGroup.quotientMulEquivOfEq kernel_eq_core.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective projection projection_surjective).trans
      (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three))

end BinaryLinear.Affine.ThreeLocal
