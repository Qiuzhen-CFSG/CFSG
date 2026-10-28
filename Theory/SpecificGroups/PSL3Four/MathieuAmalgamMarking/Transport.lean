module

public import Theory.SpecificGroups.PSL3Four.MathieuAmalgamMarking.Marks

/-!
# The exact linear relators on an original marked subgroup

Pulling back the canonical pair gives two generators of the same original
parabolic. The first thirteen words use only the linear generator slots,
so the fourth generator may be any element of the original ambient group.
-/

public noncomputable section
open Subgroup Subgroup.CosetWordCertificate Matrix
namespace Matrix.PSL3Four.MathieuAmalgamMarking
open Theory.SpecificGroups.MathieuAmalgamCompletion
variable {G : Type*} [Group G]

private theorem eval_hom {H α : Type*} [Group H] (f : H→*G)
    (g : α→H) (w : Word α) : f (eval g w)=eval (fun i => f (g i)) w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons,eval_cons,map_mul,ih]
    cases a with
    | mk a b => cases b <;> simp

private theorem eval_agrees {α : Type*} (g h : α→G) (w : Word α)
    (ha : ∀ a∈w,g a.1=h a.1) : eval g w=eval h w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons,eval_cons,ha a (by simp),ih (fun b hb => ha b (by simp [hb]))]

private theorem first_support : ∀ i : Fin 13,
    ∀ a∈relator ⟨i.val,by omega⟩, a.1.val<3 := by decide +kernel

/-- The same original parabolic has a generating pair satisfying all thirteen
linear-side words with the specified exterior cubic and any fourth element. -/
theorem exists_original_linear_relators (P L : Subgroup G) (hPL : P≤L)
    (e : L≃*PSL) (hP : (P.subgroupOf L).map e.toMonoidHom=Matrix.PSL3.LinearThree.pointParabolic F)
    (ell : G) (hell : ell∈L) (he : e ⟨ell,hell⟩=cycle) :
    ∃ p : Fin 2→G, closure (Set.range p)=P ∧
      (∀ i,p i∈P) ∧
      ∀ (n : G) (i : Fin 13),
        eval ![p 0,p 1,ell,n] (relator ⟨i.val,by omega⟩)=1 := by
  let k : PSL→*G := L.subtype.comp e.symm.toMonoidHom
  let p : Fin 2→G := fun i => k (pair i)
  have hkP : (Matrix.PSL3.LinearThree.pointParabolic F).map k=P := by
    rw [←hP,Subgroup.map_map]
    have hh : k.comp e.toMonoidHom=L.subtype := by
      ext x
      exact congrArg Subtype.val (e.symm_apply_apply x)
    rw [hh,subgroupOf_map_subtype,inf_eq_left.mpr hPL]
  have hp : closure (Set.range p)=P := by
    have hh := congrArg (Subgroup.map k) pair_generates_point
    rw [MonoidHom.map_closure,←Set.range_comp,hkP] at hh
    exact hh
  have hkcycle : k cycle=ell := by
    rw [←he]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨ell,hell⟩)
  refine ⟨p,hp,fun i => hp ▸ subset_closure ⟨i,rfl⟩,?_⟩
  intro n i
  have hsame : eval ![p 0,p 1,ell,n] (relator ⟨i.val,by omega⟩)=
      eval (fun j => k (generator j)) (relator ⟨i.val,by omega⟩) := by
    apply eval_agrees
    intro a ha
    have hb := first_support i a ha
    have hj : a.1=0 ∨ a.1=1 ∨ a.1=2 := by
      rcases a with ⟨j,b⟩
      fin_cases j <;> simp_all
    rcases hj with hj | hj | hj <;> rw [hj]
    · rfl
    · rfl
    · exact hkcycle.symm
  rw [hsame,←eval_hom,first_relators,map_one]

end Matrix.PSL3Four.MathieuAmalgamMarking
