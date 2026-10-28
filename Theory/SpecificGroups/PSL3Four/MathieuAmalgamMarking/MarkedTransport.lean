module

public import Theory.SpecificGroups.PSL3Four.MathieuAmalgamMarking.Transport
public import Theory.SpecificGroups.PSL3Four.MathieuAmalgamMarking.TorusLine

/-!
# Retaining the shared words in the original generating pair

The same canonical preimage pair retains both its reflection word and its
cubic line. The exact linear relators therefore coexist with the original
inverter and original cubic centralizer used to construct the hexad element.
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

/-- The literal canonical point reflection is the standard simple reflection. -/
theorem reflection_eq_standard : reflection=Matrix.PSL3.SmallCompletion.reflection F false := by
  apply congrArg (Matrix.PSL3.projection F)
  apply Subtype.ext
  change nativeReflection.val.map Representation.SL2FourNatural.fieldEquiv.toRingHom = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nativeReflection,Matrix.PSL3.SmallCompletion.reflectionSL]

/-- One original generating pair retains all thirteen linear relations,
the same literal inverter word and the same cubic line. -/
theorem exists_original_marked_linear_relators (P L : Subgroup G) (hPL : P≤L)
    (e : L≃*PSL) (hP : (P.subgroupOf L).map e.toMonoidHom=Matrix.PSL3.LinearThree.pointParabolic F)
    (ell r t : G) (hell : ell∈L) (hr : r∈L) (ht : t∈P)
    (he : e ⟨ell,hell⟩=cycle) (her : e ⟨r,hr⟩=reflection)
    (ht3 : orderOf t=3) (htell : Commute t ell) :
    ∃ p : Fin 2→G, closure (Set.range p)=P ∧ (∀ i,p i∈P) ∧
      (∀ i,p i=(e.symm (pair i):G)) ∧
      eval p reflectionWord=r ∧ zpowers (eval p torusWord)=zpowers t ∧
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
  have hkr : k reflection=r := by
    rw [←her]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨r,hr⟩)
  have hwordr : eval p reflectionWord=r := by
    rw [show eval p reflectionWord=k (eval pair reflectionWord) from (eval_hom k pair _).symm,
      reflection_word,hkr]
  let tL : L := ⟨t,hPL ht⟩
  have htp : e tL∈Matrix.PSL3.LinearThree.pointParabolic F :=
    hP ▸ mem_map_of_mem e.toMonoidHom ht
  have htL3 : orderOf (e tL)=3 := (e.orderOf_eq tL).trans ((orderOf_coe tL).symm.trans ht3)
  have htc : Commute (e tL) cycle := by
    rw [←he]
    exact (show Commute tL (⟨ell,hell⟩:L) from Subtype.ext htell.eq).map e.toMonoidHom
  have htline := congrArg (Subgroup.map k) (point_cycle_cubic_line (e tL) htp htL3 htc)
  rw [MonoidHom.map_zpowers,MonoidHom.map_zpowers] at htline
  have hkt : k (e tL)=t := congrArg Subtype.val (e.symm_apply_apply tL)
  rw [hkt] at htline
  have hwordt : zpowers (eval p torusWord)=zpowers t := by
    rw [show eval p torusWord=k (eval pair torusWord) from (eval_hom k pair _).symm,
      torus_word]
    exact htline.symm
  refine ⟨p,hp,fun i => hp ▸ subset_closure ⟨i,rfl⟩,fun _ => rfl,hwordr,hwordt,?_⟩
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
