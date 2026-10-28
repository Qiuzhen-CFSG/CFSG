module
public import Theory.Representation.SL3.DualInvariantLines

/-!
# Natural summands in a doubled SL₃ module

The nonzero proper additive invariant subgroups of F³ ⊕ F³ are exactly
its scalar graphs and the second axis. The existing transvection argument
proves exhaustiveness without assuming field-linearity. Here these subgroups
are indexed injectively by the projective line `Option F`.

This finite odd family supplies a two-group-invariant central flag in the
nonbinary linear-three MS analysis. Source: the elementary module argument
used with Aschbacher–Smith C.1.34, printed pp.136–137; compare C.1.35,
pp.137–139, for the corresponding family in the doubled dual quotient.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Representation.SL3ParabolicNatural
variable {F : Type*} [Field F]
local notation "W" => (Fin 3 → F)
local notation "V" => (W × W)

/-- The projective line of natural summands, with the second axis at infinity. -/
def naturalLine (a : Option F) : Subgroup (Multiplicative V) :=
  match a with
  | none => (AddMonoidHom.fst W W).toMultiplicative.ker
  | some a =>
    ({ toFun := fun v : V => v.2 - a • v.1
       map_zero' := by simp
       map_add' := by intros; simp only [Prod.fst_add,Prod.snd_add,smul_add]; abel } :
      V →+ W).toMultiplicative.ker

theorem mem_naturalLine_none (v : Multiplicative V) :
    v ∈ naturalLine (none : Option F) ↔ v.toAdd.1 = 0 := Iff.rfl

theorem mem_naturalLine_some (a : F) (v : Multiplicative V) :
    v ∈ naturalLine (some a) ↔ v.toAdd.2 = a • v.toAdd.1 := by
  change v.toAdd.2 - a • v.toAdd.1 = 0 ↔ _
  exact sub_eq_zero

theorem naturalLine_invariant (a : Option F) (g : SL(3,F)) (v : Multiplicative V)
    (hv : v ∈ naturalLine a) :
    Multiplicative.ofAdd (specialLinearNatural 3 g v.toAdd.1,
      specialLinearNatural 3 g v.toAdd.2) ∈ naturalLine a := by
  cases a with
  | none =>
    rw [mem_naturalLine_none] at hv ⊢
    change specialLinearNatural 3 g v.toAdd.1=0
    rw [hv,map_zero]
  | some a =>
    rw [mem_naturalLine_some] at hv ⊢
    change specialLinearNatural 3 g v.toAdd.2=a • specialLinearNatural 3 g v.toAdd.1
    rw [hv,map_smul]

theorem naturalLine_ne_bot (a : Option F) : naturalLine a ≠ ⊥ := by
  let w : W := fun _ => 1
  have hw : w ≠ 0 := fun he => one_ne_zero (congrFun he 0)
  cases a with
  | none =>
    intro he
    have hm : Multiplicative.ofAdd (0,w) ∈ naturalLine (none : Option F) := rfl
    rw [he,mem_bot] at hm
    exact hw (congrArg (fun v : Multiplicative V => v.toAdd.2) hm)
  | some a =>
    intro he
    have hm := (mem_naturalLine_some a (Multiplicative.ofAdd (w,a • w))).mpr rfl
    rw [he,mem_bot] at hm
    exact hw (congrArg (fun v : Multiplicative V => v.toAdd.1) hm)

theorem naturalLine_ne_top (a : Option F) : naturalLine a ≠ ⊤ := by
  let w : W := fun _ => 1
  have hw : w ≠ 0 := fun he => one_ne_zero (congrFun he 0)
  cases a with
  | none =>
    intro he
    have hm : Multiplicative.ofAdd (w,0) ∈ naturalLine (none : Option F) :=
      he.symm ▸ mem_top _
    exact hw ((mem_naturalLine_none _).mp hm)
  | some a =>
    intro he
    have hm : Multiplicative.ofAdd (0,w) ∈ naturalLine (some a) := he.symm ▸ mem_top _
    have hh := (mem_naturalLine_some _ _).mp hm
    exact hw (hh.trans (smul_zero _))

theorem naturalLine_injective : Function.Injective (naturalLine (F := F)) := by
  let w : W := fun _ => 1
  have hw : w ≠ 0 := fun he => one_ne_zero (congrFun he 0)
  intro a b he
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      have hm := (mem_naturalLine_some b (Multiplicative.ofAdd (w,b • w))).mpr rfl
      rw [←he,mem_naturalLine_none] at hm
      exact (hw hm).elim
  | some a =>
    have hm := (mem_naturalLine_some a (Multiplicative.ofAdd (w,a • w))).mpr rfl
    rw [he] at hm
    cases b with
    | none => exact (hw ((mem_naturalLine_none _).mp hm)).elim
    | some b => exact congrArg some (smul_left_injective F hw ((mem_naturalLine_some _ _).mp hm))

/-- The natural projective-line family exhausts all nonzero proper additive
invariant subgroups. No field-linearity of the subgroup is assumed. -/
theorem invariant_natural_subgroup_eq_line (D : Subgroup (Multiplicative V))
    (hne : D ≠ ⊥) (hlt : D ≠ ⊤)
    (hD : ∀ g : SL(3,F), ∀ v ∈ D, Multiplicative.ofAdd
      (specialLinearNatural 3 g v.toAdd.1,specialLinearNatural 3 g v.toAdd.2) ∈ D) :
    ∃ a : Option F, D = naturalLine a := by
  let E : AddSubgroup V :=
    { carrier := {v | Multiplicative.ofAdd v ∈ D}
      zero_mem' := D.one_mem
      add_mem' := D.mul_mem
      neg_mem' := D.inv_mem }
  have hne' : E ≠ ⊥ := by
    intro hh
    apply hne
    ext v
    change v ∈ D ↔ v = 1
    exact (show v.toAdd ∈ E ↔ v.toAdd = 0 by rw [hh]; rfl)
  have hlt' : E ≠ ⊤ := by
    intro hh
    apply hlt
    apply top_unique
    intro v _
    exact (show v.toAdd ∈ E from hh.symm ▸ AddSubgroup.mem_top _)
  rcases invariant_double_natural_classification E hne' hlt'
    (fun g v hv => hD g (Multiplicative.ofAdd v) hv) with hz | ⟨a,ha⟩
  · refine ⟨none,?_⟩
    ext v
    exact (hz v.toAdd).trans (mem_naturalLine_none v).symm
  · refine ⟨some a,?_⟩
    ext v
    exact (ha v.toAdd).trans (mem_naturalLine_some a v).symm

end Representation.SL3ParabolicNatural
