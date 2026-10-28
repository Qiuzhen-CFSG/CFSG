module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourcePlaneCensus
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourcePlaneCensus

/-!
# Single-root rectangle fusion census

The eight checked point-stabilizer orbits leave eight candidate fusion
sets when precisely one root orbit is included and the mixed orbit is
excluded. Normalizer fusion makes additive pair counts constant. Direct
64-element certificates eliminate every candidate except the seven row
points or the three column points, respectively.

This supplies the counting step in Aschbacher, *Sporadic Groups* (1994),
39.7–39.8, pp.214–216. It also excludes the putative 27-point set directly,
using the same literal additive coordinates as the ambient normalizer action.
The internal import reuses the established orbit words and decoder labels.
-/

open Theory.GroupTheory.TransvectionFive.UniquenessLinear.PlaneCensus
namespace Theory.GroupTheory.TransvectionFive.CoreFusionCensus

private def rowOnly : Finset Code := Finset.univ.filter (fun x => x ≠ 0 ∧ x >>> 3 = 0)
private def columnOnly : Finset Code := {4,32,36}

private theorem one_root_candidates : ∀ a b c : Bool,
    let m : Fin 8 → Bool := ![false,true,true,a,b,c,false,false]
    (∀ x ∈ selected m, pairCount (selected m) x = pairCount (selected m) 4) →
      selected m = rowOnly := by decide +kernel

private theorem other_root_candidates : ∀ a b c : Bool,
    let m : Fin 8 → Bool := ![false,false,true,a,b,c,true,false]
    (∀ x ∈ selected m, pairCount (selected m) x = pairCount (selected m) 4) →
      selected m = columnOnly := by decide +kernel

private theorem invariant_eq_selected (s : Finset Code)
    (h : ∀ (k : Fin 5) (x : Code), shear k x ∈ s ↔ x ∈ s) :
    s = selected (fun i => decide (representative i ∈ s)) := by
  ext x
  have hh := mem_fold s h (path x) x
  rw [normal_form] at hh
  simpa only [selected,Finset.mem_filter,Finset.mem_univ,true_and,decide_eq_true_eq]
    using hh.symm

/-- If only the row root orbit fuses, the entire rectangle fusion set is
its seven nonzero row vectors. -/
public theorem row_only (s : Finset Code) (h0 : (0 : Code) ∉ s)
    (h1 : (1 : Code) ∈ s) (h4 : (4 : Code) ∈ s) (h32 : (32 : Code) ∉ s)
    (h33 : (33 : Code) ∉ s)
    (h : ∀ (k : Fin 5) (x : Code), shear k x ∈ s ↔ x ∈ s)
    (hpair : ∀ x ∈ s, pairCount s x = pairCount s 4) :
    ∀ x : Code, x ∈ s ↔ x ≠ 0 ∧ x >>> 3 = 0 := by
  classical
  let m : Fin 8 → Bool := fun i => decide (representative i ∈ s)
  have he : s = selected m := invariant_eq_selected s h
  have hm : m = ![false,true,true,m 3,m 4,m 5,false,false] := by
    funext i
    fin_cases i <;> first
      | exact decide_eq_false h0
      | exact decide_eq_true h1
      | exact decide_eq_true h4
      | exact decide_eq_false h32
      | exact decide_eq_false h33
      | rfl
  rw [he,hm] at hpair ⊢
  rw [one_root_candidates _ _ _ hpair]
  intro x
  simp [rowOnly]

/-- If only the column root orbit fuses, the entire rectangle fusion set
is its three nonzero column vectors. -/
public theorem column_only (s : Finset Code) (h0 : (0 : Code) ∉ s)
    (h1 : (1 : Code) ∉ s) (h4 : (4 : Code) ∈ s) (h32 : (32 : Code) ∈ s)
    (h33 : (33 : Code) ∉ s)
    (h : ∀ (k : Fin 5) (x : Code), shear k x ∈ s ↔ x ∈ s)
    (hpair : ∀ x ∈ s, pairCount s x = pairCount s 4) :
    ∀ x : Code, x ∈ s ↔ x = 4 ∨ x = 32 ∨ x = 36 := by
  classical
  let m : Fin 8 → Bool := fun i => decide (representative i ∈ s)
  have he : s = selected m := invariant_eq_selected s h
  have hm : m = ![false,false,true,m 3,m 4,m 5,true,false] := by
    funext i
    fin_cases i <;> first
      | exact decide_eq_false h0
      | exact decide_eq_false h1
      | exact decide_eq_true h4
      | exact decide_eq_true h32
      | exact decide_eq_false h33
      | rfl
  rw [he,hm] at hpair ⊢
  rw [other_root_candidates _ _ _ hpair]
  intro x
  simp [columnOnly]

end Theory.GroupTheory.TransvectionFive.CoreFusionCensus
