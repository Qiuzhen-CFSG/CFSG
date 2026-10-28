module

public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourcePlaneCensus
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourcePlaneCensus

/-!
# Rectangle fusion counts from the two root orbits

The existing eight-orbit normal form reduces an invariant subset of the
64-element rectangle to its orbit-selection vector. Inclusion of the two
root orbits and exclusion of the non-root core orbit leave eight choices.
Equality of additive pair counts at the marked point and one row root
eliminates all choices except those of size 21 or 45.

The internal import intentionally reuses the checked orbit words, labels,
and selection function; it does not expose them as a new public API.
Source: Aschbacher, *Sporadic Groups* (1994), 39.1(7), 39.10 and 40.2,
pp.213–217. This counting proof replaces the intermediate 40.1 argument;
the root-fusion and core-exclusion premises still have to be supplied.
-/

open Theory.GroupTheory.TransvectionFive.UniquenessLinear.PlaneCensus
namespace Theory.GroupTheory.TransvectionFive.FusionTypesCensus

private theorem candidates : ∀ a b c : Bool,
    let m : Fin 8 → Bool := ![false,true,true,a,b,c,true,false]
    pairCount (selected m) 1 = pairCount (selected m) 4 →
      (selected m).card = 21 ∨ (selected m).card = 45 := by decide +kernel

/-- The two root orbits and exclusion of the non-root core orbit force the
source 40.2 counts. Only equality of the pair counts at 1 and 4 is needed. -/
public theorem card_dichotomy (s : Finset Code) (h0 : (0 : Code) ∉ s)
    (h1 : (1 : Code) ∈ s) (h4 : (4 : Code) ∈ s) (h32 : (32 : Code) ∈ s)
    (h33 : (33 : Code) ∉ s)
    (h : ∀ (k : Fin 5) (x : Code), shear k x ∈ s ↔ x ∈ s)
    (hpair : pairCount s 1 = pairCount s 4) : s.card = 21 ∨ s.card = 45 := by
  classical
  let m : Fin 8 → Bool := fun i => decide (representative i ∈ s)
  have he : s = selected m := by
    ext x
    have hh := mem_fold s h (path x) x
    rw [normal_form] at hh
    simpa only [selected, Finset.mem_filter, Finset.mem_univ, true_and,
      m, decide_eq_true_eq] using hh.symm
  have hm : m = ![false,true,true,m 3,m 4,m 5,true,false] := by
    funext i
    fin_cases i <;> first
      | exact decide_eq_false h0
      | exact decide_eq_true h1
      | exact decide_eq_true h4
      | exact decide_eq_true h32
      | exact decide_eq_false h33
      | rfl
  rw [he,hm] at hpair ⊢
  exact candidates _ _ _ hpair

end Theory.GroupTheory.TransvectionFive.FusionTypesCensus
