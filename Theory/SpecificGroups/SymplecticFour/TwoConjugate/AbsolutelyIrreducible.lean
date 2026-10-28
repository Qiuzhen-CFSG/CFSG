module
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.MovingPair
public import Theory.Representation.AbsolutelyIrreducible
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Absolute irreducibility of the original opposite central-root pair

Two independent central parameters isolate a rank-one operator in the
F-linear span of the upper displacements. Every endomorphism commuting
with the opposite pair therefore preserves a coordinate line. The proved
irreducibility makes such an endomorphism scalar, which is the Schur
criterion for absolute irreducibility over the same coefficient field.

This strengthens the irreducibility step of Aschbacher--Smith E.2.7,
printed pp.219--220, for the binary PSL2 representation-recognition branch.
The rank-one operator need not be a group element or a single displacement;
no root element in the pair is assumed.
-/

public section
open Matrix Subgroup
open Representation.OneCohomology.SymplecticFour
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Theory.SpecificGroups.SymplecticFour.TwoConjugate
variable {F : Type*} [Field F] [CharP F 2]
local notation "a" => (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "b" => (Sum.inl (1 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "c" => (Sum.inr (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "d" => (Sum.inr (1 : Fin 2) : Fin 2 ⊕ Fin 2)

private theorem upper_difference (s t : F) (x : Vector F) :
    upper s t • x - x =
      s • (x c • Pi.single a 1) + t • (x d • Pi.single a 1 + x c • Pi.single b 1) := by
  rw [upper_apply]
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [Pi.single_apply] <;> ring

/-- Independent central parameters force absolute irreducibility of the
same opposite pair, without a root-element assumption. -/
theorem pairAction_absolutelyIrreducible_of_independent (V : Subgroup (Sp F)) (s t u v : F) (hdet : s*v-u*t≠0)
    (h₁ : upper s t∈V) (h₂ : upper u v∈V) :
    Representation.IsAbsolutelyIrreducible (pairAction V) := by
  let _ := pairAction_irreducible_of_independent V s t u v hdet h₁ h₂
  apply (Representation.isAbsolutelyIrreducible_iff_surjective (pairAction V)).mpr
  intro f
  let ea : Vector F := Pi.single a 1
  let eb : Vector F := Pi.single b 1
  let ec : Vector F := Pi.single c 1
  let q : F := (f ec) c
  have hu (p r : F) (h : upper p r∈V) :
      p • f ea + r • f eb = p • (q • ea) +
        r • ((f ec) d • ea + q • eb) := by
    have hh := congrArg (fun x : Vector F => x-f ec)
      (Representation.IntertwiningMap.isIntertwining (pairAction V) (pairAction V) (f := f)
        (⟨upper p r,(show V≤oppositePair V from le_sup_left) h⟩ : oppositePair V) ec)
    change f (upper p r • ec) - f ec = upper p r • f ec - f ec at hh
    rw [←map_sub,upper_difference,upper_difference] at hh
    simpa [ea,eb,ec,q,map_add,map_smul] using hh
  have he : f ea = q • ea := by
    apply smul_right_injective (Vector F) hdet
    have hs := hu s t h₁
    have ht := hu u v h₂
    calc
      (s*v-u*t) • f ea = v • (s • f ea + t • f eb) -
          t • (u • f ea + v • f eb) := by module
      _ = v • (s • (q • ea) + t • ((f ec) d • ea + q • eb)) -
          t • (u • (q • ea) + v • ((f ec) d • ea + q • eb)) := by rw [hs,ht]
      _ = (s*v-u*t) • (q • ea) := by module
  refine ⟨q,?_⟩
  have hz : f-algebraMap F (Representation.End (pairAction V)) q=0 := by
    rcases Representation.IsIrreducible.injective_or_eq_zero
        (f-algebraMap F (Representation.End (pairAction V)) q) with hinj | hz
    · have hh : (f-algebraMap F (Representation.End (pairAction V)) q) ea =
          (f-algebraMap F (Representation.End (pairAction V)) q) 0 := by
        change f ea-q • ea = _
        rw [he,sub_self,map_zero]
      have hea : ea≠0 := by
        intro hh
        have := congrFun hh a
        simp [ea] at this
      exact (hea (hinj hh)).elim
    · exact hz
  exact (sub_eq_zero.mp hz).symm
/-- The actual non-diagonal pair is absolutely irreducible over F. -/
theorem pairAction_absolutelyIrreducible_of_no_diagonal (V : Subgroup (Sp F))
    (hc : V ≤ (CentralRootGeometry.parameter (F := F)).range)
    (hl : ¬ V ≤ RootSubgroup.group 0) (hs : ¬ V ≤ RootSubgroup.group 4)
    (hd : ∀μ:F,μ≠0 → ¬V ≤ diagonal μ) :
    Representation.IsAbsolutelyIrreducible (pairAction V) := by
  obtain ⟨s,t,u,v,h₁,h₂,hdet⟩ := exists_independent_of_no_diagonal V hc hl hs hd
  exact pairAction_absolutelyIrreducible_of_independent V s t u v hdet h₁ h₂

open DiagramAutomorphisms EvenBorelTorus CentralRootGeometry

/-- The moving actor discharges both axis and diagonal exceptions, so the
literal original opposite pair is absolutely irreducible. -/
theorem pairAction_absolutelyIrreducible_of_moving_actor [Finite F]
    (hq : 2 < Nat.card F)
    (α : ActorReduction.stabilizer (F := F)) (hα : ¬PreservesDiagram α.val)
    (V : Subgroup (Sp F)) (hV : V.map α.val.toMonoidHom = V)
    (hc : V ≤ (center (unipotent (F := F))).map (unipotent (F := F)).subtype)
    (hr : 2 < Nat.card V) : Representation.IsAbsolutelyIrreducible (pairAction V) := by
  have hne : V≠⊥ := by intro he; subst V; simp at hr
  obtain ⟨hl,hs⟩ := not_root_axes_of_moving_actor hq α hα V hV hne
  exact pairAction_absolutelyIrreducible_of_no_diagonal V
    (parameter_range (F := F) ▸ hc) hl hs
    (not_diagonal_of_moving_actor hq α hα V hV hr)

end Theory.SpecificGroups.SymplecticFour.TwoConjugate
