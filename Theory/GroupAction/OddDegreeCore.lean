module
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!
# Two-cores in actions of odd degree

A two-group acting on an odd finite set has a fixed point. If it is the
normal two-core of a transitive actor, translating that fixed point shows
that it fixes the entire set. Two subgroups transitive on complementary
point sets generate the transitivity needed in the opposite-root application.

Source: the elementary p-group fixed-point argument used in DGS,
*Groups and Graphs* (1985), (14.3), (14.9), pp.212,215--216.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupAction
variable {X V : Type*} [Group X] [MulAction X V]

/-- A normal two-core fixes a transitive set of odd cardinality pointwise. -/
theorem pCoreIn_fixes_of_transitive_on (A : Subgroup X) (T : Set V)
    (hstable : ∀ g∈A, ∀ v∈T, g • v∈T)
    (htrans : ∀ v∈T, ∀ w∈T, ∃ g∈A, g • v=w)
    (hodd : Odd (Nat.card T)) :
    ∀ g∈A.pCoreIn 2, ∀ v∈T, g • v=v := by
  let C : SubMulAction A V := { carrier := T, smul_mem' := fun g v hv => hstable g g.property v hv }
  have hcard : Nat.card C = Nat.card T := rfl
  obtain ⟨v,hv⟩ := (pCore_isPGroup (p := 2) (G := A)).nonempty_fixed_point_of_prime_not_dvd_card
    C (by rw [hcard]; exact hodd.not_two_dvd_nat)
  intro g hg w hw
  obtain ⟨a,ha,he⟩ := htrans v v.property w hw
  have hh : (⟨w,hw⟩ : C)∈MulAction.fixedPoints (pCore 2 A) C := by
    have ht := smul_mem_fixedPoints_of_normal (⟨a,ha⟩ : A) hv
    convert ht using 1
    exact (Subtype.ext he).symm
  obtain ⟨q,hq,rfl⟩ := hg
  exact congrArg Subtype.val (hh ⟨q,hq⟩)

/-- Two complementary orbits, joined through a third point, give transitivity. -/
theorem transitive_on_of_two_complement_orbits (A R S : Subgroup X) (T : Set V)
    (hRA : R ≤ A) (hSA : S ≤ A) {a b c : V}
    (hc : c∈T) (hca : c≠a) (hcb : c≠b)
    (hR : ∀ v∈T, v≠a → ∃ r∈R, r • b=v)
    (hS : ∀ v∈T, v≠b → ∃ s∈S, s • a=v) :
    ∀ v∈T, ∀ w∈T, ∃ g∈A, g • v=w := by
  have reach (w : V) (hw : w∈T) : ∃ g∈A, g • a=w := by
    by_cases hwb : w=b
    · obtain ⟨r,hr,her⟩ := hR c hc hca
      obtain ⟨s,hs,hes⟩ := hS c hc hcb
      refine ⟨r⁻¹*s,A.mul_mem (A.inv_mem (hRA hr)) (hSA hs),?_⟩
      rw [mul_smul,hes,←her,inv_smul_smul,hwb]
    · obtain ⟨s,hs,hes⟩ := hS w hw hwb
      exact ⟨s,hSA hs,hes⟩
  intro v hv w hw
  obtain ⟨r,hr,her⟩ := reach v hv
  obtain ⟨s,hs,hes⟩ := reach w hw
  exact ⟨s*r⁻¹,A.mul_mem hs (A.inv_mem hr),by rw [mul_smul,←her,inv_smul_smul,hes]⟩


end Theory.GroupAction
