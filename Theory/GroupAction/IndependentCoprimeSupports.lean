module

public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.Lemmas
public import Mathlib.Order.SupIndep

/-!
# Independent coprime action supports

For a faithful action on a finite abelian group, mutually fixed coprime
supports and their actors are independent families of subgroups. Coprime
splitting separates each support from the sum of the others; faithfulness
on each support gives the same conclusion for the actors. Mutual fixedness
also proves that the actors commute.

This is the direct-product step in Aschbacher--Smith, *The Classification of
Quasithin Groups*, D.2.12, printed pp.183–184. The hypotheses here isolate
that step for arbitrary coprime actors and arbitrary indexing types.
-/

open scoped IsMulCommutative

namespace ActionSupport

variable {G V I : Type*} [Group G] [Group V] [Finite V]
    [IsMulCommutative V] [MulDistribMulAction G V]

/-- A coprime actor has disjoint fixed subgroup and support. -/
public theorem fixed_support_isCompl (X : Subgroup G) [Finite X]
    (hcop : Nat.Coprime (Nat.card X) (Nat.card V)) :
    IsCompl (FixedPoints.subgroup X V) (commutatorAction X V) := by
  exact isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (Group.isSolvable_of_comm (fun x y : V => IsMulCommutative.is_comm.comm x y))
    hcop inferInstance

/-- Under a faithful action, a coprime actor is faithful on its support. -/
public theorem eq_one_of_fixes_support [FaithfulSMul G V]
    (X : Subgroup G) [Finite X]
    (hcop : Nat.Coprime (Nat.card X) (Nat.card V))
    (x : X) (hfix : ∀ v ∈ commutatorAction X V, (x : G) • v = v) :
    (x : G) = 1 := by
  apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
  intro v
  have hcompl := fixed_support_isCompl X hcop
  have hv : v ∈ FixedPoints.subgroup X V ⊔ commutatorAction X V := by
    rw [hcompl.sup_eq_top]
    trivial
  let _ : (FixedPoints.subgroup X V).Normal := Subgroup.normal_of_isMulCommutative _
  obtain ⟨c, hc, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hv
  have hxc : (x : G) • c = c := hc x
  simp only [smul_mul', hxc, hfix w hw, one_smul]

/-- Coprime supports fixed by every other actor form an independent family. -/
public theorem supports_iSupIndep (X : I → Subgroup G) [∀ i, Finite (X i)]
    (hcop : ∀ i, Nat.Coprime (Nat.card (X i)) (Nat.card V))
    (hcross : ∀ i j, i ≠ j →
      commutatorAction (X j) V ≤ FixedPoints.subgroup (X i) V) :
    iSupIndep (fun i => commutatorAction (X i) V) := by
  rw [iSupIndep_def]
  intro i
  apply (fixed_support_isCompl (X i) (hcop i)).disjoint.symm.mono_right
  exact iSup_le fun j => iSup_le fun hji => hcross i j hji.symm

/-- The actors are independent as well: the other actors fix this actor's
support, on which this actor is faithful. -/
public theorem actors_iSupIndep [FaithfulSMul G V]
    (X : I → Subgroup G) [∀ i, Finite (X i)]
    (hcop : ∀ i, Nat.Coprime (Nat.card (X i)) (Nat.card V))
    (hcross : ∀ i j, i ≠ j →
      commutatorAction (X j) V ≤ FixedPoints.subgroup (X i) V) :
    iSupIndep X := by
  rw [iSupIndep_def]
  intro i
  rw [Subgroup.disjoint_def]
  intro x hxi hxrest
  apply eq_one_of_fixes_support (X i) (hcop i) ⟨x, hxi⟩
  have hrest : (⨆ j, ⨆ (_ : j ≠ i), X j) ≤
      fixingSubgroup G (commutatorAction (X i) V : Set V) := by
    refine iSup_le fun j => iSup_le fun hji => ?_
    intro y hy
    rw [mem_fixingSubgroup_iff]
    intro v hv
    exact hcross j i hji hv ⟨y, hy⟩
  exact (mem_fixingSubgroup_iff (M := G)).mp (hrest hxrest)

omit [Finite V] in
/-- Actors fixing each other's supports commute in a faithful abelian action. -/
public theorem commute_of_cross_fixed [FaithfulSMul G V]
    (X Y : Subgroup G)
    (hXY : commutatorAction Y V ≤ FixedPoints.subgroup X V)
    (hYX : commutatorAction X V ≤ FixedPoints.subgroup Y V)
    (x : X) (y : Y) : Commute (x : G) (y : G) := by
  apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
  intro v
  have hdX : v⁻¹ * (x : G) • v ∈ commutatorAction X V := by
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨x, v, rfl⟩
  have hdY : v⁻¹ * (y : G) • v ∈ commutatorAction Y V := by
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨y, v, rfl⟩
  have hx := hXY hdY x
  have hy := hYX hdX y
  change (x : G) • (v⁻¹ * (y : G) • v) = v⁻¹ * (y : G) • v at hx
  change (y : G) • (v⁻¹ * (x : G) • v) = v⁻¹ * (x : G) • v at hy
  rw [smul_mul', smul_inv'] at hx hy
  have hxy := congrArg (fun w => ((x : G) • v) * w) hx
  have hyx := congrArg (fun w => ((y : G) • v) * w) hy
  simp only [← mul_assoc, mul_inv_cancel, one_mul] at hxy hyx
  change (x * y : G) • v = (y * x : G) • v
  simp only [mul_smul]
  rw [hxy, hyx]
  ac_rfl

end ActionSupport
