module
public import CFSG.Quasithin.Chapter13.Section09.CentralizerStructure.NormalCore
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.WreathOuter
public import Theory.GroupTheory.QuaternionCentralProductTransport
/-!
# Solvability of the original wreath involution centralizer

The marked Q is first proved normal from the reduced-closure and native
hyperplane-fixer geometry. Its intrinsic quaternion presentation makes Aut(Q)
solvable by the actual orthogonal wreath action. The kernel of conjugation
by C_G(z) lies in C_G(z,t), a two-group by 13.9.7. The extension criterion
therefore proves solvability of C_G(z), retaining the original marked groups.

This supplies the solvability consequence of Aschbacher–Smith 13.9.8,
printed p.972. The later exact quotient and B-normality geometry is separate.
-/
public section
namespace CFSG.Quasithin.Chapter13.Section09.CentralizerStructure
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {d : Configuration G} {m : PairData d}
namespace CoreData
variable (q : CoreData m)

/-- The literal centralizer of Q has two-power order, since it centralizes
its marked member t and 13.9.7 identifies that common centralizer. -/
theorem centralizer_isPGroup (hE : IsEvenCharacteristicAt d.T) :
    IsPGroup 2 (centralizer (q.Q.subgroupOf m.C : Set m.C)) := by
  have hD : IsPGroup 2 m.D := by
    rw [m.source13_9_7 hE]
    exact d.T.isPGroup'.to_le (PairData.thompson_le_T (d := d))
  let j : centralizer (q.Q.subgroupOf m.C : Set m.C) →* m.D := {
    toFun := fun x => ⟨x.val.val,x.val.property,
      mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (x.property ⟨m.t,m.t_mem_C⟩ q.t_mem)).symm⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  apply hD.of_injective j
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun a : m.D => (a : G)) hxy

/-- The actual marked centralizer is solvable as soon as the preceding
source geometry and native hyperplane-fixer calculation are available. -/
theorem centralizer_solvable_of_hyperplane_fixers (h : m.ClosureData)
    (hE : IsEvenCharacteristicAt d.T)
    (hfix : ∀ E : Subgroup m.Tilde, E ≤ m.tilde q.Q → Nat.card E = 8 →
      m.tilde d.T ⊓ centralizer (E : Set m.Tilde) ≤
        centralizer (m.tilde q.Q : Set m.Tilde)) :
    Group.IsSolvable m.C := by
  let : (q.Q.subgroupOf m.C).Normal := q.normal_of_hyperplane_fixers h hE hfix
  let a := q.factors.map (subgroupOfEquivOfLe q.le_C).symm
  let : Group.IsSolvable (MulAut (q.Q.subgroupOf m.C)) := a.mulAut_isSolvable
  let f : m.C →* MulAut (q.Q.subgroupOf m.C) := MulAut.conjNormal
  have hp : IsPGroup 2 f.ker := by
    rw [MulAut.conjNormal_ker_eq_centralizer]
    exact q.centralizer_isPGroup hE
  let : Group.IsNilpotent f.ker := hp.isNilpotent
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [range_subtype])

end CoreData
end CFSG.Quasithin.Chapter13.Section09.CentralizerStructure
