module

public import Theory.GroupTheory.PerfectCentralQuotientNormalizer
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Solvable

/-!
# Solvable proper Sylow overgroups

This property is invariant under group isomorphism and lifts through a central
quotient of a perfect group. In the latter case a proper subgroup cannot map
onto the quotient, since adjoining central elements does not enlarge its
commutator subgroup. These transports retain the given Sylow subgroup.

Application: Aschbacher–Smith, 13.1.2(5), printed p.866: local components
contained in one of the five small quotient models must coincide.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory

/-- Every proper overgroup of a Sylow two-subgroup is solvable. -/
def SolvableSylowOvergroups (G : Type*) [Group G] : Prop :=
  ∀ (S : Sylow 2 G) (P : Subgroup G), (S : Subgroup G) ≤ P → P ≠ ⊤ →
    Group.IsSolvable P

namespace SolvableSylowOvergroups
variable {G H : Type*} [Group G] [Group H] [Finite G]

/-- Transport through an actual group isomorphism. -/
theorem of_equiv (e : G ≃* H) (h : SolvableSylowOvergroups H) :
    SolvableSylowOvergroups G := by
  intro S P hSP hP
  let Q := P.map e.toMonoidHom
  have hQ : Q ≠ ⊤ := by
    intro he
    apply hP
    exact e.mapSubgroup.injective (he.trans e.mapSubgroup.map_top.symm)
  let : Group.IsSolvable Q := h (S.mapSurjective e.surjective) Q (map_mono hSP) hQ
  exact Group.isSolvable_of_isSolvable_injective
    (f := (P.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
    (P.equivMapOfInjective e.toMonoidHom e.injective).injective

/-- A perfect central cover inherits the property from its quotient. -/
theorem of_central_quotient [Group.IsPerfect G]
    (f : G →* H) (hf : Function.Surjective f) (hk : f.ker ≤ center G)
    (h : SolvableSylowOvergroups H) : SolvableSylowOvergroups G := by
  intro S P hSP hP
  let Q := P.map f
  have hQ : Q ≠ ⊤ := by
    intro he
    apply hP
    apply top_unique
    apply perfect_le_of_map_le_of_central_kernel f hk (⊤ : Subgroup G) P
    change _ ≤ Q
    rw [he]
    exact le_top
  let q : P →* Q := f.subgroupMap P
  have hker : q.ker ≤ center P := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp (hk (congrArg Subtype.val hx)) y.val)
  let : Group.IsSolvable q.ker := Group.isSolvable_of_comm (fun x y =>
    Subtype.ext (mem_center_iff.mp (hker y.property) x.val))
  let : Group.IsSolvable Q := h (S.mapSurjective hf) Q (map_mono hSP) hQ
  exact Group.isSolvable_of_ker_le_range q.ker.subtype q (by simp)
end SolvableSylowOvergroups
end Theory.GroupTheory
