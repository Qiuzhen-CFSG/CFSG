module

public import Theory.GroupTheory.SolvableSylowOvergroups
public import Theory.GroupTheory.SolvableMutualCommutator
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# Two-kernel lifts of solvable Sylow overgroups

The property that proper Sylow-two overgroups are solvable lifts through a
two-group kernel: that kernel lies in every Sylow two-subgroup. In a perfect
group with this property a nonsolvable subgroup normalized by a Sylow
two-subgroup is the whole group. Its join with the Sylow subgroup is first
the whole group, and its resulting two-group quotient is trivial.

These statements apply to the literal two-core quotient of a terminal
overcomponent in Aschbacher–Smith, 12.2.7, printed pp.797–798, used in
12.3.12, p.811. They avoid replacing a quasisimple two-core quotient by a
quasisimplicity assumption on the subgroup itself.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.SolvableSylowOvergroups
variable {G H : Type*} [Group G] [Group H] [Finite G]

/-- Lift through a surjective homomorphism with two-group kernel. -/
theorem of_two_kernel (f : G →* H) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (h : SolvableSylowOvergroups H) :
    SolvableSylowOvergroups G := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Group.IsNilpotent f.ker := hk.isNilpotent
  intro S B hSB hB
  have hker : f.ker ≤ B := (hk.le_sylow_of_normal S).trans hSB
  have himage : B.map f ≠ ⊤ := by
    intro he
    apply hB
    have hh := congrArg (comap f) he
    simpa only [comap_map_eq, sup_eq_left.mpr hker, comap_top] using hh
  exact (Group.isSolvable_map_iff_of_solvable_ker f B).mp
    (h (S.mapSurjective hf) (B.map f) (map_mono hSB) himage)

/-- A nonsolvable Sylow-normalized subgroup in a perfect group with solvable
proper Sylow overgroups is the whole group. -/
theorem eq_top_of_sylow_normalizes [Group.IsPerfect G]
    (h : SolvableSylowOvergroups G) (S : Sylow 2 G) (B : Subgroup G)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hs : ¬ Group.IsSolvable B) : B = ⊤ := by
  have hgen : B ⊔ (S : Subgroup G) = ⊤ := by
    by_contra hh
    let : Group.IsSolvable (B ⊔ (S : Subgroup G) : Subgroup G) := h S _ le_sup_right hh
    exact hs (Group.isSolvable_of_isSolvable_injective
      (f := inclusion (show B ≤ B ⊔ (S : Subgroup G) from le_sup_left))
      (inclusion_injective _))
  let : B.Normal := normalizer_eq_top_iff.mp
    (top_unique (hgen ▸ sup_le B.le_normalizer hn))
  let : Group.IsNilpotent (G ⧸ B) :=
    (isPGroup_quotient_of_sup_eq_top B S S.isPGroup' hgen).isNilpotent
  exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ B)

end Theory.GroupTheory.SolvableSylowOvergroups
