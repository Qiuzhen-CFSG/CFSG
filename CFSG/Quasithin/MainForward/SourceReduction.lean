module

public import CFSG.Quasithin.MainForward.SourceFamilies
public import FeitThompson.FinalTheorem

/-!
# Exhaustiveness of the three source branches

Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, p. 1166, splits first on `|M(T)| = 1` and then on
whether `L_f(G,T)` is empty. To justify the strict inequality in the second
branch, `M(T)` must be nonempty. The odd-order theorem rules out odd order
for a nonabelian simple group. Thus every Sylow two-subgroup is nontrivial,
and its normalizer lies in a maximal two-local subgroup.

The K-class stays explicit here. The complete known-simple catalogue must
be supplied at final assembly. Theorems 2.1.1, D, and E are not proved by
this exhaustion argument.
-/

@[expose] public section

namespace CFSG.Quasithin.MainForward

open Theory.GroupTheory

universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}

/-- The odd-order theorem discharges the even-order premise needed to begin
the local argument. -/
theorem even_card (h : IsSimpleQTKE K G) : Even (Nat.card G) := by
  let := h.simple
  by_contra hodd
  exact h.nonabelian (isMulCommutative_iff.mpr
    (IsSimpleGroup.comm_iff_isSolvable.mpr
      (odd_order_theorem G (Nat.not_even_iff_odd.mp hodd))))

/-- In the actual main-theorem inputs, a Sylow two-subgroup is nonidentity. -/
theorem sylow_ne_bot (h : IsSimpleQTKE K G) (T : Sylow 2 G) :
    (T : Subgroup G) ≠ ⊥ :=
  T.ne_bot_of_dvd_card (even_iff_two_dvd.mp (even_card h))

/-- The source family `M(T)` cannot be empty. -/
theorem maximalOvergroups_nonempty (h : IsSimpleQTKE K G) (T : Sylow 2 G) :
    (maximalTwoLocalOvergroups (T : Subgroup G)).Nonempty :=
  maximalTwoLocalOvergroups_nonempty_of_isPGroup _ (sylow_ne_bot h T) T.isPGroup'

/-- The three cases on p. 1166 are exhaustive for the actual local families.
The strict cardinal bound is proved, not added as a premise. -/
theorem source_cases (h : IsSimpleQTKE K G) (T : Sylow 2 G) :
    (maximalTwoLocalOvergroups (T : Subgroup G)).ncard = 1 ∨
    (1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard ∧
      faithfulLocalComponents T = ∅) ∨
    (1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard ∧
      (faithfulLocalComponents T).Nonempty) := by
  classical
  have hpos := (maximalOvergroups_nonempty h T).ncard_pos
  by_cases hone : (maximalTwoLocalOvergroups (T : Subgroup G)).ncard = 1
  · exact Or.inl hone
  have hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard := by omega
  by_cases hempty : faithfulLocalComponents T = ∅
  · exact Or.inr (Or.inl ⟨hmany, hempty⟩)
  · exact Or.inr (Or.inr ⟨hmany, Set.nonempty_iff_ne_empty.mpr hempty⟩)

end CFSG.Quasithin.MainForward
