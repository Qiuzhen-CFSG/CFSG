module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Centers.Intersections
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Ordered flag stabilizers and their two-residuals

The j-th subgroup fixes every proper nonzero member of the marked flag
except V_j. Its two-residual is embedded into the original ambient group;
the initial joins are the H_i in the induction of 12.8.10(5). For n=2 the
first stabilizer is all LT, consistently with the existing F.P.

Only definitions and elementary containment/recursion facts are asserted
here. Identifying these stabilizers as natural minimal parabolics and
proving their generation properties requires the genuine natural action.

Source: Aschbacher–Smith, Lemma 12.8.10(5), printed p.854 (PDF p.871).
-/

open Subgroup
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

@[expose] public def orderedParabolic (F : InvariantFlag T V n) (L : Subgroup G) (j : ℕ) : Subgroup G :=
  (L ⊔ (T : Subgroup G)) ⊓ ⨅ i : ℕ, ⨅ (_ : 1 ≤ i ∧ i < n ∧ i ≠ j), F.Gi i

@[expose] public def orderedResidual (F : InvariantFlag T V n) (L : Subgroup G) (j : ℕ) : Subgroup G :=
  (pResidual 2 (F.orderedParabolic L j)).map (F.orderedParabolic L j).subtype

@[expose] public def initialResiduals (F : InvariantFlag T V n) (L : Subgroup G) (i : ℕ) : Subgroup G :=
  ⨆ j : ℕ, ⨆ (_ : 1 ≤ j ∧ j ≤ i), F.orderedResidual L j

public theorem orderedParabolic_one (F : InvariantFlag T V n) (L : Subgroup G) :
    F.orderedParabolic L 1 = F.P L := by
  apply congrArg ((L ⊔ (T : Subgroup G)) ⊓ ·)
  apply le_antisymm
  · apply le_iInf; intro i; apply le_iInf; intro hi
    exact iInf_le_of_le i (iInf_le_of_le (by omega) le_rfl)
  · apply le_iInf; intro i; apply le_iInf; intro hi
    exact iInf_le_of_le i (iInf_le_of_le (by omega) le_rfl)

public theorem orderedParabolic_le_H (F : InvariantFlag T V n) (hn : 2 ≤ n)
    (L : Subgroup G) {j : ℕ} (hj : 2 ≤ j) : F.orderedParabolic L j ≤ F.H := by
  exact inf_le_right.trans (iInf_le_of_le 1 (iInf_le_of_le (by omega) le_rfl))

public theorem orderedResidual_le (F : InvariantFlag T V n) (L : Subgroup G) (j : ℕ) :
    F.orderedResidual L j ≤ F.orderedParabolic L j := map_subtype_le _

public theorem orderedResidual_isPPerfect (F : InvariantFlag T V n) [Finite G]
    (L : Subgroup G) (j : ℕ) : IsPPerfect 2 (F.orderedResidual L j) :=
  isPPerfect_embedded_pResidual 2 _

public theorem initialResiduals_one (F : InvariantFlag T V n) (L : Subgroup G) :
    F.initialResiduals L 1 = F.orderedResidual L 1 := by
  apply le_antisymm
  · apply iSup_le; intro j; apply iSup_le; intro hj
    have he : j = 1 := by omega
    subst j
    exact le_rfl
  · exact le_iSup_of_le 1 (le_iSup_of_le ⟨le_rfl, le_rfl⟩ le_rfl)

public theorem initialResiduals_succ (F : InvariantFlag T V n) (L : Subgroup G) (j : ℕ) :
    F.initialResiduals L (j + 1) = F.initialResiduals L j ⊔ F.orderedResidual L (j + 1) := by
  apply le_antisymm
  · apply iSup_le; intro i; apply iSup_le; intro hi
    by_cases he : i = j + 1
    · subst i; exact le_sup_right
    · exact (show F.orderedResidual L i ≤ F.initialResiduals L j from
        le_iSup_of_le i (le_iSup_of_le (show 1 ≤ i ∧ i ≤ j by omega) le_rfl)).trans le_sup_left
  · apply sup_le
    · apply iSup_le; intro i; apply iSup_le; intro hi
      exact le_iSup_of_le i (le_iSup_of_le (show 1 ≤ i ∧ i ≤ j + 1 by omega) le_rfl)
    · exact le_iSup_of_le (j + 1) (le_iSup_of_le ⟨by omega, le_rfl⟩ le_rfl)
end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
