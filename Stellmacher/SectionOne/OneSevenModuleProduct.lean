module

public import Stellmacher.SectionOne.OneSevenFactorPair
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaFixedIndices

/-!
# Module decomposition for the global SL2 factors

A finite family of distinct factors used in Stellmacher (1.7) gives the
four-element action modules in part (c), together with the fixed space of
the generated subgroup. The join of their derived C3 subgroups lies in O3(G),
so coprime action splits off its fixed complement. Each full factor fixes
its derived fixed space; consequently this complement is precisely the
fixed space of the full generated group. Action commutators distribute over
the join, and (1.4) makes the supports of distinct derived factors disjoint.
Faithfulness is used through uniqueness of the factors from their derived
subgroups. The ambient elementary abelian module makes all factors commute.

Source: refs/latex/stellmacher-n-group.tex, Stellmacher (1.7)(c), journal p.19.
-/

open scoped IsMulCommutative
open Stellmacher.SectionOne.RankOneThreeGroupAssembly
namespace Stellmacher.SectionOne
universe u

public theorem oneSevenFactor_module_product
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) {n : ℕ} (D : Fin n → Subgroup G)
    (hD : ∀ i, IsOneSevenFactor (V := V) (D i)) (hinj : Function.Injective D)
    (E : Subgroup G) (hgen : E = ⨆ i, D i) :
    IsInternalDirectProductFamily (⊤ : Subgroup V)
      (fun i : Option (Fin n) => match i with
        | none => FixedPoints.subgroup E V
        | some i => commutatorAction (D i) V) := by
  let K (i : Fin n) : Subgroup G := (commutator (D i)).map (D i).subtype
  let P : Subgroup G := ⨆ i, K i
  have hPthree : P ≤ pCore 3 G :=
    iSup_le fun i => oneSevenFactor_derived_le_threeCore (D i) (hD i)
  have hPp : IsPGroup 3 P := (pCore_isPGroup (p := 3) (G := G)).of_injective
    (Subgroup.inclusion hPthree) (Subgroup.inclusion_injective hPthree)
  have hcop : Nat.Coprime (Nat.card P) (Nat.card V) := by
    obtain ⟨a, ha⟩ := hPp.exists_card_eq
    obtain ⟨b, hb⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [ha, hb]
    exact (show Nat.Coprime 3 2 by decide).pow a b
  have hPE : P ≤ E := by
    apply iSup_le
    intro i
    rw [hgen]
    exact (Subgroup.map_subtype_le _).trans (le_iSup D i)
  have hfix : FixedPoints.subgroup P V = FixedPoints.subgroup E V := by
    apply le_antisymm
    · intro v hv
      have hEfix : E ≤ fixingSubgroup G ({v} : Set V) := by
        rw [hgen]
        refine iSup_le fun i => ?_
        intro d hd
        rw [mem_fixingSubgroup_iff]
        intro w hw
        have hwv : w = v := Set.mem_singleton_iff.mp hw
        subst w
        apply oneSevenFactor_fixes_derived_fixedPoints (D i) (hD i) d hd v
        rw [FixedPoints.mem_subgroup]
        intro k
        exact (FixedPoints.mem_subgroup (M := P) (a := v)).mp hv ⟨k, (le_iSup K i) k.property⟩
      rw [FixedPoints.mem_subgroup]
      intro e
      exact (mem_fixingSubgroup_iff (M := G)).mp (hEfix e.property) v (Set.mem_singleton v)
    · intro v hv
      rw [FixedPoints.mem_subgroup]
      intro p
      exact (FixedPoints.mem_subgroup (M := E) (a := v)).mp hv ⟨p, hPE p.property⟩
  have hU : commutatorAction P V = ⨆ i, commutatorAction (D i) V := by
    rw [commutatorAction_eq_iSup_of_eq_iSup K rfl]
    congr 1
    funext i
    exact (oneSevenFactor_full_commutator_eq_derived (D i) (hD i)).symm
  have hcompl : IsCompl (FixedPoints.subgroup E V) (⨆ i, commutatorAction (D i) V) := by
    rw [← hfix, ← hU]
    exact isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := P)
      (Group.isSolvable_of_comm fun x y => (IsMulCommutative.is_comm (M := V)).comm x y)
      hcop inferInstance
  refine ⟨?_, ?_, ?_⟩
  · rw [iSup_option]
    exact hcompl.sup_eq_top.symm
  · intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j =>
        change Disjoint (FixedPoints.subgroup E V) (commutatorAction (D j) V)
        exact hcompl.disjoint.mono_right (le_iSup (fun k => commutatorAction (D k) V) j)
    | some i =>
      cases j with
      | none => exact (hcompl.disjoint.mono_right (le_iSup _ i)).symm
      | some j =>
        change Disjoint (commutatorAction (D i) V) (commutatorAction (D j) V)
        have hne : K i ≠ K j := by
          intro heq
          have hd := oneSevenFactor_eq_of_derived_eq h (D i) (D j) (hD i) (hD j) heq
          exact hij (congrArg some (hinj hd))
        rw [oneSevenFactor_full_commutator_eq_derived (D i) (hD i),
          oneSevenFactor_full_commutator_eq_derived (D j) (hD j)]
        exact omega_pair_action_disjoint h (hD i).2.1 (hD j).2.1 hne
          (oneSevenFactor_derived_le_threeCore (D i) (hD i))
          (oneSevenFactor_derived_le_threeCore (D j) (hD j)) le_rfl
  · intro i j hij a ha b hb
    exact (IsMulCommutative.is_comm (M := V)).comm a b

end Stellmacher.SectionOne

