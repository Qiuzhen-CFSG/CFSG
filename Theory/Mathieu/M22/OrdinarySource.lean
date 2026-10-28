module
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.Coverage
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.LocalClassification
public import Theory.Mathieu.M22.Properties.FourNormalizers.Hexads
public import Theory.GroupTheory.DoubleCoverCentralizer.TwoCentralSylow
public import Theory.GroupTheory.SolvableResidual

/-!
# Solvable-residual control of the original M₂₂ centralizer

The centralizer of an involution has order 384. If it contains a Sylow
two-subgroup, it is solvable. Consequently an overgroup whose solvable
residual lies in that centralizer is itself solvable. The native geometric
coverage and order calculation for solvable Sylow overgroups then force
that overgroup to have order 384, hence to equal the centralizer.

This replaces the strict-overgroup recognition used for M₂₂ in the proof
of Aschbacher--Smith 15.1.20(3d), printed p.1097. It does not assert that
the centralizer is a maximal subgroup. The ambient Chapter15 argument
must supply the actual residual containment.
-/

public section
open Subgroup Theory.GroupTheory.DoubleCoverCentralizer
namespace Sporadic.Mathieu.OrdinaryTwentyTwo

/-- The literal two-central centralizer is determined by residual control,
without any maximality assertion or removal of its original marking. -/
theorem centralizer_eq_of_residual_le (X : Subgroup M22) (t : M22)
    (ht : orderOf t = 2) (htc : TwoCentral t)
    (hCX : centralizer ({t} : Set M22) ≤ X)
    (hR : (solvableResidual X).map X.subtype ≤ centralizer ({t} : Set M22)) :
    X = centralizer ({t} : Set M22) := by
  let C := centralizer ({t} : Set M22)
  have hcard : Nat.card C = 384 := M22FourNormalizers.involution_centralizer_card t ht
  obtain ⟨P,hPC⟩ := htc.exists_sylow_le_centralizer
  let : Group.IsSolvable C := M22SolvableSylow.solvable_of_card_384 C hcard ⟨P,hPC⟩
  let f : solvableResidual X →* C := {
    toFun x := ⟨x.val.val,hR (mem_map_of_mem X.subtype x.property)⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : C => (z : M22)) he))
  let : Group.IsSolvable (solvableResidual X) :=
    Group.isSolvable_of_isSolvable_injective hf
  have hz : solvableResidual X = ⊥ := by
    by_contra hne
    let : Nontrivial (solvableResidual X) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable (solvableResidual X) inferInstance
  let : Group.IsSolvable X := by
    obtain ⟨n,hn⟩ := exists_derivedSeries_eq_solvableResidual (G := X)
    exact ⟨n,hn.trans hz⟩
  have h3 : 3 ∣ Nat.card X :=
    (show 3 ∣ Nat.card C by rw [hcard]; decide).trans (card_dvd_of_le hCX)
  have hSyl : ∃ Q : Sylow 2 M22, (Q : Subgroup M22) ≤ X := ⟨P,hPC.trans hCX⟩
  have hn : (X.subgroupOf X).Normal := by rw [subgroupOf_self]; infer_instance
  have hplace := M22SolvableSylow.geometric_coverage X X le_rfl hn inferInstance h3 hSyl
  have hcX := M22SolvableSylow.LocalClassification.order_of_geometric_placement
    X X le_rfl hn inferInstance h3 hSyl hplace
  exact (eq_of_le_of_card_ge hCX (by rw [hcard,hcX])).symm

end Sporadic.Mathieu.OrdinaryTwentyTwo
