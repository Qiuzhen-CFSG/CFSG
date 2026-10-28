module
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.Octagon.Parabolics
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.CoreActionRigidity.Structure
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Coverage
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup
/-!
# Solvable generalized Fitting subgroups in Ree Borel overgroups

The actual rank-two Tits system places every proper Borel overgroup in
one of the two full root parabolics. Their self-centralizing two-cores
restrict through the supplied full Sylow. Conjugation of that Sylow and
the intrinsic generalized Fitting equivalence retain the original group.
Source: GLS3 2.3.4–5, 2.6.5; Aschbacher–Smith A.3.12 and C.5.13.
-/
public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace ReeF4.ConverseParabolics
open LargeLocalSeeds SectionGeometry.BNPair
open MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry
noncomputable section
attribute [local instance] borel_inf_normalizerWords_normal
private theorem proper_borel_overgroup_le_parabolic (m : ℕ) (hm : 1 ≤ m)
    (X : Subgroup (Model m)) (hB : Parabolics.borel m ≤ X) (hX : X ≠ ⊤) :
    ∃ s : Side, X ≤ parabolic m s := by
  let T := titsSystem m
  have hclass := T.subgroup_eq_standardParabolic_simpleIndices X hB
  have hI := T.simpleIndices_subset X
  change T.simpleIndices X ⊆ simpleReflections m at hI
  rw [simpleReflections_eq_pair] at hI
  rcases Set.subset_pair_iff_eq.mp hI with he | he | he | he
  · refine ⟨.linear,?_⟩
    rw [hclass,he,T.standardParabolic_empty]
    change Parabolics.borel m ≤ parabolic m .linear
    rw [parabolic_eq_rootParabolic]
    exact Parabolics.borel_le_parabolic m .linear
  · refine ⟨.linear,?_⟩
    rw [hclass,he]
    exact (standardParabolic_singleton_eq_parabolic m hm .linear).le
  · refine ⟨.suzuki,?_⟩
    rw [hclass,he]
    exact (standardParabolic_singleton_eq_parabolic m hm .suzuki).le
  · have hi : T.simpleIndices X = T.S := he.trans (simpleReflections_eq_pair m).symm
    exact (hX (hclass.trans ((congrArg T.standardParabolic hi).trans T.standardParabolic_S))).elim

theorem proper_borel_overgroup_fitting_isSolvable (m : ℕ) (hm : 1 ≤ m)
    (S : Sylow 2 (Model m)) (H : Subgroup (Model m))
    (hSH : normalizer (S : Set (Model m)) ≤ H) (hH : H ≠ ⊤) :
    Group.IsSolvable (generalizedFitting H) := by
  obtain ⟨Q,hQ⟩ := exists_sylow_eq_unipotent m
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Model m) S Q
  let e := MulAut.conj g
  let X := H.map e.toMonoidHom
  have hX : X ≠ ⊤ := by
    intro he
    apply hH
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_top_of_surjective _ e.surjective]
    exact he
  have hS : (S : Subgroup (Model m)).map e.toMonoidHom = Parabolics.unipotent m := by
    change ((g • S : Sylow 2 (Model m)) : Subgroup (Model m)) = _
    rw [hg,hQ,unipotent_eq_rootUnipotent]
  have hB : Parabolics.borel m ≤ X := by
    rw [← Parabolics.unipotent_normalizer_eq_borel m,← hS,
      ← map_normalizer_eq_of_bijective _ e.bijective]
    exact map_mono hSH
  obtain ⟨s,hs⟩ := proper_borel_overgroup_le_parabolic m hm X hB hX
  have hQX : (Q : Subgroup (Model m)) ≤ X := by
    rw [hQ,unipotent_eq_rootUnipotent]
    exact (Parabolics.unipotent_le_borel m).trans hB
  have hfit := generalizedFitting_eq_pCore_of_sylow_overgroup Q X (parabolic m s)
    hQX hs (parabolic_centralizer_pCore_le hm s)
  have hf : Group.IsSolvable (generalizedFitting X) := by
    rw [hfit]
    let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
    infer_instance
  let eH : H ≃* X := e.subgroupMap H
  let ef : generalizedFitting H ≃* generalizedFitting X :=
    ((generalizedFitting H).equivMapOfInjective eH.toMonoidHom eH.injective).trans
      (MulEquiv.subgroupCongr (map_generalizedFitting_equiv eH))
  exact Group.isSolvable_of_isSolvable_injective (f := ef.toMonoidHom) ef.injective
end
end ReeF4.ConverseParabolics
