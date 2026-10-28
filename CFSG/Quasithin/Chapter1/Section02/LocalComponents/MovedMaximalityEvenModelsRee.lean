module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityEvenModelsSmall
public import Theory.SpecificGroups.SL2.SylowOvergroupComponentUnique
public import Theory.SpecificGroups.ReeF4.OddSupplement
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.LocalIdentification
public import Theory.SpecificGroups.Suzuki.SchurCoverReduction

/-!
# Unique C-components in the Ree Sylow overgroups

The actual fixed-group comparison transports an arbitrary LocalBlockInput
to the root-defined Ree carrier. Proper full-Sylow overgroups lie in the two
root parabolics. Their normal local factors have solvable Borel supplements,
and their actual two-core quotients are PSL₂(q) and Sz(q). Rank-one uniqueness
therefore proves the desired restriction without a normalizer callback.
Source: Aschbacher--Smith A.3.12(2--3), pp.47--48; 1.2.8(1), p.506.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.MovedMaximality
open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds
open ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry
private theorem ree_local_unique (m : ℕ) (hm : 1 ≤ m) (s : Side) :
    SylowOvergroupComponentUnique (localFactor m s) := by
  let : Group.IsNilpotent (pCore 2 (localFactor m s)) := pCore_isNilpotent
  apply SylowOvergroupComponentUnique.of_quotient (pCore 2 (localFactor m s))
  cases s with
  | linear =>
    exact SylowOvergroupComponentUnique.of_equiv (linearLocalQuotientEquiv m)
      (Theory.PSL2.sylow_overgroup_component_unique (CoefficientField m))
  | suzuki =>
    let : Fact (0<m) := ⟨by omega⟩
    let : Group.IsPerfect (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
      BenderSuzuki.MatrixGroups.SchurCover.isPerfect m (by omega)
    apply SylowOvergroupComponentUnique.of_equiv (suzukiLocalQuotientEquiv m)
    exact bender_sylow_overgroup_component_unique (.suzuki m hm ⟨MulEquiv.refl _⟩)

private theorem ree_parabolic_unique (m : ℕ) (hm : 1 ≤ m) (s : Side) :
    SylowOvergroupComponentUnique (parabolic m s) := by
  let : Group.IsSolvable (borel m) := OddSupplement.borel_isSolvable m
  exact SylowOvergroupComponentUnique.of_solvable_supplement
    (localFactor m s) (borel m) (parabolic m s) (localFactor_le_parabolic m s)
    (borel_le_parabolic m s) (parabolic_eq_localFactor_sup_borel m s).symm
    (ree_local_unique m hm s)

private theorem ree_model_unique (m : ℕ) (hm : 1 ≤ m)
    [IsSimpleGroup (Model m)] [Group.IsPerfect (Model m)] :
    SylowOvergroupComponentUnique (Model m) := by
  apply SylowOvergroupComponentUnique.of_proper_conjugate_cover
  intro S P hSP hP
  obtain ⟨g,hg⟩ := ThreeSylowContainment.exists_conjugate_eq_unipotent S
  let a := MulAut.conj g
  have hp : P.map a.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hP
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [ht,map_top_of_surjective _ a.surjective]
  obtain ⟨s,hs⟩ := OddSupplement.le_parabolic m hm (P.map a.toMonoidHom) (hg ▸ map_mono hSP) hp
  refine ⟨g,parabolic m s,?_,ree_parabolic_unique m hm s⟩
  rwa [parabolic_eq_rootParabolic] at hs

variable {G : Type*} [Group G] [Finite G]
theorem ree_sylow_overgroup_component_unique [IsSimpleGroup G] [Group.IsPerfect G]
    {m : ℕ} (hm : 1 ≤ m) (hmodel : LocalModels.IsReeF4At G m) :
    SylowOvergroupComponentUnique G := by
  obtain ⟨d,⟨e⟩⟩ := hmodel
  let a := e.trans d.modelEquiv
  let : IsSimpleGroup (Model m) := a.symm.isSimpleGroup
  let : Group.IsPerfect (Model m) := Group.IsPerfect.ofSurjective
    (f := a.toMonoidHom) a.surjective
  exact SylowOvergroupComponentUnique.of_equiv a (ree_model_unique m hm)
end CFSG.Quasithin.Chapter1.Section02.MovedMaximality
