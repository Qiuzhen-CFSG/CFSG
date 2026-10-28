module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.Assembly
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear
public import GorensteinWalter.PSL2PerfectOfCard
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.SolvableOvergroups
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableOvergroupGeometry
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableRootOrbit
public import Theory.Representation.SU3.BinaryDegree.Perfectness
public import Theory.AtlasPort.LinearGroups.G2.SolvableSylowPlacement

/-!
# Solvable Sylow overgroups in the seven higher-field carriers

Every solvable subgroup containing a supplied Sylow two-subgroup normalizes
that same Sylow. Linear-three uses the full unipotent matrix calculation;
Sp₄ uses the proved orthogonal root-orbit theorem; G₂ uses the actual Bruhat
coverage and its Weyl-cell exclusions. The rank-one linear and unitary
cases use their unique proper Sylow overgroup. Perfectness of the actual
unitary carriers supplies properness, including the special central cover.

Actual multiplicative equivalences and Sylow conjugacy transport these
facts to the supplied model. The matrix fields and involutions in both
unitary cases retain the source's quadratic-field convention.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954, the assertion
that the solvable local group L₁T normalizes the component Borel.
-/

public section
open Subgroup
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.Normalization
open TorusModels.Assembly
open CFSG.Quasithin.ChapterF.Source

private theorem transport_overgroups {D E : Type*} [Group D] [Finite D] [Group E]
    (e : D ≃* E)
    (h : ∀ (S : Sylow 2 E) (A : Subgroup E), Group.IsSolvable A →
      (S : Subgroup E) ≤ A → A ≤ normalizer (S : Set E))
    (S : Sylow 2 D) (A : Subgroup D) (hA : Group.IsSolvable A) (hSA : (S : Subgroup D) ≤ A) :
    A ≤ normalizer (S : Set D) := by
  let : Group.IsSolvable A := hA
  have hs : Group.IsSolvable (A.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective A)
  have hn := h (S.mapSurjective e.surjective) (A.map e.toMonoidHom) hs (map_mono hSA)
  change A.map e.toMonoidHom ≤ normalizer ((S : Subgroup D).map e.toMonoidHom : Set E) at hn
  rw [← map_equiv_normalizer_eq] at hn
  exact (map_le_map_iff_of_injective e.injective).mp hn

private theorem rankOne_overgroups {D : Type*} [Group D] [Group.IsPerfect D]
    (S : Sylow 2 D) (facts : RankOneSylowFacts S)
    (A : Subgroup D) (hA : Group.IsSolvable A) (hSA : (S : Subgroup D) ≤ A) :
    A ≤ normalizer (S : Set D) := by
  have hnontrivial : Nontrivial D := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    let : Subsingleton D := hs
    apply facts.proper.ne
    apply top_unique
    intro x _
    simpa only [Subsingleton.elim x 1] using (normalizer (S : Set D)).one_mem
  let : Nontrivial D := hnontrivial
  apply facts.unique_maximal A hSA
  apply lt_top_iff_ne_top.mpr
  intro heq
  let : Group.IsSolvable A := hA
  have hsurj : Function.Surjective A.subtype := by
    intro x
    exact ⟨⟨x, heq ▸ mem_top x⟩, rfl⟩
  exact Group.IsPerfect.not_isSolvable D (Group.isSolvable_of_surjective hsurj)

private theorem sl3_overgroups {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 SL(3,F)) (A : Subgroup SL(3,F))
    (hA : Group.IsSolvable A) (hSA : (S : Subgroup SL(3,F)) ≤ A) :
    A ≤ normalizer (S : Set SL(3,F)) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(3,F) S
    (Matrix.PSL3.CartanActions.BorelQuotient.unipotentSLSylow F (by omega) hF)
  let e := MulAut.conj g
  have hS : (S : Subgroup SL(3,F)).map e.toMonoidHom = Matrix.PSL3.LinearThree.unipotentSL F :=
    congrArg Sylow.toSubgroup hg
  let : Group.IsSolvable A := hA
  let : Group.IsSolvable (A.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective A)
  have hU : Matrix.PSL3.LinearThree.unipotentSL F ≤ A.map e.toMonoidHom := hS ▸ map_mono hSA
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 2 ≤ n)
  have hN := (Matrix.PSL3.LinearThree.SolvableOvergroups.solvable_le_borelSL F hfour
    (A.map e.toMonoidHom) hU).trans (Matrix.PSL3.LinearThree.borelSL_le_normalizer_unipotentSL F)
  rw [← hS, ← map_equiv_normalizer_eq] at hN
  exact (map_le_map_iff_of_injective e.injective).mp hN

private theorem g2_overgroups {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F) (S : Sylow 2 (Atlas.G2.Model F)) (A : Subgroup (Atlas.G2.Model F))
    (hA : Group.IsSolvable A) (hSA : (S : Subgroup (Atlas.G2.Model F)) ≤ A) :
    A ≤ normalizer (S : Set (Atlas.G2.Model F)) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Atlas.G2.Model F) S Atlas.G2.LieParabolicSetup.sylow
  let e := MulAut.conj g
  have hS : (S : Subgroup (Atlas.G2.Model F)).map e.toMonoidHom = Atlas.G2.unipotent :=
    congrArg Sylow.toSubgroup hg
  let : Group.IsSolvable A := hA
  have hs : Group.IsSolvable (A.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective A)
  have hU : Atlas.G2.unipotent ≤ A.map e.toMonoidHom := hS ▸ map_mono hSA
  have hN := Atlas.G2.SolvableSylowPlacement.le_borel hF (A.map e.toMonoidHom) hU hs
  rw [← Atlas.G2.SylowNormalizer.normalizer_unipotent, ← hS, ← map_equiv_normalizer_eq] at hN
  exact (map_le_map_iff_of_injective e.injective).mp hN

/-- Every solvable overgroup of a supplied Sylow two-subgroup in any of the
seven higher-field models normalizes that very Sylow subgroup. -/
theorem model_solvable_overgroup_le_normalizer {D : Type*} [Group D] [Finite D]
    {n : ℕ} {unitary four : Bool} (model : Model D n unitary four) (hn : 1 < n)
    (S : Sylow 2 D) (A : Subgroup D) (hA : Group.IsSolvable A) (hSA : (S : Subgroup D) ≤ A) :
    A ≤ normalizer (S : Set D) := by
  cases model with
  | linearTwo F hF e hcover =>
    have hlarge : 3 < Nat.card F := by
      rw [hF]
      have := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 2 ≤ n)
      omega
    let : Group.IsPerfect PSL(2,F) := GorensteinWalter.psl2_isPerfect_of_card_gt_three F hlarge
    exact transport_overgroups e (fun P => rankOne_overgroups P
      (rankOneSylowFacts_psl2 F n (by omega) hF P)) S A hA hSA
  | specialLinearThree F hF e hcover =>
    exact transport_overgroups e (sl3_overgroups hF hn) S A hA hSA
  | projectiveLinearThree F hF e hcover =>
    exact transport_overgroups e (Matrix.PSL3.LinearThree.SolvableOvergroups.solvable_overgroup_le_normalizer_of_two_le
      F (by omega) hF) S A hA hSA
  | specialUnitaryThree F J hF hconj e hcover =>
    let : Group.IsPerfect J.specialSubgroup :=
      Representation.SU3.BinaryDegree.isPerfect_specialSubgroup J (by omega) hF hconj
    exact transport_overgroups e (fun P => rankOne_overgroups P
      (rankOneSylowFacts_su3 J n (by omega) hF hconj P)) S A hA hSA
  | projectiveUnitaryThree F J hF hconj e hcover =>
    let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Representation.SU3.BinaryDegree.isPerfect_projective J (by omega) hF hconj
    exact transport_overgroups e (fun P => rankOne_overgroups P
      (rankOneSylowFacts_psu3 J n (by omega) hF hconj P)) S A hA hSA
  | symplecticFour F hF e hcover =>
    have hlarge : 2 < Nat.card F := by
      rw [hF]
      exact (show (2 : ℕ) ^ 1 < 2 ^ n from Nat.pow_lt_pow_right (by decide) hn)
    exact transport_overgroups e
      (Theory.SpecificGroups.SymplecticFour.solvable_overgroups_of_orthogonal_root_orbits hF hn
        (Theory.SpecificGroups.SymplecticFour.solvable_unipotent_point_orbit_orthogonal hlarge)) S A hA hSA
  | g2 F hF e hcover =>
    have hlarge : 2 < Nat.card F := by
      rw [hF]
      exact (show (2 : ℕ) ^ 1 < 2 ^ n from Nat.pow_lt_pow_right (by decide) hn)
    exact transport_overgroups e (g2_overgroups hlarge) S A hA hSA

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.Normalization
