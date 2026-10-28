module
public import Theory.GroupTheory.SylowPairSolvableGeneration
public import Theory.GroupTheory.SolvableSylowControl.Marked
public import Theory.SpecificGroups.PSL3.BorelTwoParabolics
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.UnipotentOvergroups
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.SolvableOvergroups
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.BorelStructure
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Excluding odd solvable generation over a projective linear-three component

The actual point and line parabolics exhaust proper full-Sylow overgroups
in PSL₃ over a nonbinary characteristic-two field. Their intersection is
the solvable flag Borel. Transport the pair along a Sylow-aligned marking
and apply the odd solvable supplement obstruction. No action or parabolic
identification is assumed of the smaller nonsolvable subgroup.

Source: Aschbacher--Smith 5.1.13 and 5.2.2, pp.636 and 648. The source
application uses the literal two-core quotient of the changed-Sylow group.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree.OddSupplement
variable {F : Type*} [Field F] [Finite F]
variable {G : Type*} [Group G] [Finite G]

/-- The point and line parabolics give the intrinsic marked Sylow geometry. -/
theorem two_sylow_overgroups_of_equiv
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 ≤ n)
    (e : G ≃* PSL(3,F)) (S : Sylow 2 G) :
    ∃ P Q : Subgroup G, IsCoatom P ∧ IsCoatom Q ∧
      (S : Subgroup G) ≤ P ∧ (S : Subgroup G) ≤ Q ∧
      Group.IsSolvable (P ⊓ Q : Subgroup G) ∧
      ∀ J : Subgroup G, (S : Subgroup G) ≤ J → J ≠ ⊤ → J ≤ P ∨ J ≤ Q := by
  obtain ⟨_,a,_,hS⟩ := SolvableSylowControl.exists_aligned_equiv e S (unipotentSylow F (by omega) hF)
  change (S : Subgroup G).map a.toMonoidHom = unipotent F at hS
  let P := (pointParabolic F).comap a.toMonoidHom
  let Q := (lineParabolic F).comap a.toMonoidHom
  have hUP : (S : Subgroup G) ≤ P := (map_le_iff_le_comap).mp (by
    rw [hS]
    exact (show unipotent F ≤ borel F from (normalizer_unipotent F (by omega) hF) ▸ (unipotent F).le_normalizer).trans ((projective_parabolics_inf F) ▸ inf_le_left))
  have hUQ : (S : Subgroup G) ≤ Q := (map_le_iff_le_comap).mp (by
    rw [hS]
    exact (show unipotent F ≤ borel F from (normalizer_unipotent F (by omega) hF) ▸ (unipotent F).le_normalizer).trans ((projective_parabolics_inf F) ▸ inf_le_right))
  refine ⟨P,Q,isCoatom_comap_of_surjective a.surjective (projective_parabolics_isCoatom F).1,
    isCoatom_comap_of_surjective a.surjective (projective_parabolics_isCoatom F).2,
    hUP,hUQ,?_,?_⟩
  · let : Group.IsSolvable (borel F) := BorelStructure.borel_isSolvable F hF
    let f : (P ⊓ Q : Subgroup G) →* borel F :=
      (a.toMonoidHom.comp (P ⊓ Q).subtype).codRestrict (borel F) (fun x => (projective_parabolics_inf F) ▸ x.property)
    exact Group.isSolvable_of_isSolvable_injective (f := f) (by
      intro x y hxy
      exact Subtype.ext (a.injective (congrArg Subtype.val hxy)))
  · intro J hSJ hJ
    have hj : J.map a.toMonoidHom ≠ ⊤ := by
      intro he
      apply hJ
      apply (Subgroup.map_injective (f := a.toMonoidHom) a.injective)
      rw [he,map_top_of_surjective _ a.surjective]
    have hu : unipotent F ≤ J.map a.toMonoidHom := hS ▸ map_mono hSJ
    rcases UnipotentOvergroups.overgroup_unipotent F
      (J.map a.toMonoidHom) hu hj with hp | hq
    · exact Or.inl (map_le_iff_le_comap.mp hp)
    · exact Or.inr (map_le_iff_le_comap.mp hq)

/-- A proper S-invariant nonsolvable subgroup and a solvable odd supplement
cannot generate an extension of the actual nonbinary linear component. -/
theorem no_odd_solvable_supplement
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 2 ≤ n)
    (S : Sylow 2 G) (K R D : Subgroup G) [K.Normal]
    (e : K ≃* PSL(3,F)) (hRK : R < K) (hRns : ¬ Group.IsSolvable R)
    (hSR : (S : Subgroup G) ≤ normalizer (R : Set G))
    (ho : Odd (Nat.card D)) (hsol : Group.IsSolvable ((S : Subgroup G) ⊔ D : Subgroup G))
    (hgen : R ⊔ (S : Subgroup G) ⊔ D = ⊤) : False := by
  let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup K := e.isSimpleGroup
  apply no_solvable_odd_supplement_of_two_sylow_overgroups S K R D hRK hRns hSR ho hsol hgen
  · apply SolvableSylowControl.of_equiv e
    exact SolvableOvergroups.solvable_overgroup_le_normalizer_of_two_le F hn hF
  · exact two_sylow_overgroups_of_equiv hF (by omega) e
end Matrix.PSL3.LinearThree.OddSupplement
