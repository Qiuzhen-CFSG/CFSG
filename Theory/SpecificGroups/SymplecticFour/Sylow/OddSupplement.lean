module
public import Theory.GroupTheory.SylowPairSolvableGeneration
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.Borel
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableSupplement
public import Theory.SpecificGroups.SymplecticFour.Sylow.CoreFree
public import Theory.SpecificGroups.SymplecticFour.BorelActionGeometry.Normalizers

/-!
# Excluding odd solvable generation over a symplectic component

The native point and plane parabolics exhaust proper overgroups of the
full unipotent subgroup. Sylow conjugacy carries this pair to any actual
marking; their intersection is the solvable Borel. The matrix solvable
overgroup calculation and the two-parabolic generation obstruction then
exclude an odd solvable supplement to a proper invariant nonsolvable
subgroup of a normal nonbinary symplectic component.

Source: Aschbacher--Smith 5.1.13 and 5.2.2, pp.636 and 648. The actual
source quotient application is in the Chapter6 prime changed-Sylow proof.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {G : Type*} [Group G] [Finite G]

/-- The two concrete maximal parabolics give the intrinsic marked Sylow geometry. -/
theorem two_sylow_overgroups_of_equiv
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 ≤ n)
    (e : G ≃* Sp F) (S : Sylow 2 G) :
    ∃ P Q : Subgroup G, IsCoatom P ∧ IsCoatom Q ∧
      (S : Subgroup G) ≤ P ∧ (S : Subgroup G) ≤ Q ∧
      Group.IsSolvable (P ⊓ Q : Subgroup G) ∧
      ∀ J : Subgroup G, (S : Subgroup G) ≤ J → J ≠ ⊤ → J ≤ P ∨ J ≤ Q := by
  obtain ⟨_,a,_,hS⟩ := SolvableSylowControl.exists_aligned_equiv e S (unipotentSylow hF hn)
  change (S : Subgroup G).map a.toMonoidHom = unipotent at hS
  let P := pointParabolic.comap a.toMonoidHom
  let Q := planeParabolic.comap a.toMonoidHom
  have hUP : (S : Subgroup G) ≤ P := (map_le_iff_le_comap).mp (by
    rw [hS]
    exact unipotent_le_borel.trans inf_le_left)
  have hUQ : (S : Subgroup G) ≤ Q := (map_le_iff_le_comap).mp (by
    rw [hS]
    exact unipotent_le_borel.trans inf_le_right)
  refine ⟨P,Q,isCoatom_comap_of_surjective a.surjective BorelActionGeometry.pointParabolic_isCoatom,
    isCoatom_comap_of_surjective a.surjective BorelActionGeometry.planeParabolic_isCoatom,
    hUP,hUQ,?_,?_⟩
  · let : Group.IsSolvable (borel (F := F)) := isSolvable_borel hF
    let f : (P ⊓ Q : Subgroup G) →* borel (F := F) :=
      (a.toMonoidHom.comp (P ⊓ Q).subtype).codRestrict borel (fun x => x.property)
    exact Group.isSolvable_of_isSolvable_injective (f := f) (by
      intro x y hxy
      exact Subtype.ext (a.injective (congrArg Subtype.val hxy)))
  · intro J hSJ hJ
    have hj : J.map a.toMonoidHom ≠ ⊤ := by
      intro he
      apply hJ
      apply (map_injective (f := a.toMonoidHom) a.injective)
      rw [he,map_top_of_surjective _ a.surjective]
    have hu : unipotent ≤ J.map a.toMonoidHom := hS ▸ map_mono hSJ
    rcases TwoConjugate.proper_unipotent_overgroup_le_parabolic hF hn
      (J.map a.toMonoidHom) hu hj with hp | hq
    · exact Or.inl (map_le_iff_le_comap.mp hp)
    · exact Or.inr (map_le_iff_le_comap.mp hq)

/-- A proper S-invariant nonsolvable subgroup and a solvable odd supplement
cannot generate an extension of the actual nonbinary symplectic component. -/
theorem no_odd_solvable_supplement
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 2 ≤ n)
    (S : Sylow 2 G) (K R D : Subgroup G) [K.Normal]
    (e : K ≃* Sp F) (hRK : R < K) (hRns : ¬ Group.IsSolvable R)
    (hSR : (S : Subgroup G) ≤ normalizer (R : Set G))
    (ho : Odd (Nat.card D)) (hsol : Group.IsSolvable ((S : Subgroup G) ⊔ D : Subgroup G))
    (hgen : R ⊔ (S : Subgroup G) ⊔ D = ⊤) : False := by
  let := SimpleQuotients.isSimpleGroup_of_card_eq_two_pow hn hF
  let : IsSimpleGroup (Sp F) := EvenProjective.equiv.isSimpleGroup
  let : IsSimpleGroup K := e.isSimpleGroup
  apply no_solvable_odd_supplement_of_two_sylow_overgroups S K R D hRK hRns hSR ho hsol hgen
  · apply SolvableSylowControl.of_equiv e
    have hlarge : 2 < Nat.card F := by
      rw [hF]
      exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by decide) hn)
    exact solvable_overgroups_of_orthogonal_root_orbits hF (by omega)
      (fun J hs hu => solvable_unipotent_point_orbit_orthogonal hlarge J hs hu)
  · exact two_sylow_overgroups_of_equiv hF (by omega) e
end Theory.SpecificGroups.SymplecticFour
