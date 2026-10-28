module
public import Theory.GroupTheory.SylowPairSolvableGeneration
public import Theory.GroupTheory.SolvableSylowControl.Marked
public import Theory.SpecificGroups.G2.SolvableSylowNormalizer
public import Theory.AtlasPort.LinearGroups.G2.HigherFieldResiduals
public import Theory.AtlasPort.LinearGroups.G2.SylowNormalizer

/-!
# Odd solvable supplements to a normal G₂ component

The two concrete root parabolics are precisely the maximal overgroups
of a full Sylow two-subgroup in the split-octonion group. Their intersection
is the solvable Borel. Sylow conjugacy transports this pair to an arbitrary
marking. Together with the intrinsic solvable Sylow control, the odd-actor
argument excludes generation of an ambient extension from a proper invariant
nonsolvable subgroup and a solvable odd supplement.

Source: Aschbacher--Smith 5.1.13 and 5.2.2, printed pp.636 and 648.
The imported root and octonion constructions retain the ATLAS attribution
and license in LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Atlas.G2
open LieParabolicSetup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {G : Type*} [Group G] [Finite G]

/-- The two concrete root parabolics supply the intrinsic Sylow geometry. -/
theorem two_sylow_overgroups_of_equiv
    (e : G ≃* Model F) (S : Sylow 2 G) :
    ∃ P Q : Subgroup G, IsCoatom P ∧ IsCoatom Q ∧
      (S : Subgroup G) ≤ P ∧ (S : Subgroup G) ≤ Q ∧
      Group.IsSolvable (P ⊓ Q : Subgroup G) ∧
      ∀ J : Subgroup G, (S : Subgroup G) ≤ J → J ≠ ⊤ → J ≤ P ∨ J ≤ Q := by
  obtain ⟨_,a,_,hS⟩ := SolvableSylowControl.exists_aligned_equiv e S (sylow (F := F))
  change (S : Subgroup G).map a.toMonoidHom = unipotent at hS
  let P := parabolic₁.comap a.toMonoidHom
  let Q := parabolic₂.comap a.toMonoidHom
  have hUP : (S : Subgroup G) ≤ P := map_le_iff_le_comap.mp (by
    rw [hS]
    exact (show unipotent ≤ borel from le_sup_left).trans borel_le_parabolic₁)
  have hUQ : (S : Subgroup G) ≤ Q := map_le_iff_le_comap.mp (by
    rw [hS]
    exact (show unipotent ≤ borel from le_sup_left).trans borel_le_parabolic₂)
  refine ⟨P,Q,isCoatom_comap_of_surjective a.surjective HigherFieldResiduals.parabolic₁_isCoatom,
    isCoatom_comap_of_surjective a.surjective HigherFieldResiduals.parabolic₂_isCoatom,
    hUP,hUQ,?_,?_⟩
  · let : Group.IsSolvable (borel (K := F)) := DerivedNormalizerSolvable.isSolvable_borel
    let f : (P ⊓ Q : Subgroup G) →* borel (K := F) :=
      (a.toMonoidHom.comp (P ⊓ Q).subtype).codRestrict borel
        (fun x => (SylowNormalizer.parabolics_intersection (F := F)) ▸ x.property)
    exact Group.isSolvable_of_isSolvable_injective (f := f) (by
      intro x y hxy
      exact Subtype.ext (a.injective (congrArg Subtype.val hxy)))
  · intro J hSJ hJ
    have hj : J.map a.toMonoidHom ≠ ⊤ := by
      intro he
      apply hJ
      apply map_injective (f := a.toMonoidHom) a.injective
      rw [he,map_top_of_surjective _ a.surjective]
    have hu : unipotent ≤ J.map a.toMonoidHom := hS ▸ map_mono hSJ
    rcases ProperSylowOvergroups.le_parabolic (J.map a.toMonoidHom) hu
      (lt_top_iff_ne_top.mpr hj) with hp | hq
    · exact Or.inl (map_le_iff_le_comap.mp hp)
    · exact Or.inr (map_le_iff_le_comap.mp hq)

/-- A proper invariant nonsolvable subgroup of G₂ cannot generate the
ambient extension together with a Sylow and an odd solvable supplement. -/
theorem no_odd_solvable_supplement
    (hq : 2 < Nat.card F) (S : Sylow 2 G) (K R D : Subgroup G) [K.Normal]
    (e : K ≃* Model F) (hRK : R < K) (hRns : ¬ Group.IsSolvable R)
    (hSR : (S : Subgroup G) ≤ normalizer (R : Set G))
    (ho : Odd (Nat.card D)) (hsol : Group.IsSolvable ((S : Subgroup G) ⊔ D : Subgroup G))
    (hgen : R ⊔ (S : Subgroup G) ⊔ D = ⊤) : False := by
  let : IsSimpleGroup (Model F) := isSimple hq
  let : IsSimpleGroup K := e.isSimpleGroup
  apply no_solvable_odd_supplement_of_two_sylow_overgroups S K R D hRK hRns hSR ho hsol hgen
  · apply SolvableSylowControl.of_equiv e
    intro U J hs hu
    exact solvable_sylow_overgroup_normalizes hq U J hu hs
  · exact two_sylow_overgroups_of_equiv e
end Atlas.G2
