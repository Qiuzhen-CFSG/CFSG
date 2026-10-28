module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement.ThreePart
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The actual M₂₂ subgroups to which the finite local analysis applies

The image of J = K∩M contains a Sylow two-subgroup of M₂₂. The image of
L₁ is solvable, normal relative to that image of J, and has order divisible
by three. These facts use the actual component quotient, normality of K
in H, T ≤ M, the theta identity, and the nontrivial seed action.

This reduces the subgroup step of Aschbacher–Smith 13.8.21(2), p.956,
to a precise native finite-group problem. No assertion about placement of
arbitrary solvable subgroups is made.
-/

public section
open Subgroup Sporadic.Mathieu
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement

variable {G : Type*} [Group G] [Finite G]
variable {H K L₁ T G₁ M : Subgroup G} (s : Setup H K L₁ T G₁ M)
include s

omit [Finite G] in
/-- Monotonicity keeps the image of L₁ inside the actual intersection image. -/
theorem Setup.native_seed_le_overlap :
    markedImage K L₁ s.model ≤ markedImage K (K ⊓ M) s.model :=
  map_mono (comap_mono s.seed_le_overlap)

omit [Finite G] in
/-- The relative normality, after transport through the same component map. -/
theorem Setup.native_seed_normal :
    ((markedImage K L₁ s.model).subgroupOf (markedImage K (K ⊓ M) s.model)).Normal := by
  have hn : K ⊓ M ≤ normalizer (L₁ : Set G) := by
    let := s.seed_normal_in_overlap
    exact le_normalizer_of_normal_subgroupOf s.seed_le_overlap
  have hnK : (K ⊓ M).subgroupOf K ≤ normalizer (L₁.subgroupOf K : Set K) :=
    (comap_mono hn).trans (le_normalizer_comap _)
  exact normal_subgroupOf_of_le_normalizer
    ((map_mono hnK).trans (le_normalizer_map _))

omit [Finite G] in
/-- Solvability is transported along the actual image map. -/
theorem Setup.native_seed_solvable : Group.IsSolvable (markedImage K L₁ s.model) := by
  let := s.solvable
  rw [← markedMap_range K L₁ s.model s.seed_le_component]
  exact Group.isSolvable_of_surjective
    (markedMap K L₁ s.model s.seed_le_component).rangeRestrict_surjective

/-- The three-elements survive the two-group kernel. -/
theorem Setup.native_seed_three_dvd (V₃ : Subgroup G) (hne : V₃ ≠ ⊥)
    (hgen : ⁅V₃, L₁⁆ = V₃) : 3 ∣ Nat.card (markedImage K L₁ s.model) := by
  apply (Nat.prime_three.dvd_iff_one_le_factorization Nat.card_pos.ne').mpr
  rw [← markedImage_three_factorization K L₁ s.model s.seed_le_component]
  exact (Nat.prime_three.dvd_iff_one_le_factorization Nat.card_pos.ne').mp
    (three_dvd_seed H M L₁ V₃ s.theta hne hgen)

/-- Restriction to the relatively normal component preserves the supplied Sylow
arrangement. Its native image lies in J because T ≤ M. -/
theorem Setup.native_overlap_contains_sylow :
    ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ markedImage K (K ⊓ M) s.model := by
  let := s.component_normal
  obtain ⟨P, hP⟩ := s.sylow.exists_subgroupOf_eq_of_normal (K.subgroupOf H)
  let e : K.subgroupOf H ≃* K := subgroupOfEquivOfLe s.component_le
  let f : K.subgroupOf H →* M22 := (componentMap K s.model).comp e.toMonoidHom
  have hf : Function.Surjective f := (componentMap_surjective K s.model).comp e.surjective
  refine ⟨P.mapSurjective hf, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hxT : x.val.val ∈ T := by
    rw [hP, s.sylow_eq] at hx
    exact hx
  exact ⟨e x, ⟨x.property, s.sylow_le_M hxT⟩, rfl⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement
