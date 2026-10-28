module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.SixParabolics
public import Theory.SpecificGroups.SymmetricSix.Parabolics.SolvableGeneration
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.FourNormalizers.SixParabolicTypes

/-!
# The intrinsic A₆ diagram obstruction from solvable Sylow overgroups

An automorphism group between Inn(A₆) and the natural S₆ is one of these
two groups. In both, a Sylow two-subgroup lies in a conjugate incident pair
of solvable duad and syntheme parabolics, and those parabolics generate.
Transport through the actual inner or natural embedding therefore makes
the solvable-overgroup span the whole actor group.

The re-exported coordinate identities identify the two four-group
normalizer classes with the literal source parabolic types. Consequently
a proper overlap containing the span forces an actual non-natural diagram
actor. No representation-theoretic Dynkin exclusion is used here. The source
assembly must still transport its conjugation homomorphism and kernel.

Source: Aschbacher–Smith, 13.8.21(2), printed p.956 (PDF p.973),
using the six-letter geometry of I.5, printed pp.419–422.
-/

public section
open Subgroup AlternatingSix.ShadowLocal
open Theory.SpecificGroups.SymmetricSix hiding A6
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics

private theorem alternating_image : (alternatingGroup (Fin 6)).map permutationAction = AlternatingSix.ShadowLocal.inner := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, permutationAction_coe ⟨x, hx⟩ |>.symm⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨x.val, x.property, permutationAction_coe x⟩

/-- There is no intermediate group between the inner A₆ and natural S₆. -/
theorem six_eq_inner_or_natural (A : Subgroup AutA6)
    (hI : AlternatingSix.ShadowLocal.inner ≤ A) (hN : A ≤ natural) :
    A = AlternatingSix.ShadowLocal.inner ∨ A = natural := by
  let B := A.comap permutationAction
  have hB : alternatingGroup (Fin 6) ≤ B := by
    intro x hx
    apply hI
    exact ⟨⟨x, hx⟩, (permutationAction_coe ⟨x, hx⟩).symm⟩
  have hd : B.index ∣ 2 := by
    simpa only [alternatingGroup.index_eq_two] using index_dvd_of_le hB
  have hm : B.map permutationAction = A := by
    rw [map_comap_eq]
    exact inf_eq_right.mpr hN
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · right
    rw [index_eq_one.mp h, ← MonoidHom.range_eq_map] at hm
    exact hm.symm
  · left
    rw [Equiv.Perm.eq_alternatingGroup_of_index_eq_two h, alternating_image] at hm
    exact hm.symm

private theorem span_of_equiv {X : Type*} [Group X] [Finite X]
    (A : Subgroup AutA6) (e : X ≃* A) (P : Sylow 2 A)
    (hpair : ∀ Q : Sylow 2 X, ∃ J K : Subgroup X,
      (Q : Subgroup X) ≤ J ∧ (Q : Subgroup X) ≤ K ∧
      Group.IsSolvable J ∧ Group.IsSolvable K ∧ J ⊔ K = ⊤) :
    solvableOvergroupSpan A ⊥ ((P : Subgroup A).map A.subtype) = A := by
  let Q := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨J, K, hJ, hK, hsJ, hsK, hjoin⟩ := hpair Q
  let f : X →* AutA6 := A.subtype.comp e.toMonoidHom
  have hr : f.range = A := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  have hP : (Q : Subgroup X).map f = (P : Subgroup A).map A.subtype := by
    change ((P : Subgroup A).map e.symm.toMonoidHom).map f = _
    rw [map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    exact congrArg Subtype.val (e.apply_symm_apply x)
  have hle (H : Subgroup X) (hQ : (Q : Subgroup X) ≤ H) (hs : Group.IsSolvable H) :
      H.map f ≤ solvableOvergroupSpan A ⊥ ((P : Subgroup A).map A.subtype) := by
    apply le_sSup
    refine ⟨?_, ?_, ?_⟩
    · simpa only [bot_sup_eq, ← hP] using map_mono (f := f) hQ
    · exact hr ▸ map_le_range f H
    · let := hs
      exact Group.isSolvable_of_surjective (f.subgroupMap_surjective H)
  apply le_antisymm
  · exact sSup_le (fun _ h => h.2.1)
  · have h := sup_le (hle J hJ hsJ) (hle K hK hsK)
    rwa [← Subgroup.map_sup, hjoin, ← MonoidHom.range_eq_map, hr] at h

/-- For every Sylow two-subgroup, the solvable parabolic overgroups
generate any natural actor group containing the inner A₆. -/
theorem six_natural_solvableOvergroupSpan (A : Subgroup AutA6)
    (hI : AlternatingSix.ShadowLocal.inner ≤ A) (hN : A ≤ natural)
    (P : Sylow 2 A) :
    solvableOvergroupSpan A ⊥ ((P : Subgroup A).map A.subtype) = A := by
  rcases six_eq_inner_or_natural A hI hN with rfl | rfl
  · exact span_of_equiv AlternatingSix.ShadowLocal.inner innerEquiv P a6_solvable_parabolic_generation
  · exact span_of_equiv natural
      GLS3.Chapter5.permSixMulEquivNaturalAlternatingAutomorphisms P solvable_parabolic_generation

/-- A proper overlap containing all solvable Sylow overgroups forces
an automorphism outside the natural S₆. This is independent of the
representation-theoretic exclusion of that diagram action. -/
theorem six_nonNatural_of_span_le_proper (A J : Subgroup AutA6)
    (hI : AlternatingSix.ShadowLocal.inner ≤ A) (P : Sylow 2 A)
    (hJ : J < A)
    (hspan : solvableOvergroupSpan A ⊥ ((P : Subgroup A).map A.subtype) ≤ J) :
    ¬ A ≤ natural := by
  intro hN
  rw [six_natural_solvableOvergroupSpan A hI hN P] at hspan
  exact hJ.not_ge hspan

/-- The same obstruction supplies an actual actor failing to preserve
both source parabolic types. The parent transports its source action here. -/
theorem six_exists_diagram_action_of_span_le_proper (A J : Subgroup AutA6)
    (hI : AlternatingSix.ShadowLocal.inner ≤ A) (P : Sylow 2 A)
    (hJ : J < A)
    (hspan : solvableOvergroupSpan A ⊥ ((P : Subgroup A).map A.subtype) ≤ J) :
    ∃ β ∈ A, β ∉ natural ∧ ¬ (
      (∃ g : A6, a6DuadStabilizer.map β.toMonoidHom =
        a6DuadStabilizer.map (MulAut.conj g).toMonoidHom) ∧
      (∃ g : A6, a6SynthemeStabilizer.map β.toMonoidHom =
        a6SynthemeStabilizer.map (MulAut.conj g).toMonoidHom)) := by
  obtain ⟨β, hβ, hn⟩ := SetLike.not_le_iff_exists.mp
    (six_nonNatural_of_span_le_proper A J hI P hJ hspan)
  exact ⟨β, hβ, hn, fun h => hn
    ((AlternatingSix.ShadowLocal.FourNormalizers.SixParabolics.natural_iff_preserves_source_parabolic_types β).mpr h)⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics
