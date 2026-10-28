module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.Orbit
public import Theory.Representation.BinaryConjugationSection
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport

/-!
# The terminal involution argument for the symplectic critical orbit

A natural four-dimensional section of the actual orbit, with a central
elementary kernel, transports one involution in the critical plane to every
nonzero quotient vector. Every element of the orbit is therefore an involution.
Since the orbit contains the plane, their commutator vanishes. The preceding
source calculation must construct this section and show the commutator is
nontrivial; this module proves the terminal implication on the actual carriers.

Source: MS93 (3.6), last symplectic paragraph on printed p.871.
-/

public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

omit [Finite M] in
/-- The marked alternating component already provides natural-vector transitivity. -/
theorem natural_action_transitive (u v : BinaryPermutation.natural (Fin 6))
    (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ m : M, BinaryPermutation.naturalRepresentation (Fin 6) (s.projection m) u = v := by
  obtain ⟨g,hg⟩ :=
    Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport.transitive_nonzero u v hu hv
  obtain ⟨m,hm,he⟩ := s.component_image.ge g.property
  exact ⟨m,he ▸ hg⟩

/-- The source's terminal involution argument on the literal critical orbit.
The section hypotheses name exactly the preceding orbit calculation on p.871. -/
theorem criticalOrbitNative_elementary_of_section
    (hb : s.geometry.b R = 2) {c : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (t : Vertex R)
    (d : Representation.BinaryConjugationSection (⊤ : Subgroup M)
      (criticalOrbitNative R c t)
      (criticalOrbitNative R c t ⊓ centralizer (L : Set M))
      ((BinaryPermutation.naturalRepresentation (Fin 6)).comp
        (s.projection.comp (⊤ : Subgroup M).subtype)))
    (hcentral : criticalOrbitNative R c t ⊓ centralizer (L : Set M) ≤
      centralizer (criticalOrbitNative R c t : Set M))
    (hkernel : IsElementaryAbelian 2
      ↥(criticalOrbitNative R c t ⊓ centralizer (L : Set M)))
    (hseed : ¬ (criticalPlane R c t).comap (embedM R) ≤
      criticalOrbitNative R c t ⊓ centralizer (L : Set M)) :
    IsElementaryAbelian 2 (criticalOrbitNative R c t) := by
  classical
  let := hkernel
  apply d.elementary_of_transitive hcentral
  · exact fun b hb => elemPow_eq_one_of_isElementaryAbelian b hb
  · obtain ⟨y,hy,hny⟩ := Set.not_subset.mp hseed
    refine ⟨⟨y,le_normalClosure hy⟩,?_,?_⟩
    · exact Subtype.ext (s.criticalOrbitNative_seed_square hb hc t y hy)
    · exact fun he => hny ((d.coordinates_eq_one_iff _).mp he)
  · intro u v hu hv
    obtain ⟨m,hm⟩ := s.natural_action_transitive u v hu hv
    exact ⟨⟨m,mem_top m⟩,hm⟩

/-- Application to the actual graph subgroup and plane, with no change of
conjugation convention or replacement by an abstract isomorphic group. -/
theorem criticalOrbit_commutator_plane_eq_bot_of_section
    (hb : s.geometry.b R = 2) {c : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (t : Vertex R)
    (d : Representation.BinaryConjugationSection (⊤ : Subgroup M)
      (criticalOrbitNative R c t)
      (criticalOrbitNative R c t ⊓ centralizer (L : Set M))
      ((BinaryPermutation.naturalRepresentation (Fin 6)).comp
        (s.projection.comp (⊤ : Subgroup M).subtype)))
    (hcentral : criticalOrbitNative R c t ⊓ centralizer (L : Set M) ≤
      centralizer (criticalOrbitNative R c t : Set M))
    (hkernel : IsElementaryAbelian 2
      ↥(criticalOrbitNative R c t ⊓ centralizer (L : Set M)))
    (hseed : ¬ (criticalPlane R c t).comap (embedM R) ≤
      criticalOrbitNative R c t ⊓ centralizer (L : Set M)) :
    ⁅criticalOrbit R c t,criticalPlane R c t⁆ = ⊥ := by
  let := s.criticalOrbitNative_elementary_of_section hb hc t d hcentral hkernel hseed
  apply le_bot_iff.mp
  apply (commutator_mono le_rfl (s.criticalPlane_le_orbit hb hc t)).trans
  change ⁅(criticalOrbitNative R c t).map (embedM R),
    (criticalOrbitNative R c t).map (embedM R)⁆ ≤ ⊥
  rw [←map_commutator,commutator_self_eq_bot_iff.mpr inferInstance,Subgroup.map_bot]

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
