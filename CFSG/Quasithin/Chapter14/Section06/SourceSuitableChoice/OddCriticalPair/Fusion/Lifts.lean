module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Parabolic

public import Theory.GroupAction.BinaryWreathVectorOrbits

/-!
# Fusion of nonsingular lifts in the original orthogonal four-space

The original two-core moves the suitable vector within its two-element fiber
over the central line. Consequently equality of quotient coordinates lifts
to conjugacy by that core. Transitivity of the matrix wreath action on the
six nonsingular quotient vectors then gives conjugacy of all their actual
lifts, including both lifts over every quotient vector.

Source: Aschbacher--Smith, 14.6.17(3--4), printed p.1036.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
open Chapter15.Section03
variable {G : Type*} [Group G] [Finite G]
variable {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
attribute [local instance] orthogonalAction

include h in
theorem same_coordinate_lifts_conjugate
    (d : SourceOrthogonalFourAction D.H D.UH D.V₁ D.QH)
    (u v : (⁅D.UH,D.H⁆ : Subgroup G))
    (hmove : ¬ D.QH ≤ centralizer ({(u : G)} : Set G))
    (he : d.coordinates u = d.coordinates v) :
    ∃ q ∈ D.QH, (MulAut.conj q) (u : G) = (v : G) := by
  obtain ⟨q,hq,hqu⟩ := SetLike.not_le_iff_exists.mp hmove
  have hu : (u : G) ∈ D.UH :=
    (le_normalizer_iff_commutator_le_left.mp d.normalized) u.property
  have hz : ⁅(u : G),q⁆ ∈ D.V₁ :=
    h.commutator_UH_QH_le_point (commutator_mem_commutator hu hq)
  have hzn : ⁅(u : G),q⁆ ≠ 1 := by
    intro hh
    exact hqu (mem_centralizer_singleton_iff.mpr
      (commutatorElement_eq_one_iff_mul_comm.mp hh).symm)
  have hw : (u : G) * (v : G)⁻¹ ∈ D.V₁ := by
    have hk : u * v⁻¹ ∈ d.coordinates.ker := by
      change d.coordinates (u * v⁻¹) = 1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    rw [d.vector_kernel] at hk
    exact hk
  by_cases hw1 : (u : G) * (v : G)⁻¹ = 1
  · exact ⟨1,one_mem _,by simpa using mul_inv_eq_one.mp hw1⟩
  · obtain ⟨z,hz1,heq⟩ := (Nat.card_eq_two_iff' (1 : D.V₁)).mp h.point_card
    have hh : (u : G) * (v : G)⁻¹ = ⁅(u : G),q⁆ := by
      exact congrArg Subtype.val ((heq ⟨_,hw⟩ (fun hh => hw1 (congrArg Subtype.val hh))).trans
        (heq ⟨_,hz⟩ (fun hh => hzn (congrArg Subtype.val hh))).symm)
    refine ⟨q,hq,?_⟩
    have hc : (u : G) * ((MulAut.conj q) (u : G))⁻¹ = ⁅(u : G),q⁆ := by
      simp only [MulAut.conj_apply,commutatorElement_def,mul_inv_rev,inv_inv]
      group
    exact (inv_injective (mul_left_cancel (hh.trans hc.symm))).symm

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
open Chapter15.Section03
variable {G : Type*} [Group G] [Finite G]
variable {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
attribute [local instance] orthogonalAction

include h in
theorem nonsingular_lifts_conjugate
    (d : SourceOrthogonalFourAction D.H D.UH D.V₁ D.QH)
    (i j : OrthogonalPlaneIndex) (u v : (⁅D.UH,D.H⁆ : Subgroup G))
    (hu : (u : G) ∈ d.plane i) (hv : (v : G) ∈ d.plane j)
    (huz : (u : G) ∉ D.V₁) (hvz : (v : G) ∉ D.V₁)
    (hmove : ¬ D.QH ≤ centralizer ({(u : G)} : Set G)) :
    ∃ k ∈ D.H, (MulAut.conj k) (u : G) = (v : G) := by
  have hn (a : (⁅D.UH,D.H⁆ : Subgroup G)) (ha : (a : G) ∉ D.V₁) :
      d.coordinates a ≠ 1 := by
    intro he
    have hk : a ∈ d.coordinates.ker := he
    rw [d.vector_kernel] at hk
    exact ha hk
  obtain ⟨a,ha⟩ := BinaryWreathPointStabilizer.supported_transitive
    ((d.mem_plane_iff i u).mp hu) ((d.mem_plane_iff j v).mp hv) (hn u huz) (hn v hvz)
  obtain ⟨x,hx⟩ := d.onto a
  let v' := (⁅D.UH,D.H⁆).normalizerMonoidHom
    ⟨(x⁻¹ : D.H),normalizer_commutator_ge_right D.UH D.H (x⁻¹).property⟩ v
  have he : d.coordinates u = d.coordinates v' := by
    rw [show d.coordinates v' = d.actor (x⁻¹) • d.coordinates v from d.compatible (x⁻¹) v,
      map_inv,hx,←ha,inv_smul_smul]
  obtain ⟨q,hq,hqv⟩ := same_coordinate_lifts_conjugate h d u v' hmove he
  refine ⟨(x : G) * q,D.H.mul_mem x.property (pCoreIn_le 2 D.H hq),?_⟩
  have he' := congrArg (MulAut.conj (x : G)) hqv
  simpa [v',MulAut.conj_apply,mul_assoc] using he'

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
