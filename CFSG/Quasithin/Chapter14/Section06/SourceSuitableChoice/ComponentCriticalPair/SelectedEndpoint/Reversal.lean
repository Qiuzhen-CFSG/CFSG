module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.SelectedEndpoint.Geometry
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.Reversal

/-!
# The transporter in the symmetric critical-pair reversal

The genuine endpoint reversal retains jg in H, not merely equality of
H-invariant labels. Mapping the opposite-core intersections exchanges the
two ranks. In the equal-rank case the reversed endpoint therefore satisfies
the same quadratic budget. This is the symmetry used on p.1041; it also
allows its support placement to be transported to the literal inverse of g.

Source: Aschbacher--Smith F.9.17 and 14.6.24(3--4), pp.324,1041.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
open Section07 Section07.CriticalPairs
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {h : D.Hypothesis}

/-- The actual reversal includes the transporter in H. -/
theorem CriticalEndpoint.reverse_transporter (i : h.CriticalEndpoint)
    (hb : 3 ≤ h.b) (hn : ¬ i.conjugate D.UH ≤ D.QH) :
    ∃ j : h.CriticalEndpoint, j.representative * i.representative ∈ D.H := by
  have hsmall : D.UH ≤ D.VH := conjugateSpanBy_mono h.plus_le le_rfl
  have hn' : ¬ vertexModule (family (D := D)) h.f7Setup.seed i.vertex ≤
      (family (D := D) true).pCoreIn 2 := by
    intro hc
    apply hn
    have hm := map_mono (f := (D.LT ⊔ D.H).subtype) hc
    rw [i.large_map, ← AmalgamLocalCores.pCoreIn_map_of_injective
      2 _ (D.LT ⊔ D.H).subtype_injective,
      show (family (D := D) true).map (D.LT ⊔ D.H).subtype = D.H from
        map_subgroupOf_eq_of_le le_sup_right] at hm
    exact (map_mono hsmall).trans hm
  obtain ⟨j,hj⟩ := i.reversal (i.moving_of_not_le_core hb _ le_rfl hn')
  exact ⟨j,hj⟩

/-- One transporter acts on all invariant labels, with the book's right
conjugation translated to the project's left conjugation. -/
theorem CriticalEndpoint.labels_of_transporter (i j : h.CriticalEndpoint)
    (hp : j.representative * i.representative ∈ D.H)
    (A : Subgroup G) (hA : D.H ≤ normalizer (A : Set G)) :
    j.conjugate (i.conjugate A) = A := by
  rw [CriticalEndpoint.conjugate, CriticalEndpoint.conjugate, map_map]
  have he : (MulAut.conj j.representative).toMonoidHom.comp
      (MulAut.conj i.representative).toMonoidHom =
      (MulAut.conj (j.representative * i.representative)).toMonoidHom := by
    ext x
    simp [mul_assoc]
  rw [he]
  exact mem_normalizer_iff_map_conj_eq.mp (hA hp)

/-- The same literal transporter exchanges actor and denominator ranks. -/
theorem CriticalEndpoint.ranks_of_transporter (i j : h.CriticalEndpoint)
    (hb : 3 ≤ h.b) (hp : j.representative * i.representative ∈ D.H) :
    Nat.log 2 ((D.UH ⊓ j.conjugate D.QH).relIndex D.UH) =
      rank (((i.conjugate D.UH).subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H))) ∧
    rank (((j.conjugate D.UH).subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H))) =
      Nat.log 2 ((D.UH ⊓ i.conjugate D.QH).relIndex D.UH) := by
  have hU := i.labels_of_transporter j hp D.UH (le_normalizer_conjugateSpanBy _ _)
  have hQ := i.labels_of_transporter j hp D.QH
    (D.H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image D.H (pCore 2 D.H)))
  change (i.conjugate D.UH).map (MulAut.conj j.representative).toMonoidHom = D.UH at hU
  change (i.conjugate D.QH).map (MulAut.conj j.representative).toMonoidHom = D.QH at hQ
  constructor
  · have he := relIndex_map_map_of_injective
      (f := (MulAut.conj j.representative).toMonoidHom)
      (i.conjugate D.UH ⊓ D.QH) (i.conjugate D.UH)
      (MulAut.conj j.representative).injective
    rw [map_inf _ _ _ (MulAut.conj j.representative).injective,hU] at he
    rw [rank,i.actor_card h hb]
    exact congrArg (Nat.log 2) he
  · have he := relIndex_map_map_of_injective
      (f := (MulAut.conj j.representative).toMonoidHom)
      (D.UH ⊓ i.conjugate D.QH) D.UH (MulAut.conj j.representative).injective
    rw [map_inf _ _ _ (MulAut.conj j.representative).injective,hQ] at he
    rw [rank,j.actor_card h hb]
    exact congrArg (Nat.log 2) he

end CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis

namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.SelectedEndpoint
open Chapter13.Section08 Chapter13.Section08.CriticalGeometry
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] {D : ChapterF.Section09.Setup G} {h : D.Hypothesis}
    {ρ : Representation (ZMod 2) (Source.Hstar D.H) E}

/-- In either symmetric rank the reversed endpoint is quadratic with the
same positive rank. The original transporter remains part of the output. -/
theorem Geometry.reverse_quadratic_of_equal_ranks
    (q : Geometry h ρ) (hplus : D.Vplus = D.V) [IsElementaryAbelian 2 D.UH]
    (s : ConjugationSection D.H D.UH D.V₁ ρ)
    (heq : Nat.log 2 ((D.UH ⊓ q.endpoint.conjugate D.QH).relIndex D.UH) =
      rank (Source.starImage D.H (q.endpoint.conjugate D.UH))) :
    ∃ j : h.CriticalEndpoint,
      j.representative * q.endpoint.representative ∈ D.H ∧
      Reorientation.QuadraticMember ρ (Source.starImage D.H (j.conjugate D.UH)) ∧
      rank (Source.starImage D.H (j.conjugate D.UH)) =
        rank (Source.starImage D.H (q.endpoint.conjugate D.UH)) := by
  have hn : ¬ q.endpoint.conjugate D.UH ≤ D.QH := by
    intro hn
    exact not_le_of_gt q.opposite_denominator_strict (le_inf le_rfl hn)
  obtain ⟨j,hj⟩ := q.endpoint.reverse_transporter q.track_lower hn
  obtain ⟨hd,ha⟩ := q.endpoint.ranks_of_transporter j q.track_lower hj
  let c : BinaryConjugationSection D.H D.UH D.V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 D.H))) := {
    section_le := s.le, kernel_le := s.line_le, normalized := s.normalizes
    coordinates := s.quotient, onto := s.surjective, kernel_eq := s.kernel
    equivariant := fun a u => (s.conjugates a u).symm }
  have hc : Nat.log 2 ((D.UH ⊓ j.conjugate D.QH).relIndex D.UH) ≤
      rank (((j.conjugate D.UH).subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H))) := by
    rw [hd,ha,heq]
    rfl
  exact ⟨j,hj,(TwoComponents.quadraticEndpointOfComparison h j q.track_lower hplus c hc).member,
    ha.trans heq⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.SelectedEndpoint
