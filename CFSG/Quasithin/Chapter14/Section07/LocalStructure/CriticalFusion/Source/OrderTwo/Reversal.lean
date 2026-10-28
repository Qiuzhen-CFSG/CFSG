module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.CriticalIntersections

/-!
# The precise earlier critical-path symmetry used in 14.7.69

Remark 14.7.39 invokes F.9.17: reverse the extended geodesic and then
re-mark its first edge. The new critical path need not be the old path,
and the marking element is not required to interchange both endpoints.
`Reversal` retains both paths, the actual right conjugator, the two U
markings, the two point markings and the critical rank selection.
`EarlierSymmetry` is the universal earlier-source implication; its producer
is qt-14-07 via 14.7.39 and F.9.17. It contains no module, intersection,
partition, centralizer, fusion or order-two conclusion.

The point markings transport the actual point centralizers and their
two-cores. The original full-image branch then forces the reverse full-image
branch by transporting the relative index and applying the reverse rank
selection. Thus the reverse module calculation is justified on precisely
the same original U/V₁ and projection, before conjugating its output.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
F.9.17, printed pp.324–325; 14.7.17 and 14.7.39, pp.1048 and 1060;
14.7.69, pp.1072–1073.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace CriticalPath

/-- The rank comparison and actual quadratic action in Notation 14.7.1.
Nontriviality of the star image is proved from the positive relative rank.
No ordinary-offender inequality of ratio one is imposed. -/
structure SourceSelection (c : CriticalPath (L := L) F) (d : Data T L V F W)
    : Prop extends c.RankSelection where
  quadratic : BinaryOffender.IsQuadratic d.action (c.Uα.subgroupOf F.H)

/-- The output of reversing and re-marking a critical geodesic. The four
markings refer to two possibly different paths, rather than a swapping element. -/
structure Reversal (c : CriticalPath (L := L) F) where
  path : CriticalPath (L := L) F
  conjugator : G
  conjugator_mem : conjugator ∈ GeometryGroup T L F
  base_U : conjugate F.U conjugator = c.Uα
  tip_U : conjugate path.Uα conjugator = F.U
  base_point : conjugate (F.Vi 1) conjugator = c.Zα
  tip_point : conjugate path.Zα conjugator = F.Vi 1
  earlier : path.EarlierImages
  selection : path.RankSelection

end CriticalPath

namespace Data

/-- The universal earlier 14.7.39/F.9.17 symmetry implication. This retains
the rank equality at which it is valid and only geometric/selection outputs. -/
def EarlierSymmetry (_d : Data T L V F W) : Prop :=
  ∀ c : CriticalPath (L := L) F, c.EarlierImages → c.SourceSelection _d →
    Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) =
      Nat.log 2 (Nat.card (star F c.Uα)) → Nonempty c.Reversal

end Data

namespace CriticalPath.Reversal
variable {c : CriticalPath (L := L) F} (r : c.Reversal)

omit [Finite G] in
private theorem conjugate_centralizer (A : Subgroup G) (g : G) :
    conjugate (centralizer (A : Set G)) g = centralizer (conjugate A g : Set G) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨(MulAut.conj g) x, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
  intro a ha
  apply (MulAut.conj g⁻¹).injective
  simpa [map_mul, MulAut.conj_apply, mul_assoc] using
    hx ((MulAut.conj g⁻¹) a) (mem_map_of_mem _ ha)

private theorem point_centralizer (d : Data T L V F W) :
    centralizer (F.Vi 1 : Set G) = F.H := by
  apply le_antisymm
  · rw [d.centralizer_eq]
    exact centralizer_le (by
      intro x hx
      have he : x = d.z := Set.mem_singleton_iff.mp hx
      rw [he, d.point]
      exact mem_zpowers d.z)
  · intro h hh x hx
    rw [d.point] at hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    have hz : d.z * h = h * d.z := (d.centralizer_eq ▸ hh) d.z (Set.mem_singleton d.z)
    exact (Commute.zpow_left hz n).eq

/-- The reverse endpoint centralizer goes to the original H. -/
theorem tip_H (d : Data T L V F W) :
    conjugate (conjugate F.H r.path.conjugator) r.conjugator = F.H := by
  rw [← CriticalIntersections.critical_point_centralizer_eq d r.path,
    conjugate_centralizer, r.tip_point, point_centralizer d]

/-- The literal reverse two-core goes to O₂(H), preserving the quotient kernel. -/
theorem tip_core (d : Data T L V F W) :
    conjugate r.path.Qα r.conjugator = F.H.pCoreIn 2 := by
  change ((conjugate F.H r.path.conjugator).pCoreIn 2).map
    (MulAut.conj r.conjugator⁻¹).toMonoidHom = _
  rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj r.conjugator⁻¹).injective]
  change (conjugate (conjugate F.H r.path.conjugator) r.conjugator).pCoreIn 2 = _
  rw [r.tip_H d]

/-- Reciprocal geodesic placement follows from the marked endpoints and
the original containment Uα≤H. -/
theorem reverse_placement (d : Data T L V F W) (earlier : c.EarlierImages) :
    F.U ≤ conjugate F.H r.path.conjugator := by
  intro x hx
  have hxU : (MulAut.conj r.conjugator⁻¹) x ∈ c.Uα :=
    r.base_U ▸ mem_map_of_mem _ hx
  have hxH : (MulAut.conj r.conjugator⁻¹) x ∈
      conjugate (conjugate F.H r.path.conjugator) r.conjugator :=
    (r.tip_H d).symm ▸ c.Uα_le_H earlier hxU
  exact (mem_map_iff_mem (MulAut.conj r.conjugator⁻¹).injective).mp hxH

/-- Full critical image is deduced for the reverse path from the actual
transported relative index and the earlier critical rank comparison. -/
theorem full_image (d : Data T L V F W) (earlier : c.EarlierImages)
    (hfull : star F c.Uα = star F (Q T L)) :
    star F r.path.Uα = star F (Q T L) := by
  have hi : (F.U ⊓ r.path.Qα).relIndex F.U = 4 := by
    have ht := relIndex_map_map_of_injective
      (f := (MulAut.conj r.conjugator⁻¹).toMonoidHom) (F.U ⊓ r.path.Qα) F.U
      (MulAut.conj r.conjugator⁻¹).injective
    change (conjugate (F.U ⊓ r.path.Qα) r.conjugator).relIndex
      (conjugate F.U r.conjugator) = (F.U ⊓ r.path.Qα).relIndex F.U at ht
    rw [conjugate_inf, r.base_U, r.tip_core d, inf_comm,
      CriticalIntersections.core_intersection_index_eq_star_card _ (c.Uα_le_H earlier),
      hfull, c.star_Q_card d earlier] at ht
    exact ht.symm
  rcases r.path.order_two_or_full d r.earlier r.selection with htwo | he
  · have hc := r.selection.comparison
    rw [hi, htwo] at hc
    norm_num at hc
  · exact he

end CriticalPath.Reversal
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
