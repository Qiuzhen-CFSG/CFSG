module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Geometry

/-!
# Adjoining the endpoint to the backward span

If W(t) lies in the kernel two before the endpoint, its endpoint commutator
lies in the actual radius commutator R₀. Thus the endpoint normalizes W(t)V_a.
The edge stabilizer already normalizes both factors. When those two local
groups generate G_a, the product is normal in G_a. Every containment and
normality here is relative to the actual local stabilizer.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.7)(i), last paragraph
of printed p.887 and first paragraph of p.888. The existence of the required
edge and its W(t) containment remain separate mathematical obligations.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward
variable {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R}

private theorem normalizes_join_of_commutator_le {G : Type*} [Group G]
    (A W N : Subgroup G) (hN : A ≤ normalizer (N : Set G))
    (hcomm : ⁅W, A⁆ ≤ N) : A ≤ normalizer (↑(W ⊔ N) : Set G) := by
  apply le_normalizer_iff.mpr
  intro a ha x hx
  have hmap : (W ⊔ N).map (MulAut.conj a).toMonoidHom ≤ W ⊔ N := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rintro _ ⟨w, hw, rfl⟩
      have hc : ⁅a, w⁆ ∈ N :=
        hcomm (commutator_comm A W ▸ commutator_mem_commutator ha hw)
      have hh := (W ⊔ N).mul_mem (mem_sup_right hc) (mem_sup_left hw)
      simpa [MulAut.conj_apply, commutatorElement_def, mul_assoc] using hh
    · exact (mem_normalizer_iff_map_conj_eq.mp (hN ha)).le.trans le_sup_right
  exact hmap (mem_map_of_mem (MulAut.conj a).toMonoidHom hx)

variable [Finite M]

/-- Every subgroup of Q_c has endpoint displacement in R₀. This is the
literal commutator calculation used when W(t) ≤ Q_c. -/
theorem endpoint_commutator_le_radius (p : Counterexample geometry)
    (hb : 0 < geometry.b R) (initial : InitialFacts p)
    (W : Subgroup (FreeAmalgam R)) (hW : W ≤ Q R p.c) :
    ⁅W, Z R p.a'⁆ ≤ radiusCommutator p.a p.a' := by
  obtain ⟨s, hs⟩ := p.exists_before (show 1 ≤ geometry.b R by omega)
  have hcs : Adjacent R p.c s := p.before.adjacent (geometry := geometry) hs
  have hscol : color R s = true := by
    have hn := adjacent_color_ne R hs.endpoint_adjacent
    rw [p.end_color] at hn
    cases h : color R s <;> simp_all
  rw [initial.radius_eq_edge s hs, edgeDisplacement, commutator_comm]
  exact commutator_mono le_rfl (hW.trans (Q_le_adjacent_h R hscol hcs))

/-- R₀ commutes with every backward span because b > 6; there is no
assumption of centrality in either far local group. -/
theorem radius_commutes_backwardSpan (p : Counterexample geometry)
    (hb : 6 < geometry.b R) (t : Vertex R) :
    ⁅radiusCommutator p.a p.a', backwardSpan geometry p.a t⁆ = ⊥ := by
  rw [commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr
    ((backwardSpan_le_centralizer_V p.color_a hb t).trans
      (centralizer_le p.radius_le_start))

/-- The favorable W(t) bound and the source's local generation give
normality of the actual join W(t)V_a in G_a. -/
theorem backwardSpan_join_normal (p : Counterexample geometry)
    (hb : 4 < geometry.b R) (initial : InitialFacts p) (t : Vertex R)
    (hgen : (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a)
    (hW : backwardSpan geometry p.a t ≤ Q R p.c) :
    backwardSpan geometry p.a t ⊔ V R p.a ≤ stabilizer R p.a ∧
      ((backwardSpan geometry p.a t ⊔ V R p.a).subgroupOf (stabilizer R p.a)).Normal := by
  have hb₂ : 2 < geometry.b R := by omega
  have hlocal : backwardSpan geometry p.a t ⊔ V R p.a ≤ stabilizer R p.a :=
    (sup_le (backwardSpan_le_Q p.color_a hb t)
      (geometry.V_le_Q hb₂ p.a p.color_a)).trans (fun _ hx => hx.1)
  refine ⟨hlocal, normal_subgroupOf_of_le_normalizer ?_⟩
  rw [← hgen]
  apply sup_le
  · exact (le_inf (backwardSpan_normalized hb₂ p.a t p.color_a)
      (inf_le_left.trans (V_normalized p.a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  · exact normalizes_join_of_commutator_le _ _ _
      (p.end_Z_le_start_stabilizer.trans (V_normalized p.a))
      ((endpoint_commutator_le_radius p (by omega) initial _ hW).trans p.radius_le_start)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward
