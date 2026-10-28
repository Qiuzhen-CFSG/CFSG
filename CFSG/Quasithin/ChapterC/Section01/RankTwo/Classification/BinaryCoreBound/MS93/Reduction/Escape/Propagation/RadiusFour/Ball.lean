module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Edges

/-!
# Local radius spans and the common-normal-subgroup obstruction

Covariance makes every radius span normal under its own stabilizer.
A span of radius strictly smaller than the critical distance lies in Q
at an M-vertex, including generators of both colors. The radius-three span
at an adjacent H-vertex consequently lies in the edge overlap when b > 4.
If it were also normal at the M-vertex, source characteristic faithfulness
would make it trivial, contradicting the natural subgroup of order eight
that it contains.

Source: Meierfrankenfeld--Stellmacher (1993), the normal-radius contradiction
in (4.3.8), printed p.889, using the characteristic condition and (2.1)(iii).
This proves the obstruction; its application still requires the source
argument establishing the second relative normality.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

theorem VBall_normalized (a : Vertex R) (n : ℕ) :
    stabilizer R a ≤ normalizer (VBall R a n : Set (FreeAmalgam R)) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (VBall R a n).map (MulAut.conj g).toMonoidHom = VBall R a n
  have h := VBall_act R g⁻¹ a n
  have hga : act R g⁻¹ a = a := (stabilizer R a).inv_mem hg
  simpa only [hga, inv_inv] using h.symm

theorem VBall_le_of_dist_add_le (a c : Vertex R) (n m : ℕ)
    (h : (cosetGraph R).dist c a + n ≤ m) : VBall R c n ≤ VBall R a m := by
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  apply le_iSup_of_le y
  have htri := (cosetGraph_connected R).dist_triangle (u := y) (v := c) (w := a)
  exact le_iSup_of_le (show (cosetGraph R).dist y a ≤ m by omega) le_rfl

theorem VBall_le_Q (a : Vertex R) (ha : color R a = false) (n : ℕ)
    (hn : n < geometry.b R) : VBall R a n ≤ Q R a := by
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  by_cases hcol : color R y = false
  · apply Z_le_Q_of_dist_lt R y (geometry.exists_critical y hcol)
    rw [geometry.distance_constant y hcol]
    exact lt_of_le_of_lt hy hn
  · have hyne : y ≠ a := by intro heq; exact hcol (heq ▸ ha)
    have hpos := (cosetGraph_connected R).pos_dist_of_ne hyne
    obtain ⟨s, hys, hsa⟩ := exists_adjacent_dist_sub_one R y a hpos
    have hs : color R s = false := by
      have hh := adjacent_color_ne R hys
      cases hyc : color R y <;> cases hsc : color R s <;> simp_all
    apply (EdgeTransfer.edge_Z_le s y hs (adjacent_symm R hys)).trans
    apply Z_le_Q_of_dist_lt R s (geometry.exists_critical s hs)
    rw [geometry.distance_constant s hs]
    change (cosetGraph R).dist s a < geometry.b R
    omega

/-- The radius-three span about an H-vertex cannot also be normal in its
M-neighbor. The source characteristic condition kills a common local normal
subgroup, whereas the span contains the nonzero natural subgroup. -/
theorem radius_three_not_normal (source : LocalSource L R)
    (modules : ModuleFacts source geometry) (hb : 4 < geometry.b R)
    (a t : Vertex R) (ha : color R a = false) (hat : Adjacent R a t) :
    ¬ ((VBall R t 3).subgroupOf (stabilizer R a)).Normal := by
  intro hnormal
  have hdist : (cosetGraph R).dist t a = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr (adjacent_symm R hat))
  have hQ : VBall R t 3 ≤ Q R a :=
    (VBall_le_of_dist_add_le a t 3 4 (by rw [hdist])).trans (VBall_le_Q a ha 4 hb)
  have hN := no_common_normal_at_edge R source.characteristic a t ha hat
    (VBall R t 3) (le_inf (hQ.trans (fun _ hx => hx.1))
      (hQ.trans (fun _ hx => hx.2 t hat))) hnormal
    (normal_subgroupOf_of_le_normalizer (VBall_normalized t 3))
  have hZ : Z R a ≤ VBall R t 3 := le_iSup_of_le a
    (le_iSup_of_le (show (cosetGraph R).dist a t ≤ 3 by
      rw [SimpleGraph.dist_comm, hdist]; omega) le_rfl)
  have hU : U R a = ⊥ := le_bot_iff.mp ((U_le_Z a).trans (hZ.trans hN.le))
  have hcard := modules.natural.card_at a ha
  rw [hU, card_bot] at hcard
  omega

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour
