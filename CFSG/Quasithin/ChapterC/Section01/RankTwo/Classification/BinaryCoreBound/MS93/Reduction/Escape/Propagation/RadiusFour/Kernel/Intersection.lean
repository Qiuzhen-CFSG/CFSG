module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Kernel.Basic

/-!
# The final xi-conjugate argument of MS93 (4.3.8)

Conjugate the second predecessor through the stabilizer of the fourth to
an actual neighbor of the fifth. Its Z-join is preserved by nonmovement.
If the radius-four ball centralizes this conjugate, the kernel intersection
centralizes the original second predecessor. Otherwise both the conjugate
and the fourth predecessor move at the sixth, so rigidity identifies their
Z-layers and gives the same centralizer bound.

The preceding radius-four noncontainment is explicit in this helper and
is discharged by Kernel's final assembly.
Source: Meierfrankenfeld--Stellmacher (1993), printed p.889, final paragraph
of (4.3.8), stopping before the final contradiction for (4.3).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour.Kernel
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- The final xi-conjugate argument on p.889. The noncontainment premise is
exactly the conclusion of the preceding normal-radius contradiction. -/
theorem intersection_le_of_not_le (source : LocalSource L R)
    (hb : 2 < geometry.b R) (rigidity : RigidityFacts geometry)
    (backward : BackwardFacts geometry) (p : Counterexample geometry)
    {d : Vertex R} (hd : Before p.a p.a' d 4)
    (hnot : ¬ VBall R p.a 4 ≤ Q R d) :
    VBall R p.a 4 ⊓ Q R d ≤ Q R p.c := by
  have hlarge := rigidity.six_lt p
  obtain ⟨t₃, h₃⟩ := p.exists_before (show 3 ≤ geometry.b R by omega)
  obtain ⟨t₅, h₅⟩ := p.exists_before (show 5 ≤ geometry.b R by omega)
  obtain ⟨s, hs⟩ := p.exists_before (show 6 ≤ geometry.b R by omega)
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  have hsc : color R s = false := (hs.color (by decide)).trans p.end_color
  have hd₃ : Adjacent R d t₃ := hd.adjacent (geometry := geometry) h₃
  have hc₃ : Adjacent R p.c t₃ := adjacent_symm R (h₃.adjacent (geometry := geometry) p.before)
  have hd₅ : Adjacent R d t₅ := adjacent_symm R (h₅.adjacent (geometry := geometry) hd)
  have hs₅ : Adjacent R s t₅ := hs.adjacent (geometry := geometry) h₅
  obtain ⟨g, hg, hgt⟩ := stabilizer_transitive_neighbors R d hd₃ hd₅
  have hxi : Adjacent R (act R g p.c) t₅ := by
    rw [← hgt]
    exact (adjacent_act_iff R g p.c t₃).mpr hc₃
  have hxic : color R (act R g p.c) = false :=
    (action_preserves_color R g p.c).trans p.before_color
  have hjoin := nonmoving_join_conjugate source hb hdc hd₃ hc₃
    (backward.far_not_moving p d hd) g hg
  have hIlocal : VBall R p.a 4 ⊓ Q R d ≤ stabilizer R p.c := by
    have hcd : (cosetGraph R).dist d p.c = 2 := by
      apply neighbor_distance_two hdc hd₃ hc₃
      intro heq
      have h := hd.1
      rw [heq, p.before.1] at h
      omega
    exact inf_le_right.trans (Q_le_stabilizer_of_dist_le_two d p.c hdc p.before_color hcd.le)
  rw [← source.C_eq_Q geometry.radical_ne_bot p.c p.before_color]
  apply le_inf hIlocal
  have hId : VBall R p.a 4 ⊓ Q R d ≤ centralizer (Z R d : Set (FreeAmalgam R)) :=
    inf_le_right.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes d hdc)))
  have hcjoin : Z R p.c ≤ Z R (act R g p.c) ⊔ Z R d := hjoin.symm ▸ le_sup_left
  by_cases hcomm : ⁅VBall R p.a 4, Z R (act R g p.c)⁆ = ⊥
  · apply le_centralizer_iff.mpr
    apply hcjoin.trans
    exact sup_le
      ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans
        (centralizer_le inf_le_left)) (le_centralizer_iff.mp hId)
  · have hxiMove := moving_of_ball_noncommutation source hb p h₅ hs hxi hxic hcomm
    have hdcomm : ⁅VBall R p.a 4, Z R d⁆ ≠ ⊥ := by
      intro heq
      apply hnot
      rw [← source.C_eq_Q geometry.radical_ne_bot d hdc]
      refine le_inf (ball_le_stabilizer (geometry := geometry) p.color_a ?_)
        (commutator_eq_bot_iff_le_centralizer.mp heq)
      have hpath := hd.2
      rw [p.distance_eq_b] at hpath
      omega
    have hdMove := moving_of_ball_noncommutation source hb p h₅ hs hd₅ hdc hdcomm
    obtain ⟨q, hqa, hqt⟩ := counterexample_at_edge p (by omega) s t₅ hsc hs₅
    obtain ⟨v, _hvt, _hvm, hv⟩ := rigidity.moving_Z_unique q t₅ hqt
    rw [hqa] at hv
    have heq : Z R (act R g p.c) = Z R d :=
      (hv _ hxi hxiMove).trans (hv d hd₅ hdMove).symm
    rw [heq, sup_idem] at hcjoin
    exact hId.trans (centralizer_le hcjoin)
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour.Kernel

