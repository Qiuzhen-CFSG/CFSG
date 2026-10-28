module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Bound.Commutator
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Bound.Radius

/-!
# Assembly of the noncentral backward bound

The W(t) bound is proved in Commutator.lean by the critical-commutator
contradiction, retaining the reverse moving condition in its generators.
Radius.lean proves actual endpoint movement and identifies R₀ with H_c.
Choosing a moving neighbor on the backward edge and applying neighboring
Z-rigidity then gives the moving assertion at the vertex four before the
endpoint. The theorem `boundFacts` assembles both conclusions of (4.3.6)
from the preceding module, initial, local-control, edge-transfer and rigidity
stages, with no additional radius identity or later propagation premise.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.6), printed pp.886--887,
especially the first paragraph of the proof on p.887.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- An endpoint known to move at c gives the radius/H identification by
(4.3.2), at the actual last edge of this particular critical path. -/
theorem radius_eq_H_of_endpoint_moving (p : Counterexample geometry)
    (hb : 0 < geometry.b R) (initial : InitialFacts p)
    (control : ∀ q : Counterexample geometry, LocalControl q)
    (hm : p.a' ∈ movingNeighbors geometry p.c) :
    radiusCommutator p.a p.a' = H R p.c := by
  obtain ⟨t, ht⟩ := p.exists_before (show 1 ≤ geometry.b R by omega)
  have hct : Adjacent R p.c t := p.before.adjacent (geometry := geometry) ht
  exact (initial.radius_eq_edge t ht).trans
    (moving_edge_eq_at p hb control p.c t p.a' p.before_color hct ht.endpoint_adjacent hm).2.symm

/-- The radius/H identification gives the moving assertion by
choosing an actual moving neighbor and applying the authorized rigidity. -/
theorem noncentral_backward_moving_of_radius_eq_H (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (rigidity : RigidityFacts geometry) (d : Vertex R)
    (hd : Before p.a p.a' d 4) (hn : ¬ radiusCommutator p.a p.a' ≤ localCenter d)
    (hH : radiusCommutator p.a p.a' = H R p.c) :
    d ∈ movingNeighbors geometry p.c := by
  obtain ⟨t, ht⟩ := p.exists_before (show 3 ≤ geometry.b R by omega)
  have hct : Adjacent R p.c t := adjacent_symm R (ht.adjacent (geometry := geometry) p.before)
  have hdt : Adjacent R d t := hd.adjacent (geometry := geometry) ht
  have hdcol : color R d = false := (hd.color (by decide)).trans p.end_color
  obtain ⟨q, hqc, hqt⟩ := counterexample_at_edge p (by omega) p.c t p.before_color hct
  obtain ⟨e, het, he, _⟩ := rigidity.moving_Z_unique q t hqt
  have hec : e ∈ movingNeighbors geometry p.c := by simpa only [hqc] using he
  have hecol : color R e = false := moving_color p.before_color hec
  have hRe : radiusCommutator p.a p.a' = edgeDisplacement e t :=
    hH.trans (moving_edge_eq_at p (by omega) control p.c t e p.before_color hct het hec).2
  have hRU : radiusCommutator p.a p.a' ≤ U R e := by
    rw [hRe]
    exact Initial.edge_le_natural source e t hecol het
  have hRZ : radiusCommutator p.a p.a' ≤ Z R d := by
    rw [hRe]
    exact (edge_le_Z p hb control edge e t hecol het).trans
      (EdgeTransfer.edge_Z_le d t hdcol hdt)
  obtain ⟨r, hrd, hrt⟩ := counterexample_at_edge p (by omega) d t hdcol hdt
  have heq := rigidity.equal_Z r t hrt e d het hdt
    (fun h => hn ((le_inf hRU hRZ).trans h))
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.dist_comm]
    exact before_dist (geometry := geometry) hd p.before (by decide)
  · intro h
    exact hec.2 (heq ▸ h)

/-- Conditional assembly with the radius/H identity explicit. The theorem
`boundFacts` below discharges it using actual endpoint movement. -/
theorem boundFacts_of_noncentral_radius_eq_H (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p))
    (control : ∀ p : Counterexample geometry, LocalControl p) (edge : EdgeTransfer geometry)
    (rigidity : RigidityFacts geometry)
    (hH : ∀ (p : Counterexample geometry) (d : Vertex R), Before p.a p.a' d 4 →
      ¬ radiusCommutator p.a p.a' ≤ localCenter d →
        radiusCommutator p.a p.a' = H R p.c) :
    BoundFacts geometry where
  bound p d hd hn := ⟨noncentral_backward_moving_of_radius_eq_H source p hb
    control edge rigidity d hd hn (hH p d hd hn), fun t hat hgen =>
      noncentral_backward_bound source p hb modules initial control edge rigidity d t hd hn hat hgen⟩

/-- Source (4.3.6), including moving membership and the complete
reverse-moving W(t) bound, from the preceding stages alone. -/
theorem boundFacts (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p))
    (control : ∀ p : Counterexample geometry, LocalControl p) (edge : EdgeTransfer geometry)
    (rigidity : RigidityFacts geometry) : BoundFacts geometry := by
  apply boundFacts_of_noncentral_radius_eq_H source hb modules initial control edge rigidity
  intro p _ _ _
  obtain ⟨hi⟩ := initial p
  exact Radius.radius_eq_H source p hb hi control

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward
