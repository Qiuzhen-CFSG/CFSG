module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Ball
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Forward.Reversal
/-!
# Kernel-intersection geometry in MS93 (4.3.8)

Nonmovement makes the actual conjugated Z-joins equal. Together with the
forward commutation, this makes the kernel intersection centralize Z_mu.
Noncommutation at the fifth-predecessor edge selects a critical pair whose
second predecessor is the original sixth predecessor.

Source: Meierfrankenfeld--Stellmacher (1993), printed p.889, (4.3.8).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour.Kernel
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

theorem nonmoving_join_conjugate (source : LocalSource L R) (hb : 2 < geometry.b R)
    {a t v : Vertex R} (ha : color R a = false) (hat : Adjacent R a t)
    (hvt : Adjacent R v t) (hn : v ∉ movingNeighbors geometry a)
    (g : FreeAmalgam R) (hg : g ∈ stabilizer R a) :
    Z R (act R g v) ⊔ Z R a = Z R v ⊔ Z R a := by
  have hnorm : stabilizer R a ≤ normalizer (Z R a ⊔ Z R v : Subgroup (FreeAmalgam R)) := by
    by_cases hav : a = v
    · subst v
      simpa only [sup_idem] using Z_normalized R a
    · exact Backward.Moving.nonmoving_Z_join_normalized source hb ha
        (neighbor_distance_two ha hat hvt hav) hn
  have hmap := mem_normalizer_iff_map_conj_eq.mp (hnorm ((stabilizer R a).inv_mem hg))
  change (Z R a ⊔ Z R v).map (MulAut.conj g⁻¹).toMonoidHom = Z R a ⊔ Z R v at hmap
  have hga : act R g a = a := hg
  rw [Subgroup.map_sup, ← Z_act, ← Z_act, hga] at hmap
  simpa only [sup_comm] using hmap

theorem inf_commutation (source : LocalSource L R) (hb : 2 < geometry.b R)
    (forward : ForwardFacts geometry) (p : Counterexample geometry)
    {d t₃ t₅ : Vertex R} (hd : Before p.a p.a' d 4)
    (h₃ : Before p.a p.a' t₃ 3) (h₅ : Before p.a p.a' t₅ 5)
    (w : CentralOrbitWitnesses p d t₃ t₅) :
    ⁅VBall R p.a 4 ⊓ Q R d, Z R w.mu⁆ = ⊥ := by
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  have heq := nonmoving_join_conjugate source hb hdc
    (hd.adjacent (geometry := geometry) h₃) w.first_adjacent
    (forward.nonmoving p d t₃ t₅ hd h₃ h₅ w) w.second_conjugator w.second_local
  rw [w.second_image] at heq
  have hμ : Z R w.mu ≤ Z R w.lam ⊔ Z R d := heq.symm ▸ le_sup_left
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mpr
  apply hμ.trans
  exact sup_le
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (forward.commutation p d t₃ t₅ hd h₃ h₅ w))).trans (centralizer_le inf_le_left))
    ((commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes d hdc)).trans
      (centralizer_le inf_le_right))

omit [Finite M] in
theorem ball_le_stabilizer {a l : Vertex R} (ha : color R a = false)
    (hnear : (cosetGraph R).dist a l + 4 ≤ geometry.b R) :
    VBall R a 4 ≤ stabilizer R l := by
  rw [Forward.VBall_le_iff ha]
  intro x hx hxa
  apply Z_le_stabilizer_of_dist_le x (geometry.exists_critical x hx)
  rw [geometry.distance_constant x hx]
  change (cosetGraph R).dist x l ≤ geometry.b R
  have ht := (cosetGraph_connected R).dist_triangle (u := x) (v := a) (w := l)
  omega

/-- The genuine sixth predecessor is the second predecessor of every critical
pair selected by noncommutation at the chosen fifth-predecessor edge. -/
theorem moving_of_ball_noncommutation (source : LocalSource L R)
    (hb : 2 < geometry.b R) (p : Counterexample geometry)
    {t₅ s l : Vertex R} (h₅ : Before p.a p.a' t₅ 5)
    (hs : Before p.a p.a' s 6) (hlt : Adjacent R l t₅)
    (hl : color R l = false) (hne : ⁅VBall R p.a 4, Z R l⁆ ≠ ⊥) :
    l ∈ movingNeighbors geometry s := by
  have hpath := h₅.2
  rw [p.distance_eq_b] at hpath
  have htl : (cosetGraph R).dist t₅ l = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr (adjacent_symm R hlt))
  have hnear : (cosetGraph R).dist p.a l + 4 ≤ geometry.b R := by
    have htri := (cosetGraph_connected R).dist_triangle (u := p.a) (v := t₅) (w := l)
    omega
  obtain ⟨x, hx, hxa, hal, hcrit⟩ := Forward.exists_critical_of_not_commuting p.color_a hl hnear hne
  apply Forward.Reversal.critical_endpoint_moving source hb hx hcrit
  have hst : (cosetGraph R).dist s t₅ = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr
      (hs.adjacent (geometry := geometry) h₅))
  have hsPath := hs.2
  rw [p.distance_eq_b] at hsPath
  have htri₁ := (cosetGraph_connected R).dist_triangle (u := s) (v := t₅) (w := l)
  have htri₂ := (cosetGraph_connected R).dist_triangle (u := p.a) (v := s) (w := l)
  have hsl : (cosetGraph R).dist s l = 2 := by omega
  have hxl : (cosetGraph R).dist x l = geometry.b R :=
    hcrit.1.trans (geometry.distance_constant x hx)
  have htri₃ := (cosetGraph_connected R).dist_triangle (u := x) (v := p.a) (w := s)
  have htri₄ := (cosetGraph_connected R).dist_triangle (u := x) (v := s) (w := l)
  exact ⟨hsl, by omega⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour.Kernel
