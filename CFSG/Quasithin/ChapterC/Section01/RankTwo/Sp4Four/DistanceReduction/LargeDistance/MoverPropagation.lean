module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.LargeDistance.Paths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalSelectedGeneration

/-!
# Mover comparisons along repeated critical paths

The source backward choice conjugates both the neighboring vertex and its
edge by the same element of the starting stabilizer. The first pair of
full movers is therefore conjugated and reversed. Equality and inequality
of that pair are invariant under every step. Exact overlaps transport the
same comparison to each newly covered even position of the later path.

The original tensor consumer uses this to supply both mover comparisons
needed for the fourth-seed argument. No global equality of neighboring
movers is assumed or proved by the transport itself.

Source: MS93 (5.10)(iii), printed p.922, and (5.11), pp.923--924.
-/

public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
variable {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R}

@[expose] def OrbitChoice (p : CriticalSegment geometry) (d t : Vertex R) : Prop :=
  ∃ g ∈ stabilizer R p.first,
    d = act R g (p.path.walk.getVert 2) ∧ t = act R g (p.path.walk.getVert 1)

@[expose] def MoverAgreement (p : CriticalSegment geometry) (k : ℕ) : Prop :=
  LocalPackage.J R (p.path.walk.getVert (2*k+2)) (p.path.walk.getVert (2*k+1)) =
    LocalPackage.J R (p.path.walk.getVert (2*k)) (p.path.walk.getVert (2*k+1))

/-- An orbit-preserving backward step reverses the initial pair of movers,
so it preserves both equality and inequality of the full movers. -/
theorem backward_mover_agreement_iff (hb : 2 ≤ geometry.b R)
    {p q : CriticalSegment geometry} (h : BackwardLink geometry OrbitChoice p q) :
    MoverAgreement q 0 ↔ MoverAgreement p 0 := by
  obtain ⟨t,⟨g,hg,hd,ht⟩,_,_,hqt⟩ := h.choice
  have hga : act R g p.first = p.first := hg
  have htwo : q.path.walk.getVert 2 = p.first := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using h.overlap 0 hb
  simp only [MoverAgreement,Nat.mul_zero,Nat.zero_add,SimpleGraph.Walk.getVert_zero]
  change LocalPackage.J R (q.path.walk.getVert 2) (q.path.walk.getVert 1) =
      LocalPackage.J R q.first (q.path.walk.getVert 1) ↔
    LocalPackage.J R (p.path.walk.getVert 2) (p.path.walk.getVert 1) =
      LocalPackage.J R p.first (p.path.walk.getVert 1)
  have hJ : LocalPackage.J R p.first (act R g (p.path.walk.getVert 1)) =
      (LocalPackage.J R p.first (p.path.walk.getVert 1)).map (MulAut.conj g⁻¹).toMonoidHom := by
    simpa only [hga] using smallMoverJoin_act R g p.first (p.path.walk.getVert 1)
  conv_lhs => rw [htwo,hqt,ht,hd,hJ,smallMoverJoin_act]
  constructor
  · intro he
    exact (Subgroup.map_injective (MulAut.conj g⁻¹).injective he).symm
  · intro he
    exact congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) he.symm

/-- Every first mover comparison in the repeated original orbit is the
same comparison as at the initial path. -/
theorem sequence_first_mover_agreement_iff (hb : 2 ≤ geometry.b R)
    (s : ℕ → CriticalSegment geometry)
    (hs : ∀ n, BackwardLink geometry OrbitChoice (s n) (s (n+1))) (n : ℕ) :
    MoverAgreement (s n) 0 ↔ MoverAgreement (s 0) 0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact (backward_mover_agreement_iff hb (hs n)).trans ih

/-- The literal overlap carries the initial mover comparison to each
newly covered even position on the later critical path. -/
theorem sequence_mover_agreement_iff (hb : 2 ≤ geometry.b R)
    (s : ℕ → CriticalSegment geometry)
    (hs : ∀ n, BackwardLink geometry OrbitChoice (s n) (s (n+1)))
    (n k : ℕ) (hk : 2*k+2 ≤ geometry.b R) :
    MoverAgreement (s (n+k)) k ↔ MoverAgreement (s 0) 0 := by
  have htwo := iterated_overlap OrbitChoice s hs n k 2 (by omega)
  have hone := iterated_overlap OrbitChoice s hs n k 1 (by omega)
  have hzero := shifted_start_vertex OrbitChoice s hs n k (by omega)
  change LocalPackage.J R ((s (n+k)).path.walk.getVert (2*k+2))
      ((s (n+k)).path.walk.getVert (2*k+1)) =
    LocalPackage.J R ((s (n+k)).path.walk.getVert (2*k))
      ((s (n+k)).path.walk.getVert (2*k+1)) ↔ _
  rw [show 2*k+2=2+2*k by omega,htwo,show 2*k+1=1+2*k by omega,hone,hzero]
  simpa only [MoverAgreement,Nat.mul_zero,Nat.zero_add,SimpleGraph.Walk.getVert_zero] using
    sequence_first_mover_agreement_iff hb s hs n

end CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
