module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Noncentral.Transfer.Midpoint.Contracts

/-!
# Obstruction to the edge-stabilizer span contract

The actor in the present `CenterSpan` and `ConjugateEscape` contracts is
required to belong to G_c intersect G_b. In the actual holomorph amalgam,
this intersection is Q_b. It fixes every neighbor of b, in particular d,
and fixes Z_b pointwise. Thus no such actor gives a distinct conjugate
plane. Its two local centers in the proposed span are the same, and the
already proved edge-center index excludes the proposed span altogether.

This diagnoses the contracts, not a counterexample to the source theorem:
the full contrary hypotheses may themselves be impossible. In particular,
`ConjugateEscape` has no instances of its distinct-plane antecedent here;
that interface supplies no source escape argument.

MS93 defines G_(c,b) as the relative normalizer N_(G_c)(T_b), with T_b = Q_b,
on printed p.881. The generation and selection on pp.903--904 use that
group, rather than G_c intersect G_b. A source-correct replacement must
retain that relative normalizer and prove the required geometric transport;
the current edge-stabilizer contracts cannot serve as that replacement.
They and their existing consumers are preserved unchanged by this module.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), notation on p.881 and the second (4.6.6), pp.903--904.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Midpoint
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- In the holomorph graph the midpoint edge stabilizer fixes every other
neighbor of that edge vertex. No source or critical-pair hypotheses are needed. -/
theorem edge_actor_fixes_neighbor
    (d c b : Vertex R) (hb : color R b = true)
    (hdb : Adjacent R d b) (hcb : Adjacent R c b)
    (h : FreeAmalgam R) (hhc : h ∈ stabilizer R c) (hhb : h ∈ stabilizer R b) :
    act R h d = d := by
  have hhQ : h ∈ Q R b := (Q_h_eq_edge R hb hcb).symm ▸ ⟨hhc, hhb⟩
  exact hhQ.2 d (adjacent_symm R hdb)

/-- The distinct-plane premise in the literal `ConjugateEscape` contract
is impossible already from its two edge conditions and actor memberships. -/
theorem conjugate_plane_eq_of_edge_stabilizers
    (d c b : Vertex R) (hd : color R d = false)
    (hdb : Adjacent R d b) (hcb : Adjacent R c b)
    (h : FreeAmalgam R) (hhc : h ∈ stabilizer R c) (hhb : h ∈ stabilizer R b) :
    ⁅Z R (act R h d), Q R b⁆ = ⁅Z R d, Q R b⁆ := by
  have hb : color R b = true := by
    have hn := adjacent_color_ne R hdb
    cases hx : color R b <;> simp_all
  rw [edge_actor_fixes_neighbor d c b hb hdb hcb h hhc hhb]

/-- Every actor permitted by the edge-stabilizer contract has fixed index
one on Z_b, as opposed to the moving actor selected in the source. -/
theorem edge_actor_fixed_index_eq_one
    (c b : Vertex R) (hb : color R b = true) (hcb : Adjacent R c b)
    (h : FreeAmalgam R) (hhc : h ∈ stabilizer R c) (hhb : h ∈ stabilizer R b) :
    (centralizer ({h} : Set (FreeAmalgam R))).relIndex (Z R b) = 1 := by
  have hhQ : h ∈ Q R b := (Q_h_eq_edge R hb hcb).symm ▸ ⟨hhc, hhb⟩
  apply relIndex_eq_one.mpr
  intro z hz y hy
  have hyh : y = h := Set.mem_singleton_iff.mp hy
  subst y
  have hz' : z ∈ omegaCenter (Q R b) := by
    simpa only [Z, hb, Bool.true_eq_false, if_false, edgeOmega] using hz
  exact (mem_omegaCenter_iff.mp hz').2.2 h hhQ

/-- Apply the existing index contradiction to the literal `CenterSpan`
witness. No actor in this intersection gives its subgroup product, even
without imposing a critical path or either contrary centrality hypothesis. -/
theorem no_center_span_witness_in_edge_stabilizers
    (common : CommonFacts R source geometry) (edge : EdgeFacts R)
    (d c b : Vertex R) (hd : color R d = false)
    (hdb : Adjacent R d b) (hcb : Adjacent R c b) :
    ¬ ∃ h : FreeAmalgam R, h ∈ stabilizer R c ∧ h ∈ stabilizer R b ∧
      Z R b =
        (Z R b ⊓ (center (stabilizer R d)).map (stabilizer R d).subtype) ⊔
        (Z R b ⊓ (center (stabilizer R (act R h d))).map
          (stabilizer R (act R h d)).subtype) := by
  rintro ⟨h, hhc, hhb, hspan⟩
  have hb : color R b = true := by
    have hn := adjacent_color_ne R hdb
    cases hx : color R b <;> simp_all
  apply not_edge_center_span_of_small_fixed_index common edge d b hd hdb h _ hspan
  rw [edge_actor_fixed_index_eq_one c b hb hcb h hhc hhb]
  decide

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Midpoint
