module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.UnitaryEndingCommutator

/-!
# The first noncentral comparisons in DGS 8.7

The unitary ending comparison already supplies the square estimate with the
literal binary parameter of the moving neighbor.  The product identity for
the two edge cores gives the companion comparison for the moving core index.
No commuting-intersection hypothesis from 8.6 is used here.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
8.7, printed p.140.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open CommutingTrivial
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The two first comparisons in 8.7, with the moving binary parameter
explicit.  The first inequality is the unitary residual square estimate; the
second is the literal edge-core product identity. -/
theorem reduced_noncentral_unitary_first_comparisons
    (h : HypothesisF11 L S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily L S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓
      Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ ≠ ⊥)
    {k m : ℕ} (hk : 2 ≤ k) (hm : 2 ≤ m)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) 3 (2^k) ∨
      IsSU (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) 3 (2^k))
    (w : (graph (Reduction.reducedFamily L S₀)).neighborSet a')
    (hmove : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓
      Q (Reduction.reducedFamily L S₀) a',
      Z (Reduction.reducedFamily L S₀) w.val⁆ ≠ ⊥)
    (hrw : primeRank 2 (graphLocalGroup (Reduction.reducedFamily L S₀) w.val ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) w.val)) ≤ m) :
    let F := Reduction.reducedFamily L S₀
    (Q F a').relIndex (V F beta 1)^2 ≤
        (Q F beta).relIndex (V F a' 1) * 2^m ∧
      (Q F a').relIndex (V F beta 1) ≤
        (Q F w.val).relIndex (V F beta 1) := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily L S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let : ∀ i, Finite (F i) := finite_endpoints ht
  have hb3 : 3 ≤ b F := (source_critical_geometry ht d hc hab hd hb hcomm).2.1
  have hpair := reduced_unitary_paired_square h hob models hc hab hd hb hcomm hne
    k hk hu w m hm hrw
  have hcore := source_paired_core_indices ht (Reduction.reduced_borel_core_sylow h)
    (Reduction.reducedEarlierLocalTheorems h hob) hc hab hd hb hcomm models w hmove
    (n := m) hrw
  let x := (Q F a').relIndex (V F beta 1)
  let s := (Q F w.val).relIndex (V F beta 1 ⊓ Q F a')
  let z := (Q F w.val).relIndex (V F beta 1)
  change x^2 ≤ (Q F beta).relIndex (V F a' 1) * 2^m ∧ x ≤ z
  refine ⟨by simpa only [x] using hpair.1, ?_⟩
  have hprod : x * s = z := by
    exact hcore.1
  have hsub : V F beta 1 ⊓ Q F a' ≤ stabilizer F beta :=
    inf_le_left.trans (V_le_stabilizer_of_dist_add_le_b F ht.generate beta beta 1
      (by simp only [SimpleGraph.dist_self, zero_add]; exact hb.le))
  let : IsElementaryAbelian 2 (V F beta 1) := V_elementary F ht.generate
    (fun v => (source_Z_Q_U ht v).1) (Reduction.reduced_kernel_sylow h) beta (by omega)
  have hVL : V F beta 1 ≤ d.localGroup a' := pGroup_le_localGroup F d a' _
    (IsElementaryAbelian.isPGroup 2 _) (V_le_stabilizer_of_dist_add_le_b F ht.generate
      beta a' 1 hd.le)
  let : Finite (d.localGroup a') := Finite.of_injective
    (inclusion (d.local_le a')) (inclusion_injective _)
  let : Finite ↥(V F beta 1 ⊓ Q F a') :=
    Finite.of_injective (inclusion (inf_le_left.trans hVL)) (inclusion_injective _)
  have hs : 0 < s := Nat.pos_of_ne_zero (((Q F w.val).subgroupOf
    (V F beta 1 ⊓ Q F a')).index_ne_zero_of_finite)
  have hx : x ≤ x * s := Nat.le_mul_of_pos_right x hs
  exact hx.trans_eq hprod

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
