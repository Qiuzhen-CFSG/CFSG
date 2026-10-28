module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoCartanResidualOrderPath

/-!
# Source consumer for the terminal residual order

The terminal residual witness already contains the full Cartan, its normalizer
control, and the trivial terminal-core intersection.  The linear quotient at
the terminal vertex supplies the local `SL(2, k)` marking required by the
normalized residual-card calculation.  This module simply assembles those
existing source facts for the same path witness.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Reduction Noncommuting NoncommutingProfile
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))
local notation "α" => base F false
local notation "β" => base F true

/-- The residual attached to the source Cartan path has the terminal
coefficient-field order.  The quotient marking is chosen at the actual
terminal vertex `y`, while all Cartan and residual data are those of the
single witness supplied by `original_bTwo_path_cartan_residual_trivial`. -/
theorem original_bTwo_path_cartan_residual_order
    (h : HypothesisF11 L S) {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hy : (graph F).Adj u y) (hyne : y ≠ β)
    (hns : ¬ Group.IsSolvable (parabolic L S 0)) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2),
      ∃ g : G₀ L S, g ∈ graphLocalGroup F α ∧ g • β = t ∧
        Nat.card (bTwoResidual F β t u (g • u)) = Nat.card k := by
  obtain ⟨K,hfix,hd,hgen,ho,hcomm,_,g,hg,hgK,hgt,_,_,_,_,
    hW,hR,hdec,hdis,hdisu,hKn,hRC,hJC,hthree,hconj,hRne,hzero⟩ :=
      original_bTwo_path_cartan_residual_trivial h hc hne hb hβu ht htne hy hyne hns
  let _ := hcomm
  obtain ⟨m,hm,J,fJ,finJ,hJ,⟨eJ⟩⟩ :=
    reduced_noncommuting_actor_quotients_linear h hc hne y
  let _ := fJ
  let _ := finJ
  let _ : Fintype J := Fintype.ofFinite J
  let _ : CharP J 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hJ)
  let ey := eJ.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi J)
    ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩).symm
  let R := bTwoResidual F β t u (g • u)
  let J' := R ⊓ Q F y
  have hnormal : K ≤ normalizer (R : Set (G₀ L S)) := by
    intro x hx
    exact (hKn hx).1.2
  have hdisj : Disjoint R (Q F y) := by
    apply disjoint_iff.mpr
    simpa only [J', R] using hzero
  have hcard : Nat.card R = Nat.card J := path_cartan_residual_card h hy
    (K := K) (R := R) hfix hd hgen ho g hR hRne hdisj hnormal ey
  exact ⟨J, inferInstance, inferInstance, inferInstance, g, hg, hgt, hcard⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource

