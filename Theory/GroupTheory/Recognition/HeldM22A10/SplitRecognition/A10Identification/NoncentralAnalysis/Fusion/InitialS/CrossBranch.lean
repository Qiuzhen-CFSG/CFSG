module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.InitialS.WeakClosure
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.InitialS.CrossBranch.Overgroup
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.InitialS.CrossBranch.FiveFusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.InitialS.CrossBranch.Endgame

/-!
# The cross-fusion branch of Held's Lemma 2.9

Under the contrary initial-S-fusion assumptions, pi cannot be conjugate to
 tau*lambda*xi when both xi choices are separated. Cross fusion enlarges the
normalizer of L2 beyond a two-group. Its order-five action forces mu to be
conjugate to tau*lambda. Weak closure of S and its two-group normalizer exclude
that fusion by comparing centralizers of orders 64 and 32.

Every auxiliary normalizer, action and weak-closure premise is discharged from
the displayed local data and the stated nonfusions.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240, Lemma 2.9,
printed p.230, DOI 10.1215/ijm/1256053756.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.InitialS
open Coordinates
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- The cross representative cannot fuse with pi under the contrary
initial-S-fusion hypotheses and separation of both xi choices. -/
public theorem cross_nonfusion (h : Separated D e)
    (hxi : ¬ IsConj D.z (D.a10ModelEmbedding e xi))
    (hpiXi : ¬ IsConj D.z (D.a10ModelEmbedding e (pi * xi))) :
    ¬ IsConj D.z (D.a10ModelEmbedding e (tau * lam * xi)) := by
  intro hcross
  have hN := cross_normalizer_not_isPGroup D e h.1 hcross
  have hf := CrossBranch.mu_isConj_tau_mul_lam_of_l2_not_two D e
    h.1 h.2.1 h.2.2.1 h.2.2.2 hxi hpiXi hcross hN
  have htwo : IsPGroup 2 (normalizer (ambientElementary D e 1 : Set G)) := by
    rw [normalizer_S_eq D e h]
    exact (ambientSylow D e).isPGroup'
  exact mu_tauLambda_nonfusion_of_weak_closure D e htwo (S_weakly_closed D e h) hf

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.InitialS
