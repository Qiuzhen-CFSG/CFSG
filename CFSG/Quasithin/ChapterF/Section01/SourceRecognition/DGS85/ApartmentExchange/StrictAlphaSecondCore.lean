module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoCentralApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.CriticalProfileCentral
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoResidualSeparation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SecondKernel

/-!
# The alpha second-kernel structure before exchange

The actual marked center action makes the intersection of two opposite
neighbor cores invariant under the intrinsic alpha actor. Its transitivity
on all neighbors identifies that intersection with the complete neighboring
core intersection, hence with the two-core of the full second ball kernel.
The original central-neighbor geometry makes this subgroup elementary
abelian; the alpha two-residual moves it only inside the literal alpha center.
No small-actor naturality or chosen kernel decomposition is assumed.

Source: DGS, Groups and Graphs (1985), (10.4), (10.8), and (14.9),
pp.155,159,215--216.
-/

public noncomputable section
open Subgroup
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction Noncommuting NoncommutingProfile CommutingOneProfile
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true

/-- The whole alpha second-kernel two-core is the actual elementary
intersection, and the intrinsic residual acts trivially modulo Z_alpha. -/
theorem source_bTwo_alpha_second_core_at
    (h : HypothesisF11 L S) {v m u t : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) v u)
    (hne : ⁅Z (reducedFamily L S) v,
      Z (reducedFamily L S) u⁆ ≠ ⊥)
    (hb : b (reducedFamily L S)=2)
    (hab : (graph (reducedFamily L S)).Adj v m)
    (hβu : (graph (reducedFamily L S)).Adj m u)
    (ht : (graph (reducedFamily L S)).Adj v t)
    (htne : t≠m) :
    neighborCoreIntersection F v=D F m t ∧
      (ballKernel F v 2).pCoreIn 2=D F m t ∧
      IsElementaryAbelian 2 (D F m t) ∧
      ⁅D F m t,(pResidual 2 (graphLocalGroup F v)).map (graphLocalGroup F v).subtype⁆≤Z F v := by
  let H := reduced_triple h
  let hS := reduced_kernel_sylow h
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hab hβu
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift H ht htne
  obtain ⟨d,hd,hker⟩ := c.exists_oppositeGeometry H hS hb g hg hop
  have hnorm : graphLocalGroup F v≤normalizer (D F m t : Set (G₀ L S)) := by
    have hh := d.normalized H hS hb
    change d.actor≤normalizer (D F m t : Set (G₀ L S)) at hh
    exact (hd.trans hactor) ▸ hh
  have hDI : D F m t≤neighborCoreIntersection F v := by
    apply le_iInf
    intro z x hx
    obtain ⟨a,ha,haz⟩ := graphLocalGroup_transitive H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) v ⟨m,hab⟩ z
    change a • m=z.val at haz
    have hxa : a⁻¹*x*a∈D F m t := by
      simpa only [inv_inv] using
        (mem_normalizer_iff.mp (hnorm ((graphLocalGroup F v).inv_mem ha)) x).mp hx
    have hh := mem_map_of_mem (MulAut.conj a).toMonoidHom hxa.1
    rw [←Q_translate,haz] at hh
    simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,mul_assoc,
      mul_inv_cancel_left,inv_mul_cancel,mul_inv_cancel,mul_one] using hh
  have hI : neighborCoreIntersection F v=D F m t := le_antisymm
    (le_inf (neighborCoreIntersection_le F hab.symm) (neighborCoreIntersection_le F ht.symm)) hDI
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hω := c.omega_eq_bot_of_central_neighbor H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hactor hcentral
  have hdis : Disjoint d.residual (Z F v) :=
    disjoint_iff.mpr (bot_unique (hker.trans hω.le))
  have hel := d.elementary H hS hb c.sylow (hd.symm ▸ c.sylow_le_actor) hdis
  have hmove := c.D_residual_commutator_le_center H hS hb ht htne
  rw [hactor] at hmove
  exact ⟨hI,(reduced_neighborCoreIntersection_eq_second_core h hab.symm).symm.trans hI,hel,hmove⟩


/-- The same full second-kernel identification at the original based alpha. -/
theorem source_bTwo_alpha_second_core
    (h : HypothesisF11 L S) {u t : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
    (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
      Z (reducedFamily L S) u⁆ ≠ ⊥)
    (hb : b (reducedFamily L S)=2)
    (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
    (ht : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) false) t)
    (htne : t≠base (reducedFamily L S) true) :
    neighborCoreIntersection F α=D F β t ∧
      (ballKernel F α 2).pCoreIn 2=D F β t ∧
      IsElementaryAbelian 2 (D F β t) ∧
      ⁅D F β t,(pResidual 2 (graphLocalGroup F α)).map (graphLocalGroup F α).subtype⁆≤Z F α := by
  exact source_bTwo_alpha_second_core_at h hc hne hb
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩ hβu ht htne

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
