module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.TerminalImage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.NormalizerInputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Rigidity.Basic
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# Fixed natural lines on the actual MS93 edges

Conjugation transports the fixed subgroup of U_a under the odd edge kernel.
The terminal order-four pairing supplies one fixed line, and actual vertex
and neighbor transitivity transport its order two to every colored edge.
The line is relatively normal in the edge kernel. Relative normality in the
whole vertex stabilizer forces a line in Q into D; a nonzero line in U
cannot be normal in that stabilizer.

These are the genuine normalizer premises for the two simultaneous choices
at the end of (4.4.1), without asserting the remaining commutator identities.
Source: Meierfrankenfeld--Stellmacher (1993), printed p.892.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
open LocalCommutator LocalCommutator.CriticalCase
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

 omit [Finite M] in
 theorem fixed_line_act (g : FreeAmalgam R) (a t : Vertex R) :
    edgeFixedNatural (act R g a) (act R g t) =
      (edgeFixedNatural (R:=R) a t).map (MulAut.conj g⁻¹).toMonoidHom := by
  rw [edgeFixedNatural,edgeFixedNatural,Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,
    Theory.GroupTheory.map_centralizer_equiv,← U_act]
  change _ = U R (act R g a) ⊓ centralizer ((Q R t).map (MulAut.conj g⁻¹).toMonoidHom : Set (FreeAmalgam R))
  rw [← Q_act]

 theorem fixed_line_card_transport {c s : Vertex R} (hc : color R c=false)
    (hcs : Adjacent R c s) (hcard : Nat.card (edgeFixedNatural (R:=R) c s)=2)
    {a t : Vertex R} (ha : color R a=false) (hat : Adjacent R a t) :
    Nat.card (edgeFixedNatural (R:=R) a t)=2 := by
  obtain ⟨u,hu⟩ := exists_mVertex_of_color R hc
  obtain ⟨v,hv⟩ := exists_mVertex_of_color R ha
  let g := u⁻¹*v
  have hg : act R g c=a := by rw [hu,act_mVertex,mul_inv_cancel_left,← hv]
  have hadj : Adjacent R a (act R g s) := by
    rw [← hg]
    exact (adjacent_act_iff R g c s).mpr hcs
  obtain ⟨k,hk,hkt⟩ := stabilizer_transitive_neighbors R a hadj hat
  have hka : act R k a=a := hk
  have hcast : edgeFixedNatural (R:=R) a t =
      (edgeFixedNatural (R:=R) c s).map (MulAut.conj (g*k)⁻¹).toMonoidHom := by
    rw [← fixed_line_act]
    rw [act_mul R g k c,act_mul R g k s,hg,hka,hkt]
  rw [hcast,Subgroup.card_map_of_injective (MulAut.conj (g*k)⁻¹).injective,hcard]

 theorem fixed_line_card (common : CommonFacts R source geometry)
    (hb : 4<geometry.b R) {a c : Vertex R} (ha : color R a=false)
    (hd : (cosetGraph R).dist a c=2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) {d t : Vertex R} (hdc : color R d=false)
    (hdt : Adjacent R d t) : Nat.card (edgeFixedNatural (R:=R) d t)=2 := by
  have hfirst : Adjacent R c (w.path.walk.getVert 1) := by
    apply (cosetGraph_adj R _ _).mp
    apply w.path.walk.adj_snd
    intro hnil
    have hz := hnil.length_eq_zero
    have hb' := w.path.length_eq_b
    omega
  exact fixed_line_card_transport w.path.start_color hfirst
    (n.pairing common hb ha hd).2.2.2.2 hdc hdt

 omit [Finite M] in
 theorem fixed_line_edge (hb : 2<geometry.b R)
    {a t : Vertex R} (ha : color R a=false) (hat : Adjacent R a t) :
    edgeFixedNatural (R:=R) a t≤Q R t ∧
      ((edgeFixedNatural (R:=R) a t).subgroupOf (Q R t)).Normal := by
  have hZ : Z R a≤Q R t := by
    apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a ha)
    rw [geometry.distance_constant a ha,SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)]
    change 1<geometry.b R
    omega
  refine ⟨inf_le_left.trans ((U_le_Z R a).trans hZ),?_⟩
  apply normal_subgroupOf_of_le_normalizer
  exact (le_centralizer_iff.mp (show edgeFixedNatural (R:=R) a t≤centralizer (Q R t : Set (FreeAmalgam R)) from inf_le_right)).trans
    (Subgroup.centralizer_le_normalizer _)

 omit [Finite M] in
 theorem line_normal_implies_fixed {c : Vertex R} {F : Subgroup (FreeAmalgam R)}
    (hF : F≤Q R c) (hcard : Nat.card F=2)
    (hn : (F.subgroupOf (stabilizer R c)).Normal) : F≤fixedCore R c := by
  have hFS : F≤stabilizer R c := hF.trans (fun _ hx=>hx.1)
  have hnorm : stabilizer R c≤normalizer F :=
    (normal_subgroupOf_iff_le_normalizer hFS).mp hn
  have hcentral : F≤centralizer (stabilizer R c : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (hnorm.trans (normalizer_le_centralizer_of_card_two F hcard))
  exact le_inf hF (hcentral.trans (centralizer_le (Ltilde_le_stabilizer c)))

 theorem natural_line_not_normal (common : CommonFacts R source geometry)
    {c : Vertex R} (hc : color R c=false) {F : Subgroup (FreeAmalgam R)}
    (hFU : F≤U R c) (hcard : Nat.card F=2) :
    ¬(F.subgroupOf (stabilizer R c)).Normal := by
  intro hn
  have hFS : F≤stabilizer R c := hFU.trans ((U_le_Z R c).trans (Z_le_stabilizer R c))
  have hnorm : stabilizer R c≤normalizer F :=
    (normal_subgroupOf_iff_le_normalizer hFS).mp hn
  have hcentral : F≤centralizer (stabilizer R c : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (hnorm.trans (normalizer_le_centralizer_of_card_two F hcard))
  have hloc : F≤Escape.localCenter c := by
    rw [Escape.Propagation.Rigidity.localCenter_eq]
    exact le_inf hFS hcentral
  have hbot : F=⊥ := by
    apply le_bot_iff.mp
    rw [← Escape.Propagation.Rigidity.U_inf_localCenter_eq_bot (moduleFacts common) c hc]
    exact le_inf hFU hloc
  rw [hbot,card_bot] at hcard
  omega


omit [Finite M] in
 theorem fixed_line_le_common_Z (hb : 2<geometry.b R)
    {a c t : Vertex R} (ha : color R a=false) (hc : color R c=false)
    (hat : Adjacent R a t) (hct : Adjacent R c t) :
    edgeFixedNatural (R:=R) a t≤Z R c := by
  let := geometry.U_elementary (by omega) a ha
  have hFQ := (fixed_line_edge hb ha hat).1
  have hFO : edgeFixedNatural (R:=R) a t≤edgeOmega R t := by
    intro x hx
    exact mem_omegaCenter_iff.mpr ⟨hFQ hx,
      elemPow_eq_one_of_isElementaryAbelian x hx.1,fun y hy=>hx.2 y hy⟩
  apply hFO.trans
  rw [Z,if_pos hc]
  exact le_iSup_of_le t (le_iSup_of_le hct le_rfl)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
