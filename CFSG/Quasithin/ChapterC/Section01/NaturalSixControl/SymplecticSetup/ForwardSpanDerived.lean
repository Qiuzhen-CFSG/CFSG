module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardSpanAll
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.SelectedForwardIndex
public import Theory.GroupTheory.ClassTwoCommutator
/-!
# The terminal normal span is a nonabelian central extension

At critical distance four the forward moving layer has Baumann index two.
Its conjugate Z-span P lies in the normal hyperplane kernel T. The forward
span calculation gives [P,T] inside the central line H=[U,T], hence P' lies
in H. A prescribed backward critical pair consists of two layers in P, so
P' is nontrivial. The order-two bound therefore gives P'=H. In particular
P' is centralized by the entire starting stabilizer and lies in its Z-layer.

The intrinsic derived subgroup has order two and is central. Commutator rows
then show that every square is central, making P/Z(P) elementary abelian.
Radius centrality places [P,Q_alpha] in Z(P), so the starting kernel acts
trivially on this literal central quotient. These are the group inputs to
the terminal representation argument; no natural-module recognition is
assumed or asserted here. The SourceData consumer uses its actual
characteristic replacement and retains only the alternating-block case.

Source: Meierfrankenfeld--Stellmacher (1993), the terminal paragraph of
(5.12), printed p.927, and the central-extension calculation in (3.10),
printed pp.879--881, specialized to the native full point-core branch.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
private theorem elementary_central_quotient_of_derived_card_two
    {G : Type*} [Group G]
    (hc : _root_.commutator G≤center G) (hcard : Nat.card (_root_.commutator G)=2) :
    IsElementaryAbelian 2 (G⧸center G) := by
  let : Finite (_root_.commutator G) := Nat.finite_of_card_ne_zero (by omega)
  have hsquare (x y : G) : ⁅x,y⁆^2=1 := by
    have hh := pow_card_eq_one' (x:=(⟨⁅x,y⁆,commutator_mem_commutator (mem_top _) (mem_top _)⟩:
      _root_.commutator G))
    rw [hcard] at hh
    exact congrArg Subtype.val hh
  have hpow (x : G) : x^2∈center G := by
    apply mem_center_iff.mpr
    intro y
    apply commutatorElement_eq_one_iff_mul_comm.mp
    have hh := map_pow (ClassTwo.commutatorHom hc y) x 2
    change ⁅y,x^2⁆=⁅y,x⁆^2 at hh
    exact hh.trans (hsquare y x)
  have hqpow (x : G⧸center G) : x^2=1 := by
    induction x using QuotientGroup.induction_on with
    | H x =>
      rw [←QuotientGroup.mk_pow,QuotientGroup.eq_one_iff]
      exact hpow x
  exact {
    toIsMulCommutative := ⟨⟨fun x y =>
      (Commute.of_orderOf_dvd_two (fun z => orderOf_dvd_of_pow_eq_one (hqpow z)) x y).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hqpow }

open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

/-- The normal forward span lies in its hyperplane kernel. -/
theorem forward_span_le_hyperplane_kernel
    (hb : 2<s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    localZSpan R (p.walk.getVert 2) (alpha R) ≤ Q R (alpha R)⊓centralizer
      (U R (p.walk.getVert 2)⊓B R (alpha R) (s.geometry.Z_normal _):Set (FreeAmalgam R)) := by
  let T₀ := Q R (alpha R)⊓centralizer
    (U R (p.walk.getVert 2)⊓B R (alpha R) (s.geometry.Z_normal _):Set (FreeAmalgam R))
  have hl := p.length_eq_b
  have hc : color R (p.walk.getVert 2)=false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent R (alpha R) (p.walk.getVert 1) := by
    apply (cosetGraph_adj R _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) (by omega)
  have hct : Adjacent R (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i:=1) (by omega)))
  have hZT : Z R (p.walk.getVert 2)≤T₀ := by
    apply le_inf
    · apply Z_le_Q_of_dist_lt R _ (s.geometry.exists_critical _ hc)
      rw [s.geometry.distance_constant _ hc,SimpleGraph.dist_comm,p.dist_start (by omega)]
      exact hb
    · let := s.geometry.Z_elementary s.criticalDistance_pos _ hc
      exact (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
        (centralizer_le (inf_le_left.trans (DistanceEight.U_le_Z R _)))
  have hn := s.moving_hyperplane_kernel_normalized hb rfl hat hct
  rw [localZSpan_eq_conjugates]
  apply iSup_le
  intro g
  rintro _ ⟨z,hz,rfl⟩
  exact (mem_normalizer_iff.mp (hn ((stabilizer R (alpha R)).inv_mem g.property)) z).mp (hZT hz)

/-- The distance-four normal span has exactly the forward central line as its derived subgroup. -/
theorem forward_span_derived_eq_line
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    let P := localZSpan R (p.walk.getVert 2) (alpha R)
    let T₀ := Q R (alpha R)⊓centralizer
      (U R (p.walk.getVert 2)⊓B R (alpha R) (s.geometry.Z_normal _):Set (FreeAmalgam R))
    ⁅P,P⁆=⁅U R (p.walk.getVert 2),T₀⁆ ∧
      Nat.card (⁅P,P⁆:Subgroup (FreeAmalgam R))=2 ∧
      ⁅P,P⁆≤centralizer (stabilizer R (alpha R):Set (FreeAmalgam R)) ∧
      ⁅P,P⁆≤Z R (alpha R) := by
  let P := localZSpan R (p.walk.getVert 2) (alpha R)
  let T₀ := Q R (alpha R)⊓centralizer
    (U R (p.walk.getVert 2)⊓B R (alpha R) (s.geometry.Z_normal _):Set (FreeAmalgam R))
  let H := ⁅U R (p.walk.getVert 2),T₀⁆
  have hl : p.walk.length=4 := p.length_eq_b.trans hb
  have hb2 : 2<s.geometry.b R := by omega
  have hc : color R (p.walk.getVert 2)=false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent R (alpha R) (p.walk.getVert 1) := by
    apply (cosetGraph_adj R _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) (by omega)
  have hct : Adjacent R (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i:=1) (by omega)))
  have hi := s.forward_moving_index_eq_two_of_distance_four h u hfull hb p
  have hspan := s.critical_forward_span_commutator_le_line_of_two_lt h u hfull hb2 p hi.le
  have hPT : P≤T₀ := s.forward_span_le_hyperplane_kernel hb2 p
  have hder : ⁅P,P⁆≤H := (commutator_mono le_rfl hPT).trans hspan.2
  have hHcard : Nat.card H≤2 :=
    (s.moving_hyperplane_commutator_le_seed h u hfull rfl hc hat hct hi.le).1
  have hHU : H≤U R (p.walk.getVert 2) := by
    have ht : color R (p.walk.getVert 1)=true := by
      have hn := adjacent_color_ne R hat
      change false≠color R (p.walk.getVert 1) at hn
      cases hh:color R (p.walk.getVert 1) <;> simp_all
    have hTG : T₀≤stabilizer R (p.walk.getVert 2) :=
      (inf_le_left.trans (Q_le_adjacent_h R ht hat)).trans
        (fun _ hx => hx.2 _ (adjacent_symm R hct))
    exact le_normalizer_iff_commutator_le_left.mp (hTG.trans (U_normalized _))
  let := finite_Z R (p.walk.getVert 2)
  let : Finite H := Finite.of_injective
    (inclusion (hHU.trans (DistanceEight.U_le_Z R _))) (inclusion_injective _)
  let : Finite (⁅P,P⁆:Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hder) (inclusion_injective _)
  obtain ⟨c⟩ := s.exists_coordinatedChoice h u hfull p _ hct
  obtain ⟨q,_,_,_⟩ := c.exists_prescribed_backward_path s h u hfull hb2
  have hZm : Z R c.alpha1≤P := by
    rw [c.alpha1_eq,Z_act]
    dsimp only [P]
    rw [localZSpan_eq_conjugates]
    exact le_iSup (fun g : stabilizer R (alpha R) =>
      (Z R (p.walk.getVert 2)).map (MulAut.conj (g:FreeAmalgam R)⁻¹).toMonoidHom)
      ⟨c.transporter,c.transporter_mem⟩
  have hZc : Z R (p.walk.getVert (p.walk.length-2))≤P := by
    simpa only [hl,Nat.reduceSub] using Z_le_localZSpan R (p.walk.getVert 2) (alpha R)
  have hne : ⁅P,P⁆≠⊥ := by
    intro hz
    apply q.critical.2
    rw [←s.C_eq_Q _ q.end_color]
    refine le_inf (Z_le_stabilizer_of_dist_le c.alpha1 _ q.critical.1.le) ?_
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    exact (commutator_mono hZm hZc).trans_eq hz
  have hcard := (one_lt_card_iff_ne_bot (⁅P,P⁆:Subgroup (FreeAmalgam R))).mpr hne
  have hPP : ⁅P,P⁆=H := eq_of_le_of_card_ge hder (by omega)
  refine ⟨hPP,?_,hder.trans hspan.1,?_⟩
  · change Nat.card (⁅P,P⁆:Subgroup (FreeAmalgam R))=2
    have hu := (card_le_of_le hder).trans hHcard
    omega
  · exact hder.trans (((s.moving_hyperplane_commutator_le_seed h u hfull rfl hc hat hct hi.le).2).trans
      (adjacent_Z_le R rfl hat))
/-- The terminal span is a nonabelian central extension of an elementary
binary group; the whole starting kernel acts trivially on its central quotient. -/
theorem forward_span_central_quotient
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    let P := localZSpan R (p.walk.getVert 2) (alpha R)
    IsElementaryAbelian 2 (P⧸center P) ∧
      Nat.card (_root_.commutator P)=2 ∧ _root_.commutator P≤center P ∧
      ⁅P,Q R (alpha R)⁆≤(center P).map P.subtype := by
  let P := localZSpan R (p.walk.getVert 2) (alpha R)
  have hb2 : 2<s.geometry.b R := by omega
  have hPV : P≤V R (alpha R) := localZSpan_le_V R (by
    rw [SimpleGraph.dist_comm,p.dist_start (by have hl := p.length_eq_b; omega)])
  have hPG : P≤stabilizer R (alpha R) := hPV.trans (s.geometry.V_local (alpha R) rfl hb2)
  have hd := s.forward_span_derived_eq_line h u hfull hb p
  have hcard : Nat.card (_root_.commutator P)=2 := by
    rw [←card_map_of_injective (f:=P.subtype) Subtype.val_injective,P.map_subtype_commutator]
    exact hd.2.1
  have hcent : _root_.commutator P≤center P := by
    intro z hz
    apply mem_center_iff.mpr
    intro w
    apply Subtype.ext
    apply hd.2.2.1
    · rw [←P.map_subtype_commutator]
      exact mem_map_of_mem P.subtype hz
    · exact hPG w.property
  refine ⟨elementary_central_quotient_of_derived_card_two hcent hcard,hcard,hcent,?_⟩
  have hPQ : ⁅P,Q R (alpha R)⁆≤P := le_normalizer_iff_commutator_le_left.mp
    ((show Q R (alpha R)≤stabilizer R (alpha R) from fun _ hx => hx.1).trans
      (localZSpan_normalized R _ _))
  have hpnt : R.map s.projection≤Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
      (MulAut.conj u).toMonoidHom := by
    simpa only [Model.pointCore_eq_exceptional] using hfull.le
  have hPC : ⁅P,Q R (alpha R)⁆≤centralizer (P:Set (FreeAmalgam R)) :=
    ((commutator_mono hPV le_rfl).trans
      (s.radius_commutator_central_of_two_lt h u hpnt hb2)).trans (centralizer_le hPV)
  intro z hz
  refine ⟨⟨z,hPQ hz⟩,?_,rfl⟩
  apply mem_center_iff.mpr
  intro w
  exact Subtype.ext (hPC hz w w.property)
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source


namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K] {L W : Subgroup K} [L.Normal] [W.Normal]
  {T : Sylow 2 K} (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L⊔d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

/-- The actual characteristic replacement supplies the terminal nonabelian
central extension and its trivial kernel action. -/
theorem reducedSource_block_or_forward_span_central_quotient
    (r : CharacteristicReduction (L.subgroupOf J) R) {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e)
    (hb : ((originalSource d hm).reduce r).geometry.b r.radical=4) :
    IsAlternatingBlock L 6 ∨
      (let P := localZSpan r.radical (p.walk.getVert 2) (alpha r.radical)
       Nat.card (⁅P,P⁆:Subgroup (FreeAmalgam r.radical))=2 ∧
       ⁅P,P⁆≤centralizer (stabilizer r.radical (alpha r.radical):Set (FreeAmalgam r.radical)) ∧
       ⁅P,P⁆≤Z r.radical (alpha r.radical) ∧
       IsElementaryAbelian 2 (P⧸center P) ∧
       Nat.card (_root_.commutator P)=2 ∧ _root_.commutator P≤center P ∧
       ⁅P,Q r.radical (alpha r.radical)⁆≤(center P).map P.subtype) := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock|hfull
  · exact Or.inl hblock
  · right
    let s := (originalSource d hm).reduce r
    have hf : r.radical.map s.projection=Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    have h := reduced_nativeCentralLayer d hm r
    have hd := s.forward_span_derived_eq_line h _ hf hb p
    exact ⟨hd.2.1,hd.2.2.1,hd.2.2.2,s.forward_span_central_quotient h _ hf hb p⟩
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
