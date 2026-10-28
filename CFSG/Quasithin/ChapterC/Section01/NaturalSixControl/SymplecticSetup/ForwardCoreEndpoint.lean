module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardCoreImage
/-!
# Endpoint action on the component commutator of the kernel

For a critical path of length four whose endpoints are conjugate in the
middle stabilizer, the middle Baumann slice of the endpoint lies in the
product of the starting and middle seeds. The component and the first edge
kernel normalize that product; their generation of the middle stabilizer
is the reason the endpoint orbit hypothesis suffices.

An endpoint moving-layer Baumann index at most two then identifies this
slice with the fixed hyperplane of the starting seed. The literal natural
point-core fixer calculation places the common-kernel part of the residual
in the endpoint kernel times the starting seed. Its endpoint commutator
therefore lies in the starting moving layer. The existing residual index
bound supplies an index-two subgroup with this action bound.

This is the source residual-action step in MS93 (3.10)(i), printed p.880,
used in the terminal (5.12) configuration. Endpoint conjugacy and the
opposite index remain explicit geometric inputs for the final assembly;
the SourceData consumer retains the actual characteristic replacement.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

private theorem normalizes_join_of_displacement {G : Type*} [Group G]
    (N H K : Subgroup G) (hn : K≤normalizer (N:Set G))
    (hcomm : ⁅K,H⁆≤N) : K≤normalizer ((N⊔H:Subgroup G):Set G) := by
  apply le_normalizer_iff.mpr
  intro k hk x hx
  have hm : (N⊔H).map (MulAut.conj k).toMonoidHom≤N⊔H := by
    rw [Subgroup.map_sup]
    refine sup_le ((mem_normalizer_iff_map_conj_eq.mp (hn hk)).le.trans le_sup_left) ?_
    rintro _ ⟨y,hy,rfl⟩
    have hh := (N⊔H).mul_mem
      (mem_sup_left (hcomm (commutator_mem_commutator hk hy))) (mem_sup_right hy)
    simpa [MulAut.conj_apply,commutatorElement_def,mul_assoc] using hh
  exact hm (mem_map_of_mem (MulAut.conj k).toMonoidHom hx)

private theorem commutator_sup_centralized_left {G : Type*} [Group G]
    (N U A : Subgroup G) (hUN : U ≤ normalizer (N : Set G))
    (hNA : N ≤ centralizer (A : Set G)) (hUA : U ≤ normalizer (A : Set G)) :
    ⁅N ⊔ U,A⁆ = ⁅U,A⁆ := by
  apply le_antisymm
  · apply commutator_le.mpr
    intro x hx a ha
    have hprod : x ∈ (N : Set G) * (U : Set G) :=
      (coe_mul_of_right_le_normalizer_left N U hUN) ▸ hx
    obtain ⟨n,hn,u,hu,rfl⟩ := hprod
    have he : ⁅n,a⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr (hNA hn a ha).symm
    have hmem : ⁅u,a⁆ ∈ A :=
      le_normalizer_iff_commutator_le_right.mp hUA (commutator_mem_commutator hu ha)
    rw [commutatorElement_mul_left_eq_conj_mul,he,mul_one,←hNA hn _ hmem,mul_inv_cancel_right]
    exact commutator_mem_commutator hu ha
  · exact commutator_mono le_sup_right le_rfl

private theorem relIndex_sup_of_normalized {G : Type*} [Group G]
    (B A : Subgroup G) (hn : A≤normalizer (B:Set G)) :
    B.relIndex (B⊔A)=B.relIndex A := by
  let J := B⊔A
  let : (B.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer (sup_le B.le_normalizer hn)
  have hi := relIndex_sup_left (A.subgroupOf J) (B.subgroupOf J)
  rw [←subgroupOf_sup le_sup_left le_sup_right,relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right] at hi
  exact hi

private theorem inf_eq_fixed_of_small_index {G : Type*} [Group G]
    (Z B A : Subgroup G) [Finite Z]
    (hBC : Z⊓B≤centralizer (A:Set G))
    (hne : ¬ Z≤centralizer (A:Set G)) (hi : B.relIndex Z≤2) :
    Z⊓B=Z⊓centralizer (A:Set G) := by
  let E := Z⊓B
  let F := Z⊓centralizer (A:Set G)
  have hEF : E≤F := le_inf inf_le_left hBC
  have hF : 1<F.relIndex Z := by
    have hp : 0<F.relIndex Z := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hn : F.relIndex Z≠1 := by
      intro he
      exact hne ((relIndex_eq_one.mp he).trans inf_le_right)
    omega
  have hm := relIndex_mul_relIndex E F Z hEF inf_le_left
  have hE : E.relIndex Z≤2 := by simpa only [E,inf_relIndex_left] using hi
  let : Finite F := Finite.of_injective (inclusion (show F≤Z from inf_le_left)) (inclusion_injective _)
  have hpEF : 0<E.relIndex F := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hEF1 : E.relIndex F=1 := by nlinarith
  exact le_antisymm hEF (relIndex_eq_one.mp hEF1)

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

/-- A seed orbit transports its Baumann slice inside the two-seed product. -/
theorem conjugate_seed_B_slice_le
    (hb : 2<s.geometry.b R) {a c t : Vertex R}
    (hc : color R c=false) (hat : Adjacent R a t) (hct : Adjacent R c t)
    (g : FreeAmalgam R) (hg : g∈stabilizer R c) :
    Z R (act R g a)⊓B R c (s.geometry.Z_normal _)≤Z R a⊔Z R c := by
  let D := Z R a⊓B R c (s.geometry.Z_normal _)
  let H := Z R c⊔D
  have hLc : Ltilde R c≤normalizer (H:Set (FreeAmalgam R)) := by
    apply normalizes_join_of_displacement
    · exact (Ltilde_le_stabilizer c).trans (Z_normalized R c)
    · apply commutator_le.mpr
      intro l hl d hd
      exact ((mem_B_iff R c _ ((s.geometry.V_le_Q hb c hc).trans (fun _ hx => hx.1)) d).mp hd.2).2 l hl
  have htGa : Q R t≤stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have htGc : Q R t≤stabilizer R c := fun _ hx => hx.2 _ (adjacent_symm R hct)
  have hBn := Escape.Propagation.Rigidity.B_normalized (geometry:=s.geometry) hb c hc
  have hD : Q R t≤normalizer (D:Set (FreeAmalgam R)) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq]
    dsimp only [D]
    rw [Subgroup.map_inf _ _ _ (MulAut.conj x).injective,
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized R a (htGa hx)),
      mem_normalizer_iff_map_conj_eq.mp (hBn (htGc hx))]
  have hGn : stabilizer R c≤normalizer (H:Set (FreeAmalgam R)) := by
    rw [←s.residual_edge_generation hc hct]
    exact sup_le hLc ((le_inf (htGc.trans (Z_normalized R c)) hD).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _))
  have hmap : D.map (MulAut.conj g⁻¹).toMonoidHom=
      Z R (act R g a)⊓B R c (s.geometry.Z_normal _) := by
    dsimp only [D]
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,←Z_act,
      MulEquiv.toMonoidHom_eq_coe,
      mem_normalizer_iff_map_conj_eq.mp (hBn ((stabilizer R c).inv_mem hg))]
  rw [←hmap]
  apply le_trans (map_mono (show D≤H from le_sup_right))
  rw [MulEquiv.toMonoidHom_eq_coe,mem_normalizer_iff_map_conj_eq.mp (hGn ((stabilizer R c).inv_mem hg))]
  exact sup_le le_sup_right (inf_le_left.trans le_sup_left)

/-- The common-kernel residual acts on the endpoint only through the starting moving layer. -/
theorem core_endpoint_commutator_le_moving_of_orbit
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (g : FreeAmalgam R) (hg : g∈stabilizer R (p.walk.getVert 2))
    (he : act R g (alpha R)=e)
    (hindex : (B R (p.walk.getVert 2) (s.geometry.Z_normal _)).relIndex (U R e)≤2) :
    ⁅⁅Q R (alpha R),Ltilde R (alpha R)⁆⊓Q R (p.walk.getVert 2),Z R e⁆≤U R (alpha R) := by
  let c := p.walk.getVert 2
  let D := ⁅Q R (alpha R),Ltilde R (alpha R)⁆⊓Q R c
  let Bc := B R c (s.geometry.Z_normal _)
  have hl : p.walk.length=4 := p.length_eq_b.trans hb
  have hb2 : 2<s.geometry.b R := by omega
  have hc : color R c=false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent R (alpha R) (p.walk.getVert 1) := by
    apply (cosetGraph_adj R _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) (by omega)
  have hct : Adjacent R c (p.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i:=1) (by omega)))
  have hce : (cosetGraph R).dist c e=2 := by
    simpa only [c,hl,Nat.reduceSub] using p.dist_end 2
  have hZeGc : Z R e≤stabilizer R c := Z_le_stabilizer_of_dist_le e _ (by
    rw [s.geometry.distance_constant e p.end_color,SimpleGraph.dist_comm,hce]
    change 2≤s.geometry.b R
    omega)
  have hBslice : Z R e⊓Bc≤Z R (alpha R)⊔Z R c := by
    rw [←he]
    exact s.conjugate_seed_B_slice_le hb2 hc hat hct g hg
  have hBC : Z R e⊓Bc≤centralizer (Z R (alpha R):Set (FreeAmalgam R)) := by
    apply le_centralizer_iff.mpr
    apply (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R (alpha R) rfl)).trans
    apply centralizer_le
    apply hBslice.trans (sup_le _ _)
    · exact (Z_le_VBall R (alpha R) 2).trans (s.geometry.V_le_Q hb2 _ rfl)
    · apply Z_le_Q_of_dist_lt R c (s.geometry.exists_critical c hc)
      rw [s.geometry.distance_constant c hc,SimpleGraph.dist_comm]
      change (cosetGraph R).dist (alpha R) (p.walk.getVert 2)<s.geometry.b R
      rw [p.dist_start (by omega)]
      omega
  have hedge := s.critical_last_edge_inputs hb2 p
  have hlastc : Adjacent R c (p.walk.getVert (p.walk.length-1)) := by
    simpa only [c,hl,Nat.reduceSub] using
      ((cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i:=2) (by omega)))
  have hseedB : Z R (p.walk.getVert (p.walk.length-1))≤Bc :=
    (adjacent_Z_le R hc hlastc).trans (Escape.EdgeTransfer.Z_le_B hb2 c hc)
  have hZeSup : Z R e≤Bc⊔U R e := by
    rw [s.Z_eq_moving_sup_edge_at h p.end_color hedge.1]
    exact sup_le le_sup_right (hseedB.trans le_sup_left)
  have hBn : stabilizer R c≤normalizer (Bc:Set (FreeAmalgam R)) :=
    Escape.Propagation.Rigidity.B_normalized hb2 c hc
  have hUG : U R e≤stabilizer R c := (DistanceEight.U_le_Z R e).trans hZeGc
  have hBG : Bc≤stabilizer R c := by
    intro x hx
    exact ((s.geometry.V_le_Q hb2 c hc).trans (fun _ hx => hx.1))
      (((mem_B_iff R c _ ((s.geometry.V_le_Q hb2 c hc).trans (fun _ hx => hx.1)) x).mp hx).1)
  let := finite_stabilizer R c
  let : Finite (Bc⊔U R e:Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion (sup_le hBG hUG)) (inclusion_injective _)
  let : Finite (Z R e) := Finite.of_injective (inclusion hZeGc) (inclusion_injective _)
  let : Finite (U R e) := Finite.of_injective (inclusion hUG) (inclusion_injective _)
  have hZi : Bc.relIndex (Z R e)≤2 := by
    calc
      _≤Bc.relIndex (Bc⊔U R e) := relIndex_le_of_le_right hZeSup index_ne_zero_of_finite
      _=Bc.relIndex (U R e) := relIndex_sup_of_normalized _ _ (hUG.trans hBn)
      _≤2 := hindex
  have hne : ¬ Z R e≤centralizer (Z R (alpha R):Set (FreeAmalgam R)) := by
    intro hn
    apply p.critical.2
    rw [←s.C_eq_Q e p.end_color]
    exact le_inf (Z_le_stabilizer_of_dist_le (alpha R) _ p.critical.1.le)
      (le_centralizer_iff.mp hn)
  have hfixeq := inf_eq_fixed_of_small_index (Z R e) Bc (Z R (alpha R)) hBC hne hZi
  have hfi : (centralizer (Z R (alpha R):Set (FreeAmalgam R))).relIndex (U R e)≤2 := by
    have hsup : Bc.relIndex (Z R e)=(centralizer (Z R (alpha R):Set (FreeAmalgam R))).relIndex (Z R e) := by
      rw [←inf_relIndex_left (Z R e) Bc,hfixeq,inf_relIndex_left]
    exact (relIndex_le_of_le_right (DistanceEight.U_le_Z R e) index_ne_zero_of_finite).trans (hsup ▸ hZi)
  have hsmall := (s.small_edge_fixed_at h u (by
    simpa only [Model.pointCore_eq_exceptional] using hfull) p.end_color hedge.1
    (Z R (alpha R)) hedge.2.2 p.critical.2 hfi).2
  have hDa : D≤Q R (alpha R) := inf_le_left.trans
    ((s.core_commutator_le_forward_hyperplane_kernel u hfull hb2 p).trans inf_le_left)
  have hDC : D≤centralizer ((Z R (alpha R)⊔Z R c:Subgroup (FreeAmalgam R)):Set (FreeAmalgam R)) := by
    apply le_centralizer_iff.mpr
    exact sup_le
      ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R (alpha R) rfl)).trans
        (centralizer_le hDa))
      ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R c hc)).trans
        (centralizer_le (show D≤Q R c from inf_le_right)))
  have hDe : D≤Q R e⊔Z R (alpha R) := by
    apply (le_inf _ _).trans hsmall
    · have hDc : D≤Q R (p.walk.getVert (p.walk.length-2)) := by
        simpa only [hl,Nat.reduceSub,c] using (inf_le_right : D≤Q R c)
      exact hDc.trans hedge.2.1
    · change D≤centralizer ((Z R e⊓centralizer (Z R (alpha R):Set (FreeAmalgam R)):
        Subgroup (FreeAmalgam R)):Set (FreeAmalgam R))
      rw [←hfixeq]
      exact hDC.trans (centralizer_le hBslice)
  have hZaGe : Z R (alpha R)≤stabilizer R e :=
    Z_le_stabilizer_of_dist_le (alpha R) _ p.critical.1.le
  have hQe : Q R e≤centralizer (Z R e:Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R e p.end_color))
  have heq := commutator_sup_centralized_left (Q R e) (Z R (alpha R)) (Z R e)
    (hZaGe.trans (Q_normalized R e)) hQe (hZaGe.trans (Z_normalized R e))
  exact ((commutator_mono hDe le_rfl).trans_eq heq).trans
    ((s.critical_Z_commutator_le_moving p).trans inf_le_left)
/-- The actual residual has an index-at-most-two subgroup with controlled endpoint action. -/
theorem core_endpoint_small_action_of_orbit
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (g : FreeAmalgam R) (hg : g∈stabilizer R (p.walk.getVert 2))
    (he : act R g (alpha R)=e)
    (hindex : (B R (p.walk.getVert 2) (s.geometry.Z_normal _)).relIndex (U R e)≤2) :
    let Q₀ := ⁅Q R (alpha R),Ltilde R (alpha R)⁆
    let D := Q₀⊓Q R (p.walk.getVert 2)
    D.relIndex Q₀≤2 ∧ ⁅D,Z R e⁆≤U R (alpha R) := by
  refine ⟨?_,s.core_endpoint_commutator_le_moving_of_orbit h u hfull hb p g hg he hindex⟩
  simpa only [inf_relIndex_left] using s.core_commutator_second_vertex_index_le_two h u hfull hb p
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K] {L W : Subgroup K} [L.Normal] [W.Normal]
  {T : Sylow 2 K} (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L⊔d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

/-- The selected endpoint data give the residual-action bound in the literal replacement. -/
theorem reducedSource_block_or_core_endpoint_small_action
    (r : CharacteristicReduction (L.subgroupOf J) R) {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e)
    (hb : ((originalSource d hm).reduce r).geometry.b r.radical=4)
    (g : FreeAmalgam r.radical) (hg : g∈stabilizer r.radical (p.walk.getVert 2))
    (he : act r.radical g (alpha r.radical)=e)
    (hindex : (B r.radical (p.walk.getVert 2)
      (((originalSource d hm).reduce r).geometry.Z_normal _)).relIndex (U r.radical e)≤2) :
    IsAlternatingBlock L 6 ∨
      let Q₀ := ⁅Q r.radical (alpha r.radical),Ltilde r.radical (alpha r.radical)⁆
      let D := Q₀⊓Q r.radical (p.walk.getVert 2)
      D.relIndex Q₀≤2 ∧ ⁅D,Z r.radical e⁆≤U r.radical (alpha r.radical) := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock|hfull
  · exact Or.inl hblock
  · right
    let s := (originalSource d hm).reduce r
    have hf : r.radical.map s.projection=Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    exact s.core_endpoint_small_action_of_orbit (reduced_nativeCentralLayer d hm r) _ hf hb p g hg he hindex
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
