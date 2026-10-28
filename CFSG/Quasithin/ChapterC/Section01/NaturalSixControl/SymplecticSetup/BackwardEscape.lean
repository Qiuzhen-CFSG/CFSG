module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.BackwardFixedLine

public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.EdgeCentrality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Factorization.Extensions

/-!
# Unconditional backward escape for the original symplectic source

The binary point radical centralizes each commutator of order at most two.
In the small critical-image branch, the critical commutator therefore lies
in the first edge seed. The selected backward commutator is also centralized
by its selected edge radical. The recorded seed-fixer condition puts it in
the stabilizer center, whose intersection with the natural moving layer is
trivial. Its centralizer then lies in B, contradicting the selected moving
neighbor. This sharpens the conditional backward result to every eligible
choice, preserving the actual coordinated vertex.

A neighboring moving layer exists because containment of the whole radius
in B would produce a nontrivial subgroup normal in both adjacent stabilizers.
Thus backward escape is unconditional. Its literal universal form supplies
MS93 2.2(v), and reverse nonnormality gives the forward moving-layer index
at least two. The characteristic-replacement application uses the original
source coordinates and discharges the full point-core marking.

Source: Meierfrankenfeld--Stellmacher (1993), (5.8), printed pp.919--920,
with (2.2)(v), printed pp.856--857; Aschbacher--Smith C.1.37 and 13.7.4(1).
The subsequent critical-distance and core-identification steps remain separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

/-- The source radius is not fixed modulo its central layer. -/
theorem radius_not_le_B (hb : 2 < s.geometry.b R) :
    ¬ V R (alpha R) ≤ B R (alpha R) (s.geometry.Z_normal _) := by
  intro hVB
  have hVL := s.geometry.V_local (alpha R) rfl hb
  have hcomm : ⁅V R (alpha R),Ltilde R (alpha R)⁆ ≤ Z R (alpha R) := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl v hv
    exact ((mem_B_iff R _ _ hVL v).mp (hVB hv)).2 l hl
  have hcover := map_mono (f := embedM R) (s.radius_comap_le_edge_sup_commutator hb)
  rw [Subgroup.map_sup,map_commutator,s.radius_comap_map hb,s.edge_radius_comap_map hb,
    show L.map (embedM R) = Ltilde R (alpha R) by rw [Ltilde_alpha,s.residual]] at hcover
  have hZE : Z R (alpha R) ≤ V R (beta R) := by
    apply le_iSup_of_le (alpha R)
    exact le_iSup_of_le (show (cosetGraph R).dist (alpha R) (beta R) ≤ 2 from
      (SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr (base_adjacent R))).le.trans (by decide)) le_rfl
  have hVE : V R (alpha R) ≤ V R (beta R) :=
    hcover.trans (sup_le le_rfl (hcomm.trans hZE))
  have hEV : V R (beta R) ≤ V R (alpha R) := edge_radius_le_radius rfl (base_adjacent R)
  have hEeq := le_antisymm hEV hVE
  have hEQ : V R (beta R) ≤ Q R (alpha R) := hEV.trans (s.geometry.V_le_Q hb _ rfl)
  have hES : V R (beta R) ≤ stabilizer R (alpha R) ⊓ stabilizer R (beta R) :=
    le_inf (hEQ.trans (fun _ hx => hx.1))
      (hEQ.trans (fun _ hx => hx.2 _ (base_adjacent R)))
  have hbot := no_common_normal_at_edge R s.characteristic _ _ rfl (base_adjacent R)
    (V R (beta R)) hES
    (normal_subgroupOf_of_le_normalizer (by rw [hEeq]; exact DistanceEight.V_normalized R _))
    (normal_subgroupOf_of_le_normalizer (DistanceEight.V_normalized R _))
  have hw : embedM R (s.w : M) ∈ Z R (alpha R) :=
    s.module_le_Z (mem_map_of_mem (embedM R) s.w.property)
  have hzero : embedM R (s.w : M) = 1 := mem_bot.mp (hbot ▸ hZE hw)
  have hw1 : (s.w : M) = 1 := (embedM_injective R) (by simpa only [map_one] using hzero)
  exact s.w_ne (Subtype.ext hw1)

/-- The radius noncontainment at every original-group vertex. -/
theorem radius_not_le_B_at (hb : 2 < s.geometry.b R) {a : Vertex R}
    (ha : color R a = false) : ¬ V R a ≤ B R a (s.geometry.Z_normal _) := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color R ha
  have he : act R g (alpha R) = mVertex R g := by simp only [alpha,act_mVertex,one_mul]
  rw [←he,V_act,Escape.PairingControl.FirstPairing.B_act hb g (alpha R) rfl,
    map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective]
  exact s.radius_not_le_B hb

/-- The natural moving layer and edge seed generate the actual Z-layer. -/
theorem Z_eq_moving_sup_edge_at (h : NativeCentralLayer s)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t) :
    Z R a = U R a ⊔ Z R t := by
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common R a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom)
      (s.Z_eq_moving_sup_edge h)
    rw [Subgroup.map_sup,←Z_act,←U_act,←Z_act] at he
    simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using he
  · rw [hg.1] at ha
    cases ha

/-- Every oriented source edge has a neighboring moving layer outside B. -/
theorem exists_moving_neighbor_at_edge (h : NativeCentralLayer s)
    (hb : 2 < s.geometry.b R) {a t : Vertex R}
    (ha : color R a = false) (hat : Adjacent R a t) :
    ∃ d, Adjacent R d t ∧ ¬ U R d ≤ B R a (s.geometry.Z_normal _) := by
  by_contra! hn
  apply s.radius_not_le_B_at hb ha
  apply radius_le_of_normalized_edge ha hat _ _
    (Escape.Propagation.Rigidity.B_normalized hb a ha)
  apply radius_le_of_h_neighbors ha hat
  intro d hdt
  have hd : color R d = false := by
    have h1 := adjacent_color_ne R hat
    have h2 := adjacent_color_ne R hdt
    rw [ha] at h1
    cases hc : color R d <;> cases ht : color R t <;> simp_all
  rw [s.Z_eq_moving_sup_edge_at h hd hdt]
  refine sup_le (hn d hdt) ?_
  exact (adjacent_Z_le R ha hat).trans (Escape.EdgeTransfer.Z_le_B hb a ha)


include s in
/-- The actual residual and incident edge kernel generate the vertex stabilizer. -/
theorem residual_edge_generation {c t : Vertex R}
    (hc : color R c = false) (hct : Adjacent R c t) :
    Ltilde R c ⊔ Q R t = stabilizer R c := by
  have hbase : Ltilde R (alpha R) ⊔ Q R (beta R) = stabilizer R (alpha R) := by
    rw [Ltilde_alpha,s.residual,Q_beta,←Subgroup.map_sup,s.sup_eq_top]
    exact (MonoidHom.range_eq_map (embedM R)).symm.trans (stabilizer_m_base R).symm
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common R c t).mp hct
  · rcases hg with ⟨rfl,rfl⟩
    have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hbase
    rw [Subgroup.map_sup,←Ltilde_act,←Q_act,←stabilizer_act] at he
    simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using he
  · rw [hg.1] at hc
    cases hc

private theorem normalizes_join_of_displacement {G : Type*} [Group G]
    (N H K : Subgroup G) (hn : K ≤ normalizer (N : Set G))
    (hcomm : ⁅K,H⁆ ≤ N) : K ≤ normalizer ((N ⊔ H : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro k hk x hx
  have hm : (N ⊔ H).map (MulAut.conj k).toMonoidHom ≤ N ⊔ H := by
    rw [Subgroup.map_sup]
    refine sup_le ((mem_normalizer_iff_map_conj_eq.mp (hn hk)).le.trans le_sup_left) ?_
    rintro _ ⟨y,hy,rfl⟩
    have hh := (N ⊔ H).mul_mem
      (mem_sup_left (hcomm (commutator_mem_commutator hk hy))) (mem_sup_right hy)
    simpa [MulAut.conj_apply,commutatorElement_def,mul_assoc] using hh
  exact hm (mem_map_of_mem (MulAut.conj k).toMonoidHom hx)


/-- In the binary small-image branch the critical line lies in the first edge seed. -/
theorem small_critical_commutator_le_first_seed
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    {e : Vertex R} (p : CriticalPath R s.geometry (alpha R) e)
    (hsmall : (Q R e).relIndex (Z R (alpha R)) < 4) :
    ⁅Z R (alpha R),Z R e⁆ ≤ Z R (p.walk.getVert 1) := by
  have hpos : 0 < p.walk.length := p.length_eq_b ▸ s.criticalDistance_pos
  have hat : Adjacent R (alpha R) (p.walk.getVert 1) := by
    apply (cosetGraph_adj R _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) hpos
  have ht : color R (p.walk.getVert 1) = true := by
    have hn := adjacent_color_ne R hat
    change false ≠ color R (p.walk.getVert 1) at hn
    cases hc : color R (p.walk.getVert 1) <;> simp_all
  have hZe : Z R e ≤ Q R (p.walk.getVert 1) := by
    apply Z_le_Q_of_dist_lt R e (s.geometry.exists_critical e p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,s.geometry.distance_constant e p.end_color]
    change p.walk.length - 1 < s.geometry.b R
    rw [←p.length_eq_b]
    omega
  have hRZ : ⁅Z R (alpha R),Z R e⁆ ≤ Z R (alpha R) :=
    ((s.critical_Z_commutator_le_moving p).trans inf_le_left).trans (DistanceEight.U_le_Z R _)
  have hRQ : ⁅Z R (alpha R),Z R e⁆ ≤ Q R (p.walk.getVert 1) :=
    (hRZ.trans (s.Z_le_X.trans (omegaCenter_le _))).trans (Q_le_adjacent_h R ht hat)
  have hRC := s.small_edge_commutator_le_centralizer u hfull rfl hat (Z R e) hZe (s.small_critical_commutator_card h p hsmall).le
  let := s.geometry.Z_elementary s.criticalDistance_pos (alpha R) rfl
  intro x hx
  rw [Z,if_neg (by rw [ht]; decide)]
  exact mem_omegaCenter_iff.mpr ⟨hRQ hx,elemPow_eq_one_of_isElementaryAbelian x (hRZ hx),hRC hx⟩

/-- The selected backward layer escapes under the original eligibility condition. -/
theorem CoordinatedChoice.small_backward_not_le_of_eligible
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {e : Vertex R}
    {p : CriticalPath R s.geometry (alpha R) e} {delta : Vertex R}
    (c : s.CoordinatedChoice p delta)
    (hindex : 1 < (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R delta))
    (hsmall : (Q R e).relIndex (Z R (alpha R)) < 4) :
    ¬ Z R c.alpha1 ≤ Q R (p.walk.getVert (p.walk.length-2)) := by
  intro hbad
  let K := Z R e ⊓ Q R (alpha R)
  have hKfixed : K = Z R e ⊓ centralizer (Z R (alpha R) : Set (FreeAmalgam R)) :=
    s.critical_kernel_eq_fixed p
  have hpoint : R.map s.projection =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom := by
    simpa only [Model.pointCore_eq_exceptional] using hfull
  have hedge := s.critical_last_edge_inputs hb p
  have hfixed := s.small_edge_fixed_at h u hpoint p.end_color hedge.1
    (Z R (alpha R)) hedge.2.2 p.critical.2 (s.small_critical_fixedIndex_le_two h p hsmall)
  change _ ∧ _ at hfixed
  rw [←hKfixed] at hfixed
  have hfixed2 : Q R (p.walk.getVert (p.walk.length-1)) ⊓ centralizer (K : Set (FreeAmalgam R)) ≤ Q R e ⊔ Z R (alpha R) := by
    simpa only [hKfixed,Subgroup.coe_inf,Set.inf_eq_inter] using hfixed.2
  have hYt : Z R c.alpha1 ≤ Q R (p.walk.getVert (p.walk.length-1)) := hbad.trans hedge.2.1
  have hK : K ≤ Q R c.beta1 := inf_le_right.trans
    (Q_le_adjacent_h R c.edge_color c.adjacent_start)
  have hcomm : ⁅U R e,Z R (alpha R)⁆ ≤ ⁅Z R (alpha R),Z R e⁆ := by
    rw [commutator_comm]
    exact commutator_mono le_rfl (DistanceEight.U_le_Z R e)
  have hR1 : ⁅Z R c.alpha1,K⁆ ≤ ⁅Z R (alpha R),Z R e⁆ := by
    rw [commutator_comm]
    exact ((commutator_mono le_rfl hYt).trans hfixed.1).trans hcomm
  have hcritical_le : ⁅Z R (alpha R),Z R e⁆ ≤ Z R (alpha R) :=
    ((s.critical_Z_commutator_le_moving p).trans inf_le_left).trans (DistanceEight.U_le_Z R _)
  let := finite_Z R (alpha R)
  let : Finite (⁅Z R (alpha R),Z R e⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hcritical_le) (inclusion_injective _)
  have hcard : Nat.card (⁅Z R c.alpha1,K⁆ : Subgroup (FreeAmalgam R)) ≤ 2 :=
    (card_le_of_le hR1).trans_eq (s.small_critical_commutator_card h p hsmall)
  have hcent := s.small_edge_commutator_le_centralizer u hfull c.back_color c.adjacent_back K hK hcard
  have hseed := hR1.trans (s.small_critical_commutator_le_first_seed h u hfull p hsmall)
  have hfixer := c.seed_fixer
  rw [s.edgeOffenderJoin_eq h u hfull rfl c.adjacent_start] at hfixer
  have hR1bot : ⁅Z R c.alpha1,K⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (le_inf (hR1.trans ((s.critical_Z_commutator_le_moving p).trans inf_le_left))
      ((le_inf hseed hcent).trans hfixer)).trans_eq (s.movingLayer_inf_stabilizer_center_eq_bot h)
  have hYfix : Z R c.alpha1 ≤ centralizer (K : Set (FreeAmalgam R)) :=
    commutator_eq_bot_iff_le_centralizer.mp hR1bot
  have hB : Z R c.alpha1 ≤ B R (alpha R) (s.geometry.Z_normal _) := by
    apply le_trans (le_inf le_rfl hYfix)
    apply c.fixed_backward_le_B s h u hfull hb K hK
    have hF : Z R c.alpha1 ⊓ centralizer (K : Set (FreeAmalgam R)) ≤ Q R e ⊔ Z R (alpha R) :=
      (inf_le_inf_right _ hYt).trans hfixed2
    have hQ : Q R e ≤ centralizer (Z R e : Set (FreeAmalgam R)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R e p.end_color))
    have hA : Z R (alpha R) ≤ normalizer (Z R e : Set (FreeAmalgam R)) :=
      (Z_le_stabilizer_of_dist_le (alpha R) _ p.critical.1.le).trans (Z_normalized R e)
    have he := commutator_eq_of_centralizing_sup (V:=Z R e) (X:=Z R (alpha R))
      (C:=Q R e) rfl hQ hA
    rw [commutator_comm]
    exact (commutator_mono le_rfl hF).trans (he.symm.le.trans
      (by simpa only [commutator_comm] using hcritical_le))
  have hU : U R c.alpha1 ≤ B R (alpha R) (s.geometry.Z_normal _) := (DistanceEight.U_le_Z R _).trans hB
  have hBmap : (B R (alpha R) (s.geometry.Z_normal _)).map
      (MulAut.conj c.transporter⁻¹).toMonoidHom = B R (alpha R) (s.geometry.Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      (geometry := s.geometry) hb (alpha R) rfl ((stabilizer R (alpha R)).inv_mem c.transporter_mem))
  rw [c.alpha1_eq,U_act,←hBmap] at hU
  have hUd := (map_le_map_iff_of_injective (MulAut.conj c.transporter⁻¹).injective).mp hU
  have he := relIndex_eq_one.mpr hUd
  omega

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

/-- Both critical-image branches preserve the same eligible coordinated choice. -/
theorem CoordinatedChoice.backward_critical_of_eligible
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {e : Vertex R}
    {p : CriticalPath R s.geometry (alpha R) e} {delta : Vertex R}
    (c : s.CoordinatedChoice p delta)
    (hindex : 1 < (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R delta)) :
    CriticalPair R c.alpha1 (p.walk.getVert (p.walk.length-2))
      (s.geometry.exists_critical c.alpha1 c.back_color) := by
  by_cases hlarge : 4 ≤ (Q R e).relIndex (Z R (alpha R))
  · exact c.large_backward_critical s h u hfull hb hindex hlarge
  have hn := c.small_backward_not_le_of_eligible s h u hfull hb hindex (by omega)
  have hmin := criticalDistance_le R c.alpha1
    (s.geometry.exists_critical c.alpha1 c.back_color) hn
  have hd := p.dist_start (Nat.sub_le p.walk.length 2)
  have htri := (cosetGraph_connected R).dist_triangle
    (u:=c.alpha1) (v:=alpha R) (w:=p.walk.getVert (p.walk.length-2))
  have hback := c.back_distance_le_two
  have hlen := p.length_eq_b
  rw [s.geometry.distance_constant c.alpha1 c.back_color] at hmin
  change s.geometry.b R ≤ _ at hmin
  refine ⟨?_,hn⟩
  rw [s.geometry.distance_constant c.alpha1 c.back_color]
  change _ = s.geometry.b R
  omega

/-- Source (5.8): an eligible coordinated backward critical pair always exists. -/
theorem exists_backward_critical_unconditional
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    ∃ delta, ∃ c : s.CoordinatedChoice p delta,
      Adjacent R delta (p.walk.getVert 1) ∧
      1 < (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R delta) ∧
      CriticalPair R c.alpha1 (p.walk.getVert (p.walk.length-2))
        (s.geometry.exists_critical c.alpha1 c.back_color) := by
  have hpos : 0 < p.walk.length := p.length_eq_b ▸ s.criticalDistance_pos
  have hat : Adjacent R (alpha R) (p.walk.getVert 1) := by
    apply (cosetGraph_adj R _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) hpos
  obtain ⟨delta,hdelta,hmoving⟩ := s.exists_moving_neighbor_at_edge h hb rfl hat
  obtain ⟨c⟩ := s.exists_coordinatedChoice h u hfull p delta hdelta
  let := finite_Z R delta
  let : Finite (U R delta) := Finite.of_injective (inclusion (DistanceEight.U_le_Z R delta)) (inclusion_injective _)
  have hi0 : (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R delta) ≠ 0 := index_ne_zero_of_finite
  have hi1 : (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R delta) ≠ 1 :=
    fun hh => hmoving (relIndex_eq_one.mp hh)
  have hi : 1 < (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R delta) := by omega
  exact ⟨delta,c,hdelta,hi,c.backward_critical_of_eligible s h u hfull hb hi⟩

/-- The original radius escapes the kernel two steps before the critical endpoint. -/
theorem radius_escape_on_path
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    ¬ V R (alpha R) ≤ Q R (p.walk.getVert (p.walk.length-2)) := by
  obtain ⟨delta,c,_,_,hc⟩ := s.exists_backward_critical_unconditional h u hfull hb p
  exact fun hh => hc.2 (c.back_layer_le_radius.trans hh)

private theorem radius_escape_base
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {e : Vertex R}
    (hcrit : CriticalPair R (alpha R) e (s.geometry.exists_critical (alpha R) rfl))
    (c : Vertex R) (hce : (cosetGraph R).dist c e = 2)
    (hpath : (cosetGraph R).dist (alpha R) c + 2 = (cosetGraph R).dist (alpha R) e) :
    ¬ V R (alpha R) ≤ Q R c := by
  obtain ⟨w,hw⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist (alpha R) c
  obtain ⟨v,hv⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist c e
  let p : CriticalPath R s.geometry (alpha R) e :=
    ⟨rfl,w.append v,by rw [SimpleGraph.Walk.length_append,hw,hv,hce,hpath],hcrit⟩
  have heq : p.walk.getVert (p.walk.length-2) = c := by
    change (w.append v).getVert ((w.append v).length-2) = c
    rw [SimpleGraph.Walk.length_append,hv,hce,Nat.add_sub_cancel]
    simp only [SimpleGraph.Walk.getVert_append,lt_self_iff_false,ite_false,Nat.sub_self,SimpleGraph.Walk.getVert_zero]
  simpa only [heq] using s.radius_escape_on_path h u hfull hb p

/-- The exact universal escape premise consumed by critical-path extension. -/
theorem criticalEscape
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) : Factorization.CriticalEscape R s.geometry := by
  intro a ha e hcrit c hce hpath
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color R ha
  have hbase : act R g⁻¹ (mVertex R g) = alpha R := by simp only [act_mVertex,mul_inv_cancel]; rfl
  have ha' : color R (act R g⁻¹ (mVertex R g)) = false := by rw [hbase]; rfl
  have hcrit' := (criticalPair_act_iff R g⁻¹ (mVertex R g) e
    (s.geometry.exists_critical _ ha) (s.geometry.exists_critical _ ha')).mpr hcrit
  have hcritbase : CriticalPair R (alpha R) (act R g⁻¹ e) (s.geometry.exists_critical _ rfl) := by
    simpa only [hbase] using hcrit'
  have hce' : (cosetGraph R).dist (act R g⁻¹ c) (act R g⁻¹ e) = 2 := by rw [dist_act]; exact hce
  have hpath' : (cosetGraph R).dist (alpha R) (act R g⁻¹ c) + 2 =
      (cosetGraph R).dist (alpha R) (act R g⁻¹ e) := by rw [←hbase,dist_act,dist_act]; exact hpath
  have hn := s.radius_escape_base h u hfull hb hcritbase (act R g⁻¹ c) hce' hpath'
  intro hV
  apply hn
  have hh := map_mono (f:=(MulAut.conj (g⁻¹)⁻¹).toMonoidHom) hV
  rw [←V_act,←Q_act,hbase] at hh
  exact hh

/-- Source (5.8): the forward moving layer has Baumann index at least two. -/
theorem forward_moving_index_two_le
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    2 ≤ (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R (p.walk.getVert 2)) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hac : (cosetGraph R).dist (alpha R) c = 2 := p.dist_start (by omega)
  have hc : color R c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent R (alpha R) t := by
    apply (cosetGraph_adj R _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) (by omega)
  have hct : Adjacent R c t := adjacent_symm R ((cosetGraph_adj R _ _).mp
    (p.walk.adj_getVert_succ (i:=1) (by omega)))
  have hpath : (cosetGraph R).dist c e + 2 = (cosetGraph R).dist (alpha R) e := by
    rw [p.dist_end,←p.shortest]
    omega
  have hn := (critical_nonnormal_reverse R s.geometry s.edgeCentralizerCondition
    (s.criticalEscape h u hfull hb) (alpha R) rfl s.criticalDistance_pos p.critical c hac hpath).2
  have hnot : ¬ U R c ≤ B R (alpha R) (s.geometry.Z_normal _) := by
    intro hU
    have hZB : Z R c ≤ B R (alpha R) (s.geometry.Z_normal _) := by
      rw [s.Z_eq_moving_sup_edge_at h hc hct]
      exact sup_le hU ((adjacent_Z_le R rfl hat).trans (Escape.EdgeTransfer.Z_le_B hb (alpha R) rfl))
    apply hn
    apply normal_subgroupOf_of_le_normalizer
    rw [←s.residual_edge_generation rfl hat,sup_comm (Z R c) (X R (alpha R))]
    apply sup_le
    · apply normalizes_join_of_displacement
      · exact (Ltilde_le_stabilizer (alpha R)).trans (X_normalized R (alpha R))
      · apply commutator_le.mpr
        intro l hl x hx
        exact s.Z_le_X (((mem_B_iff R _ _ (s.geometry.V_local _ rfl hb) x).mp (hZB hx)).2 l hl)
    · have htG : Q R t ≤ stabilizer R (alpha R) := fun _ hx => hx.2 _ (adjacent_symm R hat)
      have htC : Q R t ≤ stabilizer R c := fun _ hx => hx.2 _ (adjacent_symm R hct)
      exact (le_inf (htG.trans (X_normalized R _)) (htC.trans (Z_normalized R _))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  let := finite_Z R c
  let : Finite (U R c) := Finite.of_injective (inclusion (DistanceEight.U_le_Z R c)) (inclusion_injective _)
  have hi0 : (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R c) ≠ 0 := index_ne_zero_of_finite
  have hi1 : (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R c) ≠ 1 := fun hh => hnot (relIndex_eq_one.mp hh)
  change 2 ≤ (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R c)
  omega

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L ⊔ d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

/-- The original characteristic replacement supplies backward escape and its index consequence. -/
theorem reducedSource_block_or_backward_escape
    (r : CharacteristicReduction (L.subgroupOf J) R) {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e)
    (hb : 2 < ((originalSource d hm).reduce r).geometry.b r.radical) :
    IsAlternatingBlock L 6 ∨
      (let s := (originalSource d hm).reduce r
       (∃ delta, ∃ c : s.CoordinatedChoice p delta,
         Adjacent r.radical delta (p.walk.getVert 1) ∧
         1 < (B r.radical (alpha r.radical) (s.geometry.Z_normal _)).relIndex (U r.radical delta) ∧
         CriticalPair r.radical c.alpha1 (p.walk.getVert (p.walk.length-2))
           (s.geometry.exists_critical c.alpha1 c.back_color)) ∧
       (¬ V r.radical (alpha r.radical) ≤ Q r.radical (p.walk.getVert (p.walk.length-2))) ∧
       2 ≤ (B r.radical (alpha r.radical) (s.geometry.Z_normal _)).relIndex
         (U r.radical (p.walk.getVert 2)) ∧
       Factorization.CriticalEscape r.radical s.geometry) := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock | hfull
  · exact Or.inl hblock
  · right
    let s := (originalSource d hm).reduce r
    have h := reduced_nativeCentralLayer d hm r
    have hf : r.radical.map s.projection = Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    exact ⟨s.exists_backward_critical_unconditional h _ hf hb p,
      s.radius_escape_on_path h _ hf hb p,s.forward_moving_index_two_le h _ hf hb p,
      s.criticalEscape h _ hf hb⟩

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
