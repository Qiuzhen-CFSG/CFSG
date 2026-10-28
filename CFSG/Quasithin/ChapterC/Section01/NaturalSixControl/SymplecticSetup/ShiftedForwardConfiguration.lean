module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ShiftedSeedChoice
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardSpan
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardKernelNonzero
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ShiftedForwardClosure
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# The shifted forward configuration and its endpoint kernel

Apply the simultaneous shifted-seed choice to the actual nonzero forward
hyperplane commutator. Conjugate the normal forward span and its kernel by
that same element. Replacing the first two edges retains the original
predecessor, so the controlled-line contradiction excludes the new critical
pair. The span first centralizes the predecessor layer and enters its kernel;
then it centralizes the endpoint layer and enters the endpoint kernel.
Both centralizer steps use the same noncentral line of order at most two.

Repeating this argument after each element of the line centralizer places
both literal conjugate spans in the old endpoint kernel. No kernel placement
or noncritical-pair hypothesis remains. The final application retains the
original characteristic reduction and discharges its full-image alternative.
Source: MS93 (5.9), printed pp.920--921, through “In particular Z≤Qe”,
toward Aschbacher--Smith C.1.37 and 13.7.4(1).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

private theorem shifted_two_walk (hb : 4<s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) (y : FreeAmalgam R)
    (hy : y∈stabilizer R (p.walk.getVert 2)) :
    ∃ q : (cosetGraph R).Walk (act R y⁻¹ (alpha R)) e,
      q.length=p.walk.length ∧ q.getVert 2=p.walk.getVert 2 ∧
      q.getVert (p.walk.length-2)=p.walk.getVert (p.walk.length-2) := by
  have hl := p.length_eq_b
  have hfix : act R y⁻¹ (p.walk.getVert 2)=p.walk.getVert 2 :=
    (stabilizer R (p.walk.getVert 2)).inv_mem hy
  let q₀ := (actWalk R y⁻¹ (p.walk.take 2)).copy rfl hfix
  have hq₀ : q₀.length=2 := by
    simp only [q₀,SimpleGraph.Walk.length_copy,actWalk_length,SimpleGraph.Walk.take_length,
      inf_eq_left.mpr (by omega : 2≤p.walk.length)]
  refine ⟨q₀.append (p.walk.drop 2),?_,?_,?_⟩
  · rw [SimpleGraph.Walk.length_append,hq₀,SimpleGraph.Walk.drop_length]
    omega
  · rw [SimpleGraph.Walk.getVert_append',hq₀,if_pos (by omega)]
    simpa only [q₀,SimpleGraph.Walk.getVert_copy,actWalk_getVert,
      SimpleGraph.Walk.take_getVert,inf_idem] using hfix
  · rw [SimpleGraph.Walk.getVert_append,hq₀,if_neg (by omega),SimpleGraph.Walk.drop_getVert]
    congr 1
    omega

private theorem radius_le_stabilizer_of_dist (a v : Vertex R) (ha : color R a=false)
    (hdis : (cosetGraph R).dist a v+2≤s.geometry.b R) :
    V R a≤stabilizer R v := by
  apply (V_le_iff R ha _).mpr
  intro d hd hda
  apply Z_le_stabilizer_of_dist_le d (s.geometry.exists_critical d hd)
  rw [s.geometry.distance_constant d hd]
  have ht := (cosetGraph_connected R).dist_triangle (u:=d) (v:=a) (w:=v)
  change (cosetGraph R).dist d v≤s.geometry.b R
  omega

private theorem line_collapse {G : Type*} [Group G] (H A C : Subgroup G)
    [Finite H] (hc : Nat.card H≤2) (hHC : ¬H≤C) (hAH : A≤H) (hAC : A≤C) : A=⊥ := by
  by_contra hn
  let : Finite A := Finite.of_injective (inclusion hAH) (inclusion_injective _)
  have hpos := (one_lt_card_iff_ne_bot A).mpr hn
  have he : A=H := eq_of_le_of_card_ge hAH (by omega)
  exact hHC (he ▸ hAC)


private theorem shifted_span_properties
    (hb : 4<s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (hindex : (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R (p.walk.getVert 2))=2)
    (y : FreeAmalgam R) (hy : y∈stabilizer R (p.walk.getVert 2))
    (H : Subgroup (FreeAmalgam R)) (hHZ : H≤Z R (alpha R))
    (hHC : H≤centralizer (stabilizer R (alpha R):Set (FreeAmalgam R)))
    (hcomm : ⁅localZSpan R (p.walk.getVert 2) (alpha R),
      Q R (alpha R)⊓centralizer (U R (p.walk.getVert 2)⊓B R (alpha R) (s.geometry.Z_normal _):Set (FreeAmalgam R))⁆≤H) :
    let a := act R y⁻¹ (alpha R)
    let Y := (localZSpan R (p.walk.getVert 2) (alpha R)).map (MulAut.conj y).toMonoidHom
    let T₀ := Q R (alpha R)⊓centralizer (U R (p.walk.getVert 2)⊓B R (alpha R) (s.geometry.Z_normal _):Set (FreeAmalgam R))
    let T₂ := T₀.map (MulAut.conj y).toMonoidHom
    let H₂ := H.map (MulAut.conj y).toMonoidHom
    T₂=Q R a⊓centralizer (U R (p.walk.getVert 2)⊓B R a (s.geometry.Z_normal _):Set (FreeAmalgam R)) ∧
    Z R (p.walk.getVert 2)≤Y ∧ Y≤V R a ∧
    stabilizer R a≤normalizer (Y:Set (FreeAmalgam R)) ∧
    ¬Y≤B R a (s.geometry.Z_normal _) ∧ H₂≤Z R a ∧
    H₂≤centralizer (stabilizer R a:Set (FreeAmalgam R)) ∧ ⁅Y,T₂⁆≤H₂ := by
  let f := (MulAut.conj y).toMonoidHom
  have hl := p.length_eq_b
  have hU : (U R (p.walk.getVert 2)).map f=U R (p.walk.getVert 2) :=
    mem_normalizer_iff_map_conj_eq.mp (U_normalized _ hy)
  have hZ : (Z R (p.walk.getVert 2)).map f=Z R (p.walk.getVert 2) :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized R _ hy)
  have hB := Escape.PairingControl.FirstPairing.B_act (geometry:=s.geometry)
    (by omega : 2<s.geometry.b R) y⁻¹ (alpha R) rfl
  simp only [inv_inv] at hB
  have hYV : localZSpan R (p.walk.getVert 2) (alpha R)≤V R (alpha R) :=
    localZSpan_le_V R (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hUB : (U R (p.walk.getVert 2)⊓B R (alpha R) (s.geometry.Z_normal _)).map f =
        U R (p.walk.getVert 2)⊓B R (act R y⁻¹ (alpha R)) (s.geometry.Z_normal _) := by
      rw [map_inf _ _ f (MulAut.conj y).injective,hU,hB]
    have hm := map_inf_centralizer_of_injective f (MulAut.conj y).injective
      (Q R (alpha R)) (U R (p.walk.getVert 2)⊓B R (alpha R) (s.geometry.Z_normal _))
    rw [hUB] at hm
    simpa only [Q_act,inv_inv,coe_inf,Set.inf_eq_inter,f] using hm.symm
  · exact hZ.symm.le.trans (map_mono (Z_le_localZSpan R _ _))
  · simpa only [V_act,inv_inv] using (map_mono (f:=f) hYV)
  · rw [stabilizer_act,inv_inv]
    exact (map_mono (localZSpan_normalized R _ _)).trans
      ((localZSpan R _ _).le_normalizer_map f)
  · rw [hB]
    intro hh
    have hAB := (map_le_map_iff_of_injective (MulAut.conj y).injective).mp hh
    have hUB := (U_le_Z _).trans ((Z_le_localZSpan R _ _).trans hAB)
    have hi := relIndex_eq_one.mpr hUB
    omega
  · simpa only [Z_act,inv_inv] using (map_mono (f:=f) hHZ)
  · rw [stabilizer_act,inv_inv]
    intro z hz g hg
    obtain ⟨z,hz,rfl⟩ := hz
    obtain ⟨g,hg,rfl⟩ := hg
    simpa only [map_mul] using congrArg f (hHC hz g hg)
  · rw [←map_commutator]
    exact map_mono hcomm

/-- The shifted span and seed lie in the old endpoint kernel. The same statement
applies after any further conjugation fixing the controlled line. -/
private theorem shifted_span_le_endpoint_kernel
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 4<s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (hindex : (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R (p.walk.getVert 2))=2)
    (d : Vertex R) (hd : color R d=false) (hed : (cosetGraph R).dist e d=2)
    (H : Subgroup (FreeAmalgam R)) (hHZ : H≤Z R (alpha R)) (hcard : Nat.card H≤2)
    (hHC : H≤centralizer (stabilizer R (alpha R):Set (FreeAmalgam R)))
    (hcomm : ⁅localZSpan R (p.walk.getVert 2) (alpha R),
      Q R (alpha R)⊓centralizer (U R (p.walk.getVert 2)⊓B R (alpha R) (s.geometry.Z_normal _):Set (FreeAmalgam R))⁆≤H)
    (y : FreeAmalgam R) (hy : y∈stabilizer R (p.walk.getVert 2))
    (hmove : ¬H.map (MulAut.conj y).toMonoidHom≤centralizer (Z R d:Set (FreeAmalgam R))) :
    Z R (act R y⁻¹ (alpha R))≤Q R e ∧
      (localZSpan R (p.walk.getVert 2) (alpha R)).map (MulAut.conj y).toMonoidHom≤Q R e := by
  let a := act R y⁻¹ (alpha R)
  let c := p.walk.getVert 2
  let v := p.walk.getVert (p.walk.length-2)
  let f := (MulAut.conj y).toMonoidHom
  let Y := (localZSpan R c (alpha R)).map f
  let T₀ := Q R (alpha R)⊓centralizer (U R c⊓B R (alpha R) (s.geometry.Z_normal _):Set (FreeAmalgam R))
  let T₂ := T₀.map f
  let H₂ := H.map f
  have ha : color R a=false := (action_preserves_color R y⁻¹ (alpha R)).trans rfl
  have hl := p.length_eq_b
  have hc : color R c=false := (p.vertex_color (by omega)).mpr (by decide)
  have hv : color R v=false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := s.geometry.even (alpha R) rfl
    change Even (s.geometry.b R) at he
    rw [Nat.even_iff] at he ⊢
    omega
  obtain ⟨hT,hZcY,hYV,hYN,hYB,hHZa,hHCa,hcomm₂⟩ :=
    s.shifted_span_properties hb p hindex y hy H hHZ hHC hcomm
  change T₂=Q R a⊓centralizer (U R c⊓B R a (s.geometry.Z_normal _):Set (FreeAmalgam R)) at hT
  change Y≤V R a at hYV
  change ⁅Y,T₂⁆≤H₂ at hcomm₂
  have hcard₂ : Nat.card H₂≤2 := by
    dsimp only [H₂,f]
    rwa [card_map_of_injective (MulAut.conj y).injective]
  let := finite_Z R a
  let : Finite H₂ := Finite.of_injective (inclusion hHZa) (inclusion_injective _)
  obtain ⟨q,hql,hqc,hqv⟩ := s.shifted_two_walk hb p y hy
  have hdae : (cosetGraph R).dist a e≤s.geometry.b R := by
    have hh := SimpleGraph.dist_le q
    rwa [hql,hl] at hh
  have hdav : (cosetGraph R).dist a v≤p.walk.length-2 := by
    have hh := SimpleGraph.dist_le (q.take (p.walk.length-2))
    rw [SimpleGraph.Walk.take_length,hql,inf_eq_left.mpr (Nat.sub_le _ _),hqv] at hh
    exact hh
  have hvQc : Z R v≤Q R c := by
    apply Z_le_Q_of_dist_lt R v (s.geometry.exists_critical v hv)
    rw [s.geometry.distance_constant v hv,SimpleGraph.dist_comm]
    have hh := SimpleGraph.dist_le ((p.walk.drop 2).take (p.walk.length-4))
    rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length,
      inf_eq_left.mpr (by omega : p.walk.length-4≤p.walk.length-2),
      SimpleGraph.Walk.drop_getVert,show 2+(p.walk.length-4)=p.walk.length-2 by omega] at hh
    change (cosetGraph R).dist c v<s.geometry.b R
    exact lt_of_le_of_lt hh (by omega)
  have heQc : Z R e≤Q R c := by
    apply Z_le_Q_of_dist_lt R e (s.geometry.exists_critical e p.end_color)
    rw [s.geometry.distance_constant e p.end_color,SimpleGraph.dist_comm,p.dist_end]
    change p.walk.length-2<s.geometry.b R
    omega
  have hvQa : Z R v≤Q R a := by
    apply Z_le_Q_of_dist_lt R v (s.geometry.exists_critical v hv)
    rw [s.geometry.distance_constant v hv,SimpleGraph.dist_comm]
    change (cosetGraph R).dist a v<s.geometry.b R
    omega
  have hQcC : Q R c≤centralizer (U R c⊓B R a (s.geometry.Z_normal _):Set (FreeAmalgam R)) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R c hc))).trans
      (centralizer_le (inf_le_left.trans (U_le_Z _)))
  have hinner : Z R v⊔(Z R e⊓Q R a)≤T₂ := by
    rw [hT]
    exact le_inf (sup_le hvQa inf_le_right)
      ((sup_le hvQc (inf_le_left.trans heQc)).trans hQcC)
  have hvd : (cosetGraph R).dist v d≤4 := by
    have hh := (cosetGraph_connected R).dist_triangle (u:=v) (v:=e) (w:=d)
    have hve : (cosetGraph R).dist v e=2 := by
      change (cosetGraph R).dist (p.walk.getVert (p.walk.length-2)) e=2
      rw [p.dist_end]
      omega
    omega
  have hZaQe : Z R a≤Q R e := by
    by_contra hn
    have hmin := criticalDistance_le R a (s.geometry.exists_critical a ha) hn
    rw [s.geometry.distance_constant a ha] at hmin
    have heq : (cosetGraph R).dist a e=s.geometry.b R := le_antisymm hdae hmin
    have hcrit : CriticalPair R a e (s.geometry.exists_critical a ha) :=
      ⟨heq.trans (s.geometry.distance_constant a ha).symm,hn⟩
    let p₂ : CriticalPath R s.geometry a e := ⟨ha,q,hql.trans (hl.trans heq.symm),hcrit⟩
    have hpred : p₂.walk.getVert (p₂.walk.length-2)=v := by
      change q.getVert (q.length-2)=v
      rw [hql,hqv]
    apply s.shifted_critical_controlled_line_false_at h u hfull hb ha p₂ d hd hed.le
      (by rwa [hpred]) Y T₂ H₂ hYV hYN hYB hHZa hcard₂ hmove hcomm₂
    rwa [hpred]
  have heQa : Z R e≤Q R a := by
    rw [←s.C_eq_Q a ha]
    refine le_inf ?_ ?_
    · apply Z_le_stabilizer_of_dist_le e (s.geometry.exists_critical e p.end_color)
      rw [s.geometry.distance_constant e p.end_color,SimpleGraph.dist_comm]
      exact hdae
    · exact le_centralizer_iff.mp (hZaQe.trans
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R e p.end_color))))
  have heT : Z R e≤T₂ := by
    rw [hT]
    exact le_inf heQa (heQc.trans hQcC)
  have hQd : Q R d≤centralizer (Z R d:Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R d hd))
  have hvC : Z R v≤centralizer (Z R d:Set (FreeAmalgam R)) := by
    apply le_trans _ hQd
    apply Z_le_Q_of_dist_lt R v (s.geometry.exists_critical v hv)
    rw [s.geometry.distance_constant v hv]
    exact lt_of_le_of_lt hvd hb
  have heC : Z R e≤centralizer (Z R d:Set (FreeAmalgam R)) := by
    apply le_trans _ hQd
    apply Z_le_Q_of_dist_lt R e (s.geometry.exists_critical e p.end_color)
    rw [s.geometry.distance_constant e p.end_color,hed]
    change 2<s.geometry.b R
    omega
  have hYGv : Y≤stabilizer R v := hYV.trans
    (s.radius_le_stabilizer_of_dist a v ha (by omega))
  have hYv : ⁅Y,Z R v⁆=⊥ :=
    line_collapse H₂ _ (centralizer (Z R d:Set (FreeAmalgam R))) hcard₂ hmove
      ((commutator_mono le_rfl (le_sup_left.trans hinner)).trans hcomm₂)
      ((le_normalizer_iff_commutator_le_right.mp (hYGv.trans (Z_normalized R v))).trans hvC)
  have hYQv : Y≤Q R v := by
    rw [←s.C_eq_Q v hv]
    exact le_inf hYGv (commutator_eq_bot_iff_le_centralizer.mp hYv)
  have hedge := s.critical_last_edge_inputs (by omega : 2<s.geometry.b R) p
  have hYGe : Y≤stabilizer R e := (hYQv.trans hedge.2.1).trans
    (fun _ hx => hx.2 _ (adjacent_symm R hedge.1))
  have hYe : ⁅Y,Z R e⁆=⊥ :=
    line_collapse H₂ _ (centralizer (Z R d:Set (FreeAmalgam R))) hcard₂ hmove
      ((commutator_mono le_rfl heT).trans hcomm₂)
      ((le_normalizer_iff_commutator_le_right.mp (hYGe.trans (Z_normalized R e))).trans heC)
  refine ⟨hZaQe,?_⟩
  rw [←s.C_eq_Q e p.end_color]
  exact le_inf hYGe (commutator_eq_bot_iff_le_centralizer.mp hYe)

/-- The literal same-choice configuration and its endpoint-kernel spans. -/
@[expose] def ShiftedForwardConfiguration (hb : 4<s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) : Prop :=
    let T₀ := Q R (alpha R)⊓centralizer
      (U R (p.walk.getVert 2)⊓B R (alpha R) (s.geometry.Z_normal _):Set (FreeAmalgam R))
    let H := ⁅U R (p.walk.getVert 2),T₀⁆
    ∃ d, ∃ _hd : color R d=false, (cosetGraph R).dist e d=2 ∧
      CriticalPair R (p.walk.getVert 2) d
        (s.geometry.exists_critical _ ((p.vertex_color (by rw [p.length_eq_b]; omega)).mpr (by decide))) ∧
      ∃ y ∈ stabilizer R (p.walk.getVert 2),
        let a := act R y⁻¹ (alpha R)
        let T₂ := T₀.map (MulAut.conj y).toMonoidHom
        let H₂ := H.map (MulAut.conj y).toMonoidHom
        let Y := (localZSpan R (p.walk.getVert 2) (alpha R)).map (MulAut.conj y).toMonoidHom
        let P := stabilizer R (p.walk.getVert 2)⊓centralizer (H₂:Set (FreeAmalgam R))
        P⊔Z R d=stabilizer R (p.walk.getVert 2) ∧
        ¬H₂≤centralizer (Z R d:Set (FreeAmalgam R)) ∧
        T₂=Q R a⊓centralizer (U R (p.walk.getVert 2)⊓B R a (s.geometry.Z_normal _):Set (FreeAmalgam R)) ∧
        Z R (p.walk.getVert 2)≤Y ∧ Y≤V R a ∧
        stabilizer R a≤normalizer (Y:Set (FreeAmalgam R)) ∧
        ¬Y≤B R a (s.geometry.Z_normal _) ∧ H₂≤Z R a ∧ Nat.card H₂≤2 ∧
        H₂≤centralizer (stabilizer R a:Set (FreeAmalgam R)) ∧ ⁅Y,T₂⁆≤H₂ ∧
        Z R a≤Q R e ∧ Y≤Q R e ∧
        conjugateSpanBy (Z R a) P≤Q R e ∧ conjugateSpanBy Y P≤Q R e

/-- Complete the actual source configuration for a prescribed shifted endpoint
and conjugator. This preserves any further properties of the supplied witnesses,
including a generating edge containing the same moving line. -/
theorem shifted_forward_configuration_of_choice
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 4<s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (hindex : (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R (p.walk.getVert 2))=2)
    (d : Vertex R) (hd : color R d=false) (hed : (cosetGraph R).dist e d=2)
    (_hcritical : CriticalPair R (p.walk.getVert 2) d
      (s.geometry.exists_critical _ ((p.vertex_color (by rw [p.length_eq_b]; omega)).mpr (by decide))))
    (y : FreeAmalgam R) (hy : y∈stabilizer R (p.walk.getVert 2)) :
    let T₀ := Q R (alpha R)⊓centralizer
      (U R (p.walk.getVert 2)⊓B R (alpha R) (s.geometry.Z_normal _):Set (FreeAmalgam R))
    let H := ⁅U R (p.walk.getVert 2),T₀⁆
    ((stabilizer R (p.walk.getVert 2)⊓
      centralizer (H.map (MulAut.conj y).toMonoidHom:Set (FreeAmalgam R)))⊔Z R d=
        stabilizer R (p.walk.getVert 2)) →
    (¬H.map (MulAut.conj y).toMonoidHom≤centralizer (Z R d:Set (FreeAmalgam R))) →
    let a := act R y⁻¹ (alpha R)
    let T₂ := T₀.map (MulAut.conj y).toMonoidHom
    let H₂ := H.map (MulAut.conj y).toMonoidHom
    let Y := (localZSpan R (p.walk.getVert 2) (alpha R)).map (MulAut.conj y).toMonoidHom
    let P := stabilizer R (p.walk.getVert 2)⊓centralizer (H₂:Set (FreeAmalgam R))
    P⊔Z R d=stabilizer R (p.walk.getVert 2) ∧
    ¬H₂≤centralizer (Z R d:Set (FreeAmalgam R)) ∧
    T₂=Q R a⊓centralizer (U R (p.walk.getVert 2)⊓B R a (s.geometry.Z_normal _):Set (FreeAmalgam R)) ∧
    Z R (p.walk.getVert 2)≤Y ∧ Y≤V R a ∧
    stabilizer R a≤normalizer (Y:Set (FreeAmalgam R)) ∧
    ¬Y≤B R a (s.geometry.Z_normal _) ∧ H₂≤Z R a ∧ Nat.card H₂≤2 ∧
    H₂≤centralizer (stabilizer R a:Set (FreeAmalgam R)) ∧ ⁅Y,T₂⁆≤H₂ ∧
    Z R a≤Q R e ∧ Y≤Q R e ∧
    conjugateSpanBy (Z R a) P≤Q R e ∧ conjugateSpanBy Y P≤Q R e := by
  dsimp only
  intro hgen hmove
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T₀ := Q R (alpha R)⊓centralizer (U R c⊓B R (alpha R) (s.geometry.Z_normal _):Set (FreeAmalgam R))
  let H := ⁅U R c,T₀⁆
  have hl := p.length_eq_b
  have hc : color R c=false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent R (alpha R) t := by
    apply (cosetGraph_adj R _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) (by omega)
  have hct : Adjacent R c t := adjacent_symm R ((cosetGraph_adj R _ _).mp
    (p.walk.adj_getVert_succ (i:=1) (by omega)))
  have hline := s.moving_hyperplane_commutator_le_seed h u hfull rfl hc hat hct hindex.le
  have hcard : Nat.card H≤2 := hline.1
  have hHZ : H≤Z R (alpha R) := hline.2.trans (adjacent_Z_le R rfl hat)
  have hspan := s.critical_forward_span_commutator_le_line h u hfull hb p hindex.le
  have hplace := s.shifted_span_le_endpoint_kernel h u hfull hb p hindex
  obtain ⟨hT,hZcY,hYV,hYN,hYB,hHZa,hHCa,hcomm⟩ :=
    s.shifted_span_properties hb p hindex y hy H hHZ hspan.1 hspan.2
  have hyplace := hplace d hd hed H hHZ hcard hspan.1 hspan.2 y hy hmove
  let a := act R y⁻¹ (alpha R)
  let H₂ := H.map (MulAut.conj y).toMonoidHom
  let Y := (localZSpan R c (alpha R)).map (MulAut.conj y).toMonoidHom
  let P := stabilizer R c⊓centralizer (H₂:Set (FreeAmalgam R))
  have hmap (A : Subgroup (FreeAmalgam R)) (x : FreeAmalgam R) :
      (A.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom =
        A.map (MulAut.conj (x*y)).toMonoidHom := by
    rw [map_map]
    congr 1
    apply MonoidHom.ext
    intro z
    change x*(y*z*y⁻¹)*x⁻¹=(x*y)*z*(x*y)⁻¹
    group
  have hconj (x : P) :
      (Z R a).map (MulAut.conj (x:FreeAmalgam R)).toMonoidHom≤Q R e ∧
      Y.map (MulAut.conj (x:FreeAmalgam R)).toMonoidHom≤Q R e := by
    have hxH : H₂.map (MulAut.conj (x:FreeAmalgam R)).toMonoidHom=H₂ :=
      mem_normalizer_iff_map_conj_eq.mp ((Subgroup.centralizer_le_normalizer _) x.property.2)
    have hxy : (x:FreeAmalgam R)*y∈stabilizer R c :=
      (stabilizer R c).mul_mem x.property.1 hy
    have hmove' : ¬H.map (MulAut.conj ((x:FreeAmalgam R)*y)).toMonoidHom≤
        centralizer (Z R d:Set (FreeAmalgam R)) := by
      rw [←hmap]
      change ¬H₂.map (MulAut.conj (x:FreeAmalgam R)).toMonoidHom≤_
      rw [hxH]
      exact hmove
    have hh := hplace d hd hed H hHZ hcard hspan.1 hspan.2 _ hxy hmove'
    change (Z R (act R y⁻¹ (alpha R))).map _≤_ ∧
      ((localZSpan R c (alpha R)).map (MulAut.conj y).toMonoidHom).map _≤_
    rw [Z_act,inv_inv,hmap,hmap]
    simpa only [Z_act,inv_inv] using hh
  refine ⟨hgen,hmove,hT,hZcY,hYV,hYN,hYB,hHZa,?_,hHCa,hcomm,
    hyplace.1,hyplace.2,?_,?_⟩
  · rw [card_map_of_injective (MulAut.conj y).injective]
    exact hcard
  · rw [conjugateSpanBy_eq_iSup_conj]
    exact iSup_le (fun x => (hconj x).1)
  · rw [conjugateSpanBy_eq_iSup_conj]
    exact iSup_le (fun x => (hconj x).2)

/-- The actual source (5.9) shifted configuration, including both normal spans
in the old endpoint kernel. Every clause uses the same shifted endpoint and
conjugator selected from the nonzero forward commutator line. -/
theorem exists_shifted_forward_configuration
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 4<s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (hindex : (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R (p.walk.getVert 2))=2) :
    s.ShiftedForwardConfiguration hb p := by
  unfold ShiftedForwardConfiguration
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T₀ := Q R (alpha R)⊓centralizer (U R c⊓B R (alpha R) (s.geometry.Z_normal _):Set (FreeAmalgam R))
  let H := ⁅U R c,T₀⁆
  have hl := p.length_eq_b
  have hc : color R c=false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent R (alpha R) t := by
    apply (cosetGraph_adj R _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) (by omega)
  have hct : Adjacent R c t := adjacent_symm R ((cosetGraph_adj R _ _).mp
    (p.walk.adj_getVert_succ (i:=1) (by omega)))
  have ht : color R t=true := by
    have hh := adjacent_color_ne R hat
    change false≠color R t at hh
    cases hh' : color R t <;> simp_all
  have hTQt : T₀≤Q R t := inf_le_left.trans (Q_le_adjacent_h R ht hat)
  have hTGc : T₀≤stabilizer R c := hTQt.trans (fun _ hx => hx.2 _ (adjacent_symm R hct))
  have hHU : H≤U R c := le_normalizer_iff_commutator_le_left.mp (hTGc.trans (U_normalized c))
  have hHne : H≠⊥ := s.critical_forward_kernel_commutator_ne_bot h u hfull hb p hindex
  have hline := s.moving_hyperplane_commutator_le_seed h u hfull rfl hc hat hct hindex.le
  have hcard : Nat.card H≤2 := hline.1
  obtain ⟨d,hd,hed,hcd,y,hy,hgen,hmove⟩ := s.exists_shifted_seed_choice h u hfull hb p H hHU hHne hcard
  exact ⟨d,hd,hed,hcd,y,hy,
    s.shifted_forward_configuration_of_choice h u hfull hb p hindex d hd hed hcd y hy hgen hmove⟩

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L ⊔ d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

/-- The exact shifted configuration on the literal characteristic replacement,
with the full point-image alternative discharged. -/
theorem reducedSource_block_or_shifted_forward_configuration
    (r : CharacteristicReduction (L.subgroupOf J) R) {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e)
    (hb : 4<((originalSource d hm).reduce r).geometry.b r.radical)
    (hindex : (B r.radical (alpha r.radical) (((originalSource d hm).reduce r).geometry.Z_normal _)).relIndex
      (U r.radical (p.walk.getVert 2))=2) :
    IsAlternatingBlock L 6 ∨ ((originalSource d hm).reduce r).ShiftedForwardConfiguration hb p := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock | hfull
  · exact Or.inl hblock
  · right
    let s := (originalSource d hm).reduce r
    have h := reduced_nativeCentralLayer d hm r
    have hf : r.radical.map s.projection=Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    exact s.exists_shifted_forward_configuration h _ hf hb p hindex

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
