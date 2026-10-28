module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.BackwardEscape
public import Theory.GroupAction.SubgroupConjugation
public import Theory.GroupTheory.CentralizerInjectiveImage
/-!
# Excluding large critical distance in the native symplectic source

The first edge kernel normalizes the critical Z-commutator, because its
point-core image is abelian. A finite two-group fixed-point argument gives
a nonzero element of that commutator in the first edge seed.

Two prescribed backward critical shifts provide two local generating pairs.
If b > 4, their endpoint layers centralize the original commutator. Its fixed
edge subgroup therefore lies in the centers of two successive vertex groups.
The shared local conjugator carries the second center back to the first
critical vertex, contradicting the absence of fixed vectors in its moving
natural layer. Native source (5.8) already supplies the required eligibility,
so no strict-index premise or later normalization alternative is needed.

The SourceData application uses the actual characteristic replacement and
retains only its separately discharged alternating-block alternative.
Source: Meierfrankenfeld--Stellmacher (1993), the first centrality calculation
in (5.10), printed p.922, specialized to the full point-core native module.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)
private theorem fixed_mod_central_normalizes {G : Type*} [Group G]
    (A Q D : Subgroup G) (hAQ : A ≤ normalizer (Q : Set G))
    (hDQ : D ≤ normalizer (Q : Set G))
    (hDA : ⁅D,A⁆ ≤ centralizer (Q : Set G)) :
    D ≤ normalizer ((⁅A,Q⁆ : Subgroup G) : Set G) := by
  apply le_normalizer_closure_iff.mpr
  rintro d hd _ ⟨a,ha,q,hq,rfl⟩
  have hq' : d*q*d⁻¹ ∈ Q := (mem_normalizer_iff.mp (hDQ hd) q).mp hq
  have hk : ⁅d,a⁆ ∈ centralizer (Q : Set G) := hDA (commutator_mem_commutator hd ha)
  have hcomm : ⁅a,d*q*d⁻¹⁆ ∈ Q :=
    le_normalizer_iff_commutator_le_right.mp hAQ (commutator_mem_commutator ha hq')
  have hzero : ⁅⁅d,a⁆,d*q*d⁻¹⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hk _ hq').symm
  rw [conjugate_commutatorElement,show d*a*d⁻¹ = ⁅d,a⁆*a by
    simp [commutatorElement_def,mul_assoc],commutatorElement_mul_left_eq_conj_mul,
    hzero,mul_one,←hk _ hcomm,mul_inv_cancel_right]
  exact commutator_mem_commutator ha hq'

theorem critical_commutator_inf_first_seed_ne_bot
    (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    {a e : Vertex R} (p : CriticalPath R s.geometry a e) :
    ⁅Z R a,Z R e⁆ ⊓ Z R (p.walk.getVert 1) ≠ ⊥ := by
  let D := ⁅Z R a,Z R e⁆
  let t := p.walk.getVert 1
  have hpos : 0<p.walk.length := p.length_eq_b ▸ s.criticalDistance_pos
  have hat : Adjacent R a t := by
    apply (cosetGraph_adj R _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero,Nat.zero_add] using
      p.walk.adj_getVert_succ (i:=0) hpos
  have ht : color R t=true := by
    have hn := adjacent_color_ne R hat
    rw [p.start_color] at hn
    cases hc : color R t <;> simp_all
  have hZe : Z R e≤Q R t := by
    apply Z_le_Q_of_dist_lt R e (s.geometry.exists_critical e p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,s.geometry.distance_constant e p.end_color]
    change p.walk.length-1<s.geometry.b R
    rw [←p.length_eq_b]
    omega
  have hQtG : Q R t≤stabilizer R a := fun _ hx => hx.2 a (adjacent_symm R hat)
  have hQtZ := hQtG.trans (Z_normalized R a)
  have hder : ⁅Q R t,Z R e⁆≤centralizer (Z R a:Set (FreeAmalgam R)) :=
    ((commutator_mono le_rfl hZe).trans (s.edge_derived_le_kernel u hfull p.start_color hat)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q R a p.start_color)))
  have hn : Q R t≤normalizer (D:Set (FreeAmalgam R)) := by
    dsimp only [D]
    rw [commutator_comm (Z R a)]
    exact fixed_mod_central_normalizes (Z R e) (Z R a) (Q R t)
      (hZe.trans hQtZ) hQtZ hder
  have hDZ : D≤Z R a :=
    ((s.critical_Z_commutator_le_moving p).trans inf_le_left).trans (DistanceEight.U_le_Z R a)
  have hZaQ : Z R a≤Q R a := by
    apply Z_le_Q_of_dist_lt R a (s.geometry.exists_critical a p.start_color)
    simpa only [SimpleGraph.dist_self] using
      (s.geometry.distance_constant a p.start_color).symm ▸ s.criticalDistance_pos
  have hDQt : D≤Q R t := (hDZ.trans hZaQ).trans (Q_le_adjacent_h R ht hat)
  have hDne : D≠⊥ := by
    intro hz
    apply p.critical.2
    rw [←s.C_eq_Q e p.end_color]
    exact le_inf (Z_le_stabilizer_of_dist_le a _ p.critical.1.le)
      (commutator_eq_bot_iff_le_centralizer.mp hz)
  have hQtP : IsPGroup 2 (Q R t) := by
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common R a t).mp hat
    · rw [hg.2]
      have he := Q_act R g (beta R)
      simp only [beta,act_hVertex,one_mul] at he
      rw [he]
      change IsPGroup 2 ((Q R (beta R)).map _)
      rw [Q_beta]
      exact (s.two_group.map (embedM R)).map _
    · have hh := p.start_color
      rw [hg.1] at hh
      cases hh
  let := finite_stabilizer R a
  let : Finite (Q R t) := Finite.of_injective (inclusion hQtG) (inclusion_injective _)
  let : Finite D := Finite.of_injective (inclusion hDQt) (inclusion_injective _)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : MulDistribMulAction (Q R t) D := conjMulDistribMulActionOfLeNormalizer _ _ hn
  have hdvd : 2∣Nat.card D := (hQtP.to_le hDQt).card_eq_or_dvd.resolve_left
    (fun hc => hDne (Subgroup.card_eq_one.mp hc))
  obtain ⟨r,hr,hrne⟩ := hQtP.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (α:=D) hdvd (show (1:D)∈MulAction.fixedPoints (Q R t) D by simp [MulAction.mem_fixedPoints])
  have hrC : (r:FreeAmalgam R)∈centralizer (Q R t:Set (FreeAmalgam R)) := by
    intro q hq
    have hh := congrArg D.subtype ((MulAction.mem_fixedPoints.mp hr) ⟨q,hq⟩)
    change q*(r:FreeAmalgam R)*q⁻¹=r at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hrZ : (r:FreeAmalgam R)∈Z R t := by
    rw [Z,if_neg (by simp [ht])]
    let := s.geometry.Z_elementary s.criticalDistance_pos a p.start_color
    exact mem_omegaCenter_iff.mpr ⟨hDQt r.property,
      elemPow_eq_one_of_isElementaryAbelian _ (hDZ r.property),hrC⟩
  intro hbot
  have hrmem : (r:FreeAmalgam R)∈D⊓Z R t := ⟨r.property,hrZ⟩
  change (r:FreeAmalgam R)∈⁅Z R a,Z R e⁆⊓Z R (p.walk.getVert 1) at hrmem
  rw [hbot] at hrmem
  have hr1 : (r:FreeAmalgam R)=1 := hrmem
  exact hrne (Subtype.ext hr1.symm)
private theorem moving_inf_full_centralizer_eq_bot_at (h : NativeCentralLayer s)
    {a : Vertex R} (ha : color R a=false) :
    U R a⊓centralizer (stabilizer R a:Set (FreeAmalgam R))=⊥ := by
  have hb : U R (alpha R)⊓centralizer (stabilizer R (alpha R):Set (FreeAmalgam R))=⊥ := by
    apply le_bot_iff.mp
    exact (inf_le_inf_left _ (centralizer_le (Ltilde_le_stabilizer _))).trans_eq
      (s.movingLayer_inf_component_centralizer_eq_bot h)
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color R ha
  have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hb
  rw [←map_inf_centralizer_of_injective _ (MulAut.conj g⁻¹).injective,
    ←U_act,←stabilizer_act,Subgroup.map_bot] at hh
  simpa only [alpha,act_mVertex,one_mul] using hh

private theorem central_fixed_map {G : Type*} [Group G] (H K : Subgroup G)
    (hHK : H≤centralizer (K:Set G)) {g : G} (hg : g∈K) :
    H.map (MulAut.conj g).toMonoidHom=H := by
  apply mem_normalizer_iff_map_conj_eq.mp
  exact Subgroup.centralizer_le_normalizer _ (le_centralizer_iff.mp hHK hg)

/-- The native central moving layer excludes the first two shifts in (5.10). -/
theorem false_of_three_shift_generators (h : NativeCentralLayer s)
    (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    {a e : Vertex R} (p : CriticalPath R s.geometry a e)
    (c v d f g : Vertex R)
    (hct : Adjacent R c (p.walk.getVert 1)) (hcv : Adjacent R c v)
    (hgenC : Q R (p.walk.getVert 1)⊔Z R f=stabilizer R c)
    (hgenD : Q R v⊔Z R g=stabilizer R d)
    (hRf : ⁅Z R a,Z R e⁆≤centralizer (Z R f:Set (FreeAmalgam R)))
    (hRg : ⁅Z R a,Z R e⁆≤centralizer (Z R g:Set (FreeAmalgam R)))
    (x : FreeAmalgam R) (hx : x∈stabilizer R c) (hxa : act R x d=a) : False := by
  let H := ⁅Z R a,Z R e⁆⊓Z R (p.walk.getVert 1)
  have hne : H≠⊥ := s.critical_commutator_inf_first_seed_ne_bot u hfull p
  have hH : H≤U R a := inf_le_left.trans ((s.critical_Z_commutator_le_moving p).trans inf_le_left)
  have ht : color R (p.walk.getVert 1)=true := by
    have hcol := p.vertex_color (show 1≤p.walk.length by
      have hh : 0<p.walk.length := p.length_eq_b ▸ s.criticalDistance_pos
      omega)
    have hf : ¬color R (p.walk.getVert 1)=false := by
      intro hh
      have he := hcol.mp hh
      norm_num at he
    cases he : color R (p.walk.getVert 1) <;> simp_all
  have hseed (w : Vertex R) (hw : color R w=true) :
      Z R w≤centralizer (Q R w:Set (FreeAmalgam R)) := by
    intro z hz
    rw [Z,if_neg (by simp [hw])] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2
  have hHC : H≤centralizer (stabilizer R c:Set (FreeAmalgam R)) := by
    apply le_centralizer_iff.mp
    rw [←hgenC]
    exact sup_le (le_centralizer_iff.mp (inf_le_right.trans (hseed _ ht)))
      (le_centralizer_iff.mp (inf_le_left.trans hRf))
  have hHv : H≤Z R v := by
    obtain ⟨y,hy,hyt⟩ := stabilizer_transitive_neighbors R c hct hcv
    rw [←hyt,Z_act]
    rw [←central_fixed_map H (stabilizer R c) hHC ((stabilizer R c).inv_mem hy)]
    exact map_mono inf_le_right
  have hc : color R c=false := by
    have hh := adjacent_color_ne R hct
    rw [ht] at hh
    cases he : color R c <;> simp_all
  have hv : color R v=true := by
    have hh := adjacent_color_ne R hcv
    rw [hc] at hh
    cases he : color R v <;> simp_all
  have hHD : H≤centralizer (stabilizer R d:Set (FreeAmalgam R)) := by
    apply le_centralizer_iff.mp
    rw [←hgenD]
    exact sup_le (le_centralizer_iff.mp (hHv.trans (hseed _ hv)))
      (le_centralizer_iff.mp (inf_le_left.trans hRg))
  have hHA : H≤centralizer (stabilizer R a:Set (FreeAmalgam R)) := by
    rw [←hxa,stabilizer_act]
    have hh := (map_mono (f:=(MulAut.conj x⁻¹).toMonoidHom) hHD).trans
      (map_centralizer_le_centralizer_image _ _)
    rwa [central_fixed_map H (stabilizer R c) hHC ((stabilizer R c).inv_mem hx)] at hh
  exact hne (le_bot_iff.mp ((le_inf hH hHA).trans_eq (s.moving_inf_full_centralizer_eq_bot_at h p.start_color)))
private theorem exists_backward_step_base (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2<s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    ∃ t x, x∈stabilizer R (alpha R) ∧ Adjacent R (alpha R) t ∧
      Adjacent R (act R x (p.walk.getVert 2)) t ∧
      Q R t⊔Z R e=stabilizer R (alpha R) ∧
      ¬Z R (act R x (p.walk.getVert 2))≤Q R (p.walk.getVert (p.walk.length-2)) := by
  have hl := p.length_eq_b
  have hd : Adjacent R (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i:=1) (by omega)))
  obtain ⟨c⟩ := s.exists_coordinatedChoice h u hfull p _ hd
  have hi := s.forward_moving_index_two_le h u hfull hb p
  have hc := c.backward_critical_of_eligible s h u hfull hb (by omega)
  refine ⟨c.beta1,c.transporter,c.transporter_mem,c.adjacent_start,?_,?_,?_⟩
  · rw [←c.alpha1_eq]
    exact c.adjacent_back
  · simpa only [s.selectedCriticalLayer_eq h u hfull p] using c.generation
  · simpa only [c.alpha1_eq] using hc.2

private theorem exists_backward_step (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2<s.geometry.b R) {a e : Vertex R}
    (p : CriticalPath R s.geometry a e) :
    ∃ t x, x∈stabilizer R a ∧ Adjacent R a t ∧
      Adjacent R (act R x (p.walk.getVert 2)) t ∧
      Q R t⊔Z R e=stabilizer R a ∧
      ¬Z R (act R x (p.walk.getVert 2))≤Q R (p.walk.getVert (p.walk.length-2)) := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color R p.start_color
  have hbase : act R g⁻¹ (mVertex R g)=alpha R := by
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  have base := s.exists_backward_step_base h u hfull hb (e:=act R g⁻¹ e)
  rw [←hbase] at base
  obtain ⟨t,x,hx,hat,hbt,hgen,hn⟩ := base (p.act g⁻¹)
  change Adjacent R (act R x ((actWalk R g⁻¹ p.walk).getVert 2)) t at hbt
  rw [actWalk_getVert] at hbt
  change ¬Z R (act R x ((actWalk R g⁻¹ p.walk).getVert 2))≤
    Q R ((actWalk R g⁻¹ p.walk).getVert ((actWalk R g⁻¹ p.walk).length-2)) at hn
  rw [actWalk_length,actWalk_getVert,actWalk_getVert] at hn
  let y := g⁻¹*x*g
  have hy (v : Vertex R) : act R y v=act R g (act R x (act R g⁻¹ v)) := by
    simp only [y,act_mul]
  have hc (v : Vertex R) : act R g (act R g⁻¹ v)=v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  refine ⟨act R g t,y,?_,?_,?_,?_,?_⟩
  · change act R y (mVertex R g)=mVertex R g
    rw [hy,show act R x (act R g⁻¹ (mVertex R g))=act R g⁻¹ (mVertex R g) from hx,hc]
  · simpa only [hc] using (adjacent_act_iff R g _ _).mpr hat
  · rw [hy]
    exact (adjacent_act_iff R g _ _).mpr hbt
  · have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hgen
    rw [Subgroup.map_sup,←Q_act,←Z_act,←stabilizer_act,hc,hc] at hh
    exact hh
  · intro hbad
    apply hn
    have hh : (Z R (act R x (act R g⁻¹ (p.walk.getVert 2)))).map
        (MulAut.conj g⁻¹).toMonoidHom≤
        (Q R (act R g⁻¹ (p.walk.getVert (p.walk.length-2)))).map
        (MulAut.conj g⁻¹).toMonoidHom := by
      rw [←Z_act,←Q_act,hc,←hy]
      exact hbad
    exact (map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hh
private theorem exists_backward_path (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2<s.geometry.b R) {a e : Vertex R}
    (p : CriticalPath R s.geometry a e) :
    ∃ a₁ t x, ∃ q : CriticalPath R s.geometry a₁ (p.walk.getVert (p.walk.length-2)),
      x∈stabilizer R a ∧ act R x (p.walk.getVert 2)=a₁ ∧
      Adjacent R a t ∧ Adjacent R a₁ t ∧
      Q R t⊔Z R e=stabilizer R a ∧ q.walk.getVert 1=t ∧ q.walk.getVert 2=a := by
  obtain ⟨t,x,hx,hat,hbt,hgen,hn⟩ := s.exists_backward_step h u hfull hb p
  have hl := p.length_eq_b
  have hc : color R (act R x (p.walk.getVert 2))=false := by
    rw [action_preserves_color]
    exact (p.vertex_color (by omega)).mpr (by decide)
  let w : (cosetGraph R).Walk (act R x (p.walk.getVert 2)) a :=
    .cons ((cosetGraph_adj R _ _).mpr hbt)
      (.cons ((cosetGraph_adj R _ _).mpr (adjacent_symm R hat)) .nil)
  have hw : w.length=2 := rfl
  let q := p.prepend_two (by omega) hc w hw hn
  refine ⟨_,t,x,q,hx,rfl,hat,hbt,hgen,?_,?_⟩
  · simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  · simpa only [SimpleGraph.Walk.getVert_zero] using
      p.prepend_two_overlap (by omega : 2≤s.geometry.b R) hc w hw hn
        (i:=0) (by omega)

/-- The native full point-core source has critical distance at most four. -/
theorem criticalDistance_le_four (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom) :
    s.geometry.b R≤4 := by
  by_contra hbad
  have hb : 4<s.geometry.b R := by omega
  have hb2 : 2<s.geometry.b R := by omega
  obtain ⟨e,⟨p⟩⟩ := CriticalPath.exists_from (R:=R) (geometry:=s.geometry) (a:=alpha R) rfl
  obtain ⟨c,v,x,q,hx,hxc,hdv,hcv,hgenD,hq1,hq2⟩ := s.exists_backward_path h u hfull hb2 p
  obtain ⟨a,t,y,r,hy,hya,hct,hat,hgenC,hr1,hr2⟩ := s.exists_backward_path h u hfull hb2 q
  have hlenP := p.length_eq_b
  have hlenQ := q.length_eq_b
  have hef : (cosetGraph R).dist (q.walk.getVert (q.walk.length-2))
      (p.walk.getVert (p.walk.length-2))=2 := by
    rw [q.dist_end]
    omega
  have hfg : (cosetGraph R).dist (p.walk.getVert (p.walk.length-2)) e=2 := by
    rw [p.dist_end]
    omega
  have heg : (cosetGraph R).dist (q.walk.getVert (q.walk.length-2)) e≤4 := by
    have hh := (cosetGraph_connected R).dist_triangle
      (u:=q.walk.getVert (q.walk.length-2)) (v:=p.walk.getVert (p.walk.length-2)) (w:=e)
    omega
  have hRe : ⁅Z R a,Z R (q.walk.getVert (q.walk.length-2))⁆≤
      Z R (q.walk.getVert (q.walk.length-2)) :=
    ((s.critical_Z_commutator_le_moving r).trans inf_le_right).trans (DistanceEight.U_le_Z R _)
  have hcent (z : Vertex R) (hz : color R z=false)
      (hdist : (cosetGraph R).dist (q.walk.getVert (q.walk.length-2)) z<s.geometry.b R) :
      ⁅Z R a,Z R (q.walk.getVert (q.walk.length-2))⁆≤centralizer (Z R z:Set (FreeAmalgam R)) := by
    apply (hRe.trans (Z_le_Q_of_dist_lt R _ (s.geometry.exists_critical _ r.end_color) ?_)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R z hz)))
    rwa [s.geometry.distance_constant _ r.end_color]
  apply s.false_of_three_shift_generators h u hfull r c v (alpha R)
    (p.walk.getVert (p.walk.length-2)) e
    (by rwa [hr1]) hcv (by rwa [hr1]) hgenD
    (hcent _ q.end_color (by omega)) (hcent _ p.end_color (by omega)) y hy
  simpa only [hq2] using hya
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L⊔d.B:Subgroup K)

/-- The actual characteristic replacement has critical distance at most four,
once its separate alternating-block alternative is excluded. -/
theorem reducedSource_block_or_criticalDistance_le_four
    (r : CharacteristicReduction (L.subgroupOf J) (d.B.subgroupOf J)) :
    IsAlternatingBlock L 6 ∨ ((originalSource d hm).reduce r).geometry.b r.radical≤4 := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock | hfull
  · exact Or.inl hblock
  · right
    let s := (originalSource d hm).reduce r
    have hf : r.radical.map s.projection=Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    exact s.criticalDistance_le_four (reduced_nativeCentralLayer d hm r) _ hf
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
