module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardSpan
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.PointLineKernel
/-!
# Critical spans over a common native edge kernel

A family of radius-two Z-layers incident to equal point-core kernels has
its small critical commutator fixed by that kernel. The opposite critical
layer fixes it as well, so local generation kills it in the moving layer.
The critical commutator bound then places the whole family in B.

A nonzero moving line determines the point-core kernel. Its centralizer
therefore carries the neighboring Z-layer through such a family. If that
layer lies outside B, its centralizer span cannot lie in the critical
predecessor kernel. Forward critical nonnormality supplies the required
noncontainment in the actual source (5.9) configuration.

Source: MS93 (5.9), printed pp.920--922, specialized to the native full
point-core image; the kernel geometry is B.3.4 and Notation 13.2.1.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

private theorem critical_common_kernel_span_le_B
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (t : Vertex R) (hat : Adjacent R (alpha R) t)
    (hgen : Q R t ⊔ Z R e = stabilizer R (alpha R))
    (D : Subgroup (FreeAmalgam R))
    (hDV : D ≤ V R (alpha R))
    (hDpre : D ≤ Q R (p.walk.getVert (p.walk.length-2)))
    (hDN : Q R t ≤ normalizer (D : Set (FreeAmalgam R)))
    (hfix : (Q R e).relIndex (Z R (alpha R)) < 4 →
      ⁅D,Z R e ⊓ Q R (alpha R)⁆ ≤ centralizer (Q R t : Set (FreeAmalgam R))) :
    D ≤ B R (alpha R) (s.geometry.Z_normal _) := by
  let N := D ⊔ Z R (alpha R)
  have hNV : N ≤ V R (alpha R) := sup_le hDV (Z_le_VBall R (alpha R) 2)
  have hpoint : R.map s.projection =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom := by
    simpa only [Model.pointCore_eq_exceptional] using hfull
  have hcom : ⁅D,Z R e⁆ ≤ Z R (alpha R) := by
    by_cases hlarge : 4 ≤ (Q R e).relIndex (Z R (alpha R))
    · exact (commutator_mono (le_inf hDV hDpre) le_rfl).trans
        (s.critical_radius_commutator_le_Z_of_two_lt h u hpoint.le hb p hlarge)
    · have hedge := s.critical_last_edge_inputs hb p
      have hsmall := s.small_edge_fixed_at h u hpoint p.end_color hedge.1
        (Z R (alpha R)) hedge.2.2 p.critical.2
        (s.small_critical_fixedIndex_le_two h p (Nat.lt_of_not_ge hlarge))
      have hK : Z R e ⊓ Q R (alpha R) =
          Z R e ⊓ centralizer (Z R (alpha R) : Set (FreeAmalgam R)) := s.critical_kernel_eq_fixed p
      have hR : ⁅D,Z R e ⊓ Q R (alpha R)⁆ ≤ ⁅Z R (alpha R),Z R e⁆ := by
        rw [commutator_comm]
        have hh := (commutator_mono le_rfl (hDpre.trans hedge.2.1)).trans hsmall.1
        rw [←hK] at hh
        exact hh.trans (by rw [commutator_comm]; exact commutator_mono le_rfl (DistanceEight.U_le_Z R e))
      have hRU := hR.trans ((s.critical_Z_commutator_le_moving p).trans inf_le_left)
      have hRZ := hR.trans ((s.critical_Z_commutator_le_moving p).trans
        (inf_le_right.trans (DistanceEight.U_le_Z R e)))
      have hRcentral : ⁅D,Z R e ⊓ Q R (alpha R)⁆ ≤
          centralizer (stabilizer R (alpha R) : Set (FreeAmalgam R)) := by
        apply le_centralizer_iff.mp
        rw [←hgen]
        apply sup_le (le_centralizer_iff.mp (hfix (Nat.lt_of_not_ge hlarge)))
        let := s.geometry.Z_elementary s.criticalDistance_pos e p.end_color
        exact le_centralizer_iff.mp (hRZ.trans
          (le_centralizer_iff_isMulCommutative.mpr inferInstance))
      have hzero : ⁅D,Z R e ⊓ Q R (alpha R)⁆ = ⊥ := by
        apply le_bot_iff.mp
        rw [←s.movingLayer_inf_stabilizer_center_eq_bot h]
        apply le_inf hRU
        intro z hz
        refine ⟨⟨z,(s.geometry.V_local (alpha R) rfl hb) ((DistanceEight.U_le_Z R _).trans
          (Z_le_VBall R (alpha R) 2) (hRU hz))⟩,?_,rfl⟩
        apply mem_center_iff.mpr
        intro x
        exact Subtype.ext (hRcentral hz x x.property)
      have hDK := commutator_eq_bot_iff_le_centralizer.mp hzero
      have hc : color R (p.walk.getVert (p.walk.length-2)) = false := by
        apply (p.vertex_color (Nat.sub_le _ _)).mpr
        have he := s.geometry.even (alpha R) rfl
        change Even (s.geometry.b R) at he
        rw [Nat.even_iff] at he ⊢
        have hl := p.length_eq_b
        omega
      exact s.critical_commutator_le_start_of_predecessor_fixed h u hfull hb p D hDV
        (hDpre.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q R _ hc)))) hDK

  have hNcom : ⁅N,Z R e⁆ ≤ Z R (alpha R) :=
    commutator_sup_le_of_relative_normal (stabilizer R (alpha R)) D (Z R (alpha R))
      (Z R e) (Z R (alpha R)) (Z_normalized R (alpha R))
      (hDV.trans (s.geometry.V_local (alpha R) rfl hb)) (Z_le_stabilizer R _)
      hcom (((s.critical_Z_commutator_le_moving p).trans inf_le_left).trans (DistanceEight.U_le_Z R _))
  have hNN : stabilizer R (alpha R) ≤ normalizer (N : Set (FreeAmalgam R)) := by
    rw [←hgen]
    apply sup_le
    · have htG : Q R t ≤ stabilizer R (alpha R) := fun _ hx => hx.2 _ (adjacent_symm R hat)
      exact (le_inf hDN (htG.trans (Z_normalized R (alpha R)))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact le_normalizer_iff_commutator_le_left.mpr (hNcom.trans le_sup_right)
  exact le_sup_left.trans (s.normalized_radius_le_B_of_critical_commutator u hfull hb p N hNV hNN hNcom)

private theorem critical_kernel_commutator_card_le_two
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {a e : Vertex R}
    (p : CriticalPath R s.geometry a e)
    (D : Subgroup (FreeAmalgam R))
    (hDpre : D ≤ Q R (p.walk.getVert (p.walk.length-2)))
    (hsmall : (Q R e).relIndex (Z R a) < 4) :
    Nat.card (⁅D,Z R e ⊓ Q R a⁆ : Subgroup (FreeAmalgam R)) ≤ 2 := by
  have hedge := s.critical_last_edge_inputs hb p
  have hpoint : R.map s.projection =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom := by
    simpa only [Model.pointCore_eq_exceptional] using hfull
  have hsmallfix := s.small_edge_fixed_at h u hpoint p.end_color hedge.1
    (Z R a) hedge.2.2 p.critical.2 (s.small_critical_fixedIndex_le_two h p hsmall)
  have hh := (commutator_mono le_rfl (hDpre.trans hedge.2.1)).trans hsmallfix.1
  have hK := s.critical_kernel_eq_fixed p
  have hbnd : ⁅D,Z R e ⊓ Q R a⁆ ≤ ⁅Z R a,Z R e⁆ := by
    rw [commutator_comm]
    rw [←hK] at hh
    exact hh.trans (by rw [commutator_comm]; exact commutator_mono le_rfl (DistanceEight.U_le_Z R e))
  let := finite_Z R a
  let : Finite (⁅Z R a,Z R e⁆ : Subgroup (FreeAmalgam R)) := Finite.of_injective
    (inclusion ((s.critical_Z_commutator_le_moving p).trans
      (inf_le_left.trans (DistanceEight.U_le_Z R a)))) (inclusion_injective _)
  exact (card_le_of_le hbnd).trans_eq (s.small_critical_commutator_card h p hsmall)

private theorem critical_common_edge_seed_family_le_B
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (t : Vertex R) (hat : Adjacent R (alpha R) t)
    (hgen : Q R t ⊔ Z R e = stabilizer R (alpha R))
    {ι : Type*} (v k : ι → Vertex R)
    (hv : ∀ i, color R (v i)=false) (hvk : ∀ i, Adjacent R (v i) (k i))
    (hk : ∀ i, Q R (k i)=Q R t)
    (hDV : (⨆ i,Z R (v i)) ≤ V R (alpha R))
    (hDpre : (⨆ i,Z R (v i)) ≤ Q R (p.walk.getVert (p.walk.length-2)))
    (hDN : Q R t ≤ normalizer ((⨆ i,Z R (v i) : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R))) :
    (⨆ i,Z R (v i)) ≤ B R (alpha R) (s.geometry.Z_normal _) := by
  let D := ⨆ i,Z R (v i)
  have ht : color R t=true := by
    have hn := adjacent_color_ne R hat
    change false≠color R t at hn
    cases hh:color R t <;> simp_all
  have hQt : Q R (alpha R) ≤ Q R t := Q_le_adjacent_h R ht hat
  have hDQ : D ≤ Q R t := hDV.trans ((s.geometry.V_le_Q hb (alpha R) rfl).trans hQt)
  apply s.critical_common_kernel_span_le_B h u hfull hb p t hat hgen D hDV hDpre hDN
  intro hsmall
  have hc := s.critical_kernel_commutator_card_le_two h u hfull hb p D hDpre hsmall
  let K := Z R e ⊓ Q R (alpha R)
  have hKQt : K ≤ Q R t := inf_le_right.trans hQt
  have hDG : D ≤ stabilizer R e :=
    (hDpre.trans (s.critical_last_edge_inputs hb p).2.1).trans
      (show Q R (p.walk.getVert (p.walk.length-1)) ≤ stabilizer R e from
        fun _ hx => hx.2 _ (adjacent_symm R (s.critical_last_edge_inputs hb p).1))
  have hRZ : ⁅D,K⁆ ≤ Z R e :=
    (commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp (hDG.trans (Z_normalized R e)))
  let := finite_Z R e
  let : Finite (⁅D,K⁆ : Subgroup (FreeAmalgam R)) := Finite.of_injective
    (inclusion hRZ) (inclusion_injective _)
  apply commutator_iSup_le_of_relative_normal (Q R t) K
    (centralizer (Q R t : Set (FreeAmalgam R))) (fun i => Z R (v i))
    ((le_centralizer_iff.mp le_rfl).trans (Subgroup.centralizer_le_normalizer _))
    (fun i => (le_iSup (fun i => Z R (v i)) i).trans hDQ)
  intro i
  have hsmalli : Nat.card (⁅Z R (v i),K⁆ : Subgroup (FreeAmalgam R)) ≤ 2 :=
    (card_le_of_le (commutator_mono (le_iSup (fun i => Z R (v i)) i) le_rfl)).trans hc
  rw [←hk i]
  exact s.small_edge_commutator_le_centralizer u hfull (hv i) (hvk i) K
    (by rwa [hk i]) hsmalli


private theorem critical_common_edge_seed_family_le_B_at
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {a e : Vertex R} (ha : color R a=false)
    (p : CriticalPath R s.geometry a e)
    (t : Vertex R) (hat : Adjacent R a t)
    (hgen : Q R t ⊔ Z R e = stabilizer R a)
    {ι : Type*} (v k : ι → Vertex R)
    (hv : ∀ i, color R (v i)=false) (hvk : ∀ i, Adjacent R (v i) (k i))
    (hk : ∀ i, Q R (k i)=Q R t)
    (hDV : (⨆ i,Z R (v i)) ≤ V R a)
    (hDpre : (⨆ i,Z R (v i)) ≤ Q R (p.walk.getVert (p.walk.length-2)))
    (hDN : Q R t ≤ normalizer ((⨆ i,Z R (v i) : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R))) :
    (⨆ i,Z R (v i)) ≤ B R a (s.geometry.Z_normal _) := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color R ha
  have hbase : act R g⁻¹ (mVertex R g)=alpha R := by
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  let j := (MulAut.conj (g⁻¹)⁻¹).toMonoidHom
  have hspan : (⨆ i,Z R (act R g⁻¹ (v i))) = (⨆ i,Z R (v i)).map j := by
    simp only [Z_act,Subgroup.map_iSup,j]
  have base := s.critical_common_edge_seed_family_le_B h u hfull hb (e:=act R g⁻¹ e)
  rw [←hbase] at base
  have hh := base (p.act g⁻¹) (act R g⁻¹ t) ((adjacent_act_iff R _ _ _).mpr hat)
    (by rw [Q_act,Z_act,stabilizer_act,←Subgroup.map_sup,hgen])
    (fun i => act R g⁻¹ (v i)) (fun i => act R g⁻¹ (k i))
    (fun i => by rw [action_preserves_color]; exact hv i)
    (fun i => (adjacent_act_iff R _ _ _).mpr (hvk i))
    (fun i => by rw [Q_act,Q_act,hk i])
    (by rw [hspan,V_act]; exact map_mono hDV)
    (by
      change (⨆ i,Z R (act R g⁻¹ (v i)))≤Q R
        ((actWalk R g⁻¹ p.walk).getVert ((actWalk R g⁻¹ p.walk).length-2))
      rw [hspan,actWalk_length,actWalk_getVert,Q_act]
      exact map_mono hDpre)
    (by
      rw [hspan,Q_act]
      exact (map_mono hDN).trans ((⨆ i,Z R (v i)).le_normalizer_map j))
  rw [hspan,Escape.PairingControl.FirstPairing.B_act hb g⁻¹ (mVertex R g) ha] at hh
  exact (map_le_map_iff_of_injective (MulAut.conj (g⁻¹)⁻¹).injective).mp hh

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


theorem critical_start_not_le_forward_B
    (hb : 2 < s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    ¬Z R (alpha R)≤B R (p.walk.getVert 2) (s.geometry.Z_normal _) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  have hl : 2<p.walk.length := p.length_eq_b ▸ hb
  have hc : color R c=false := (p.vertex_color (by omega)).mpr (by decide)
  have hac : (cosetGraph R).dist (alpha R) c=2 := p.dist_start (by omega)
  have hat : Adjacent R (alpha R) t := by
    apply (cosetGraph_adj R _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) (by omega)
  have hct : Adjacent R c t := adjacent_symm R ((cosetGraph_adj R _ _).mp
    (p.walk.adj_getVert_succ (i:=1) (by omega)))
  have hpath : (cosetGraph R).dist c e+2=(cosetGraph R).dist (alpha R) e := by
    rw [p.dist_end,←p.shortest]
    omega
  have hn := (critical_nonnormal_forward R s.geometry s.edgeCentralizerCondition
    (alpha R) rfl s.criticalDistance_pos e p.critical c hac hpath).2
  intro hZB
  apply hn
  apply normal_subgroupOf_of_le_normalizer
  rw [←s.residual_edge_generation hc hct,sup_comm (Z R (alpha R)) (X R c)]
  apply sup_le
  · apply normalizes_join_of_displacement
    · exact (Ltilde_le_stabilizer c).trans (X_normalized R c)
    · apply commutator_le.mpr
      intro l hl x hx
      have hZcX : Z R c≤X R c := s.geometry.omega_bound c hc (by
        rw [s.geometry.distance_constant c hc]
        exact s.criticalDistance_pos)
      exact hZcX (((mem_B_iff R c _ (s.geometry.V_local c hc (by
        rw [s.geometry.distance_constant c hc]
        exact hb)) x).mp (hZB hx)).2 l hl)
  · have htG : Q R t≤stabilizer R (alpha R) := fun _ hx => hx.2 _ (adjacent_symm R hat)
    have htC : Q R t≤stabilizer R c := fun _ hx => hx.2 _ (adjacent_symm R hct)
    exact (le_inf (htC.trans (X_normalized R c)) (htG.trans (Z_normalized R _))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)


theorem critical_moving_line_span_not_le_predecessor
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2<s.geometry.b R) {a e : Vertex R} (ha : color R a=false)
    (p : CriticalPath R s.geometry a e)
    (t : Vertex R) (hat : Adjacent R a t)
    (hgen : Q R t⊔Z R e=stabilizer R a)
    (mu k : Vertex R) (hmu : color R mu=false)
    (hmak : Adjacent R mu k) (hak : Adjacent R a k)
    (hmuV : Z R mu≤V R a) (hmuB : ¬Z R mu≤B R a (s.geometry.Z_normal _))
    (H : Subgroup (FreeAmalgam R)) (hH : H≤U R a⊓Z R t) (hHne : H≠⊥)
    (hHk : H≤Z R k) :
    ¬conjugateSpanBy (Z R mu) (stabilizer R a⊓centralizer (H:Set (FreeAmalgam R)))≤
      Q R (p.walk.getVert (p.walk.length-2)) := by
  let P := stabilizer R a⊓centralizer (H:Set (FreeAmalgam R))
  let D := conjugateSpanBy (Z R mu) P
  let v : P→Vertex R := fun x => act R (x:FreeAmalgam R)⁻¹ mu
  let k' : P→Vertex R := fun x => act R (x:FreeAmalgam R)⁻¹ k
  have hkeq : Q R k=Q R t := s.edge_kernel_eq_of_common_moving_line h u hfull ha hat hak H hH hHne hHk
  have hPN : P≤normalizer (Q R t:Set (FreeAmalgam R)) :=
    s.edge_line_centralizer_normalizes_kernel h u hfull ha hat H hH hHne
  have ht : color R t=true := by
    have hh := adjacent_color_ne R hat
    rw [ha] at hh
    cases he:color R t <;> simp_all
  have hHC : H≤centralizer (Q R t:Set (FreeAmalgam R)) := by
    apply (hH.trans inf_le_right).trans
    intro z hz
    rw [Z,if_neg (by rw [ht]; decide)] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2
  have hQtP : Q R t≤P := le_inf (fun _ hx => hx.2 _ (adjacent_symm R hat))
    (le_centralizer_iff.mp hHC)
  have hD : (⨆ x,Z R (v x))=D := by
    change (⨆ x,Z R (v x))=conjugateSpanBy (Z R mu) P
    rw [conjugateSpanBy_eq_iSup_conj]
    simp only [v,Z_act,inv_inv]
  intro hDpre
  apply hmuB
  apply (le_conjugateSpanBy (Z R mu) P).trans
  change D≤B R a (s.geometry.Z_normal _)
  rw [←hD]
  apply s.critical_common_edge_seed_family_le_B_at h u hfull hb ha p t hat hgen v k'
    (fun x => by simp only [v,action_preserves_color,hmu])
    (fun x => (adjacent_act_iff R _ _ _).mpr hmak)
  · intro x
    change Q R (act R (x:FreeAmalgam R)⁻¹ k)=Q R t
    rw [Q_act,inv_inv,hkeq]
    exact mem_normalizer_iff_map_conj_eq.mp (hPN x.property)
  · rw [hD]
    exact conjugateSpanBy_le hmuV (inf_le_left.trans (V_normalized a))
  · rwa [hD]
  · rw [hD]
    exact hQtP.trans (le_normalizer_conjugateSpanBy _ _)

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
