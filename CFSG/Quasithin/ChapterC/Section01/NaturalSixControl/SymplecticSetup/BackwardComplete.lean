module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.BackwardCritical
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.SmallBackwardInputs
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.SmallEdgeFixed

/-!
# Backward critical pairs on the original symplectic source

For a critical path of length greater than two, the selected backward layer
cannot lie in the kernel at the second predecessor of the endpoint if its
moving layer has Baumann index greater than two. The large-image branch is
already established. In the small-image branch the actual last edge gives a
fixed hyperplane and its moved line. The selected generation makes its fixed
part, joined with the starting layer, normal; the order-eight section bound
places that fixed part in the Baumann subgroup and contradicts the index.

Both branches preserve the same coordinated choice and characteristic
replacement. The final application uses the literal original source.

Source: MS93 (5.7), printed p.919, using (3.3), printed p.866;
Aschbacher--Smith C.1.37 and 13.7.4(1).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative

private theorem abelian_action_preserves_fixed {G : Type*} [Group G]
    (P V A : Subgroup G) (hPV : P ≤ normalizer (V : Set G)) (hA : A ≤ P)
    (hcom : ⁅P,P⁆ ≤ centralizer (V : Set G)) :
    P ≤ normalizer ((V ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
  let f : P →* MulAut V := V.normalizerMonoidHom.comp (inclusion hPV)
  have hf (p q : P) : Commute (f p) (f q) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    ext v
    change ⁅(p:G),(q:G)⁆*(v:G)*⁅(p:G),(q:G)⁆⁻¹ = (v:G)
    rw [←hcom (commutator_mem_commutator p.property q.property) v v.property,
      mul_inv_cancel_right]
  apply le_normalizer_iff.mpr
  intro g hg v hv
  have hgv : g*v*g⁻¹ ∈ V := (mem_normalizer_iff.mp (hPV hg) v).mp hv.1
  refine ⟨hgv,?_⟩
  intro a ha
  have hvfix : f ⟨a,hA ha⟩ ⟨v,hv.1⟩ = (⟨v,hv.1⟩:V) := by
    apply Subtype.ext
    change a*v*a⁻¹ = v
    rw [hv.2 a ha,mul_inv_cancel_right]
  have hh := DFunLike.congr_fun (hf ⟨a,hA ha⟩ ⟨g,hg⟩).eq (⟨v,hv.1⟩:V)
  change f ⟨a,hA ha⟩ (f ⟨g,hg⟩ ⟨v,hv.1⟩) =
    f ⟨g,hg⟩ (f ⟨a,hA ha⟩ ⟨v,hv.1⟩) at hh
  rw [hvfix] at hh
  have he : a*(g*v*g⁻¹)*a⁻¹ = g*v*g⁻¹ := congrArg Subtype.val hh
  exact mul_inv_eq_iff_eq_mul.mp he

open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

theorem edge_derived_le_kernel (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t) :
    ⁅Q R t,Q R t⁆ ≤ Q R a := by
  have hbase : ⁅Q R (beta R),Q R (beta R)⁆ ≤ Q R (alpha R) := by
    rw [Q_beta,Q_alpha R s.two_group s.core_le,←map_commutator]
    apply map_mono
    rw [←s.projection_kernel,←Subgroup.map_eq_bot_iff,map_commutator]
    have he : R.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    rw [he]
    let := pointCore_elementary
    let := IsElementaryAbelian.map (p:=2) (A:=pointCore) (MulAut.conj u).toMonoidHom
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common R a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hbase
    rw [map_commutator,←Q_act,←Q_act] at hh
    simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using hh
  · rw [hg.1] at ha
    cases ha

theorem edge_preserves_layer_centralizer (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ Q R t) :
    Q R t ≤ normalizer ((Z R a ⊓ centralizer (A : Set (FreeAmalgam R)) :
      Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  have hQt : Q R t ≤ stabilizer R a :=
    fun _ hx => hx.2 a (adjacent_symm R hat)
  apply abelian_action_preserves_fixed _ _ A (hQt.trans (Z_normalized R a)) hA
  exact (s.edge_derived_le_kernel u hfull ha hat).trans
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a ha)))
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

private theorem CoordinatedChoice.backward_critical_of_not_le
    (hb : 2 < s.geometry.b R) {e : Vertex R}
    {p : CriticalPath R s.geometry (alpha R) e} {delta : Vertex R}
    (c : s.CoordinatedChoice p delta)
    (hn : ¬ Z R c.alpha1 ≤ Q R (p.walk.getVert (p.walk.length-2))) :
    CriticalPair R c.alpha1 (p.walk.getVert (p.walk.length-2))
      (s.geometry.exists_critical c.alpha1 c.back_color) := by
  have hmin := criticalDistance_le R c.alpha1
    (s.geometry.exists_critical c.alpha1 c.back_color) hn
  have hd := p.dist_start (Nat.sub_le p.walk.length 2)
  have htri : (cosetGraph R).dist c.alpha1 (p.walk.getVert (p.walk.length-2)) ≤
      (cosetGraph R).dist c.alpha1 (alpha R) +
        (cosetGraph R).dist (alpha R) (p.walk.getVert (p.walk.length-2)) :=
    (cosetGraph_connected R).dist_triangle
  have hback := c.back_distance_le_two
  have hlen := p.length_eq_b
  rw [s.geometry.distance_constant c.alpha1 c.back_color] at hmin
  change s.geometry.b R ≤ _ at hmin
  refine ⟨?_,hn⟩
  rw [s.geometry.distance_constant c.alpha1 c.back_color]
  change _ = s.geometry.b R
  omega

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

private theorem normalizes_sup_of_commutator_le {G : Type*} [Group G]
    (A B C : Subgroup G) (hAC : A ≤ normalizer (C : Set G)) (hAB : ⁅A,B⁆ ≤ C) :
    A ≤ normalizer ((B ⊔ C : Subgroup G) : Set G) := by
  rw [le_normalizer_iff]
  intro a ha x hx
  have hm : (B ⊔ C).map (MulAut.conj a).toMonoidHom ≤ B ⊔ C := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rintro _ ⟨b,hb,rfl⟩
      have hc : ⁅a,b⁆ ∈ C := hAB (commutator_mem_commutator ha hb)
      have he : (MulAut.conj a) b = ⁅a,b⁆*b := by
        simp [MulAut.conj_apply,commutatorElement_def,mul_assoc]
      change (MulAut.conj a) b ∈ B ⊔ C
      rw [he]
      exact mul_mem (mem_sup_right hc) (mem_sup_left hb)
    · rw [MulEquiv.toMonoidHom_eq_coe,mem_normalizer_iff_map_conj_eq.mp (hAC ha)]
      exact le_sup_right
  exact hm (mem_map_of_mem (MulAut.conj a).toMonoidHom hx)

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)
variable {e : Vertex R} {p : CriticalPath R s.geometry (alpha R) e} {delta : Vertex R}

theorem CoordinatedChoice.fixed_backward_le_B
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) (c : s.CoordinatedChoice p delta)
    (K : Subgroup (FreeAmalgam R)) (hK : K ≤ Q R c.beta1)
    (hmove : ⁅Z R c.alpha1 ⊓ centralizer (K : Set (FreeAmalgam R)),Z R e⁆ ≤ Z R (alpha R)) :
    Z R c.alpha1 ⊓ centralizer (K : Set (FreeAmalgam R)) ≤
      B R (alpha R) (s.geometry.Z_normal _) := by
  let F := Z R c.alpha1 ⊓ centralizer (K : Set (FreeAmalgam R))
  let H := F ⊔ Z R (alpha R)
  let D := Z R c.alpha1 ⊔ Z R (alpha R)
  have hD : D ≤ V R (alpha R) :=
    sup_le c.back_layer_le_radius (Z_le_VBall R (alpha R) 2)
  have hHD : H ≤ D := sup_le_sup_right inf_le_left _
  have hDV : D ≤ stabilizer R (alpha R) :=
    hD.trans ((V_le_Q R rfl hb).trans (fun _ hx => hx.1))
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite D := Finite.of_injective (inclusion hDV) (inclusion_injective _)
  have hHnorm : stabilizer R (alpha R) ≤ normalizer (H : Set (FreeAmalgam R)) := by
    rw [←c.generation,s.selectedCriticalLayer_eq h u hfull p]
    apply sup_le
    · apply le_trans (le_inf _ _) (normalizer_inf_normalizer_le_normalizer_sup _ _)
      · exact s.edge_preserves_layer_centralizer u hfull c.back_color c.adjacent_back K hK
      · have hQt : Q R c.beta1 ≤ stabilizer R (alpha R) :=
          fun _ hx => hx.2 (alpha R) (adjacent_symm R c.adjacent_start)
        exact hQt.trans (Z_normalized R (alpha R))
    · apply normalizes_sup_of_commutator_le
      · exact (critical_Z_le_stabilizer R s.geometry (alpha R) rfl
          s.criticalDistance_pos p.critical).trans (Z_normalized R (alpha R))
      · rwa [commutator_comm]
  have hi : (Z R (alpha R)).relIndex H ≤ 8 :=
    (relIndex_le_of_le_right hHD index_ne_zero_of_finite).trans
      (c.backward_product_index_le_eight s h u hfull)
  exact le_trans le_sup_left (s.normal_radius_subgroup_le_B_of_index
    (s.projection_surjective_of_radical_image_le_conjugate u hfull.le) hb H
    (hHD.trans hD) hHnorm hi)

theorem CoordinatedChoice.small_false_of_line_and_movement
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) (c : s.CoordinatedChoice p delta)
    (hindex : 2 < (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R delta))
    (K : Subgroup (FreeAmalgam R)) (hK : K ≤ Q R c.beta1)
    (hline : Nat.card (⁅Z R c.alpha1,K⁆ : Subgroup (FreeAmalgam R)) ≤ 2)
    (hmove : ⁅Z R c.alpha1 ⊓ centralizer (K : Set (FreeAmalgam R)),Z R e⁆ ≤ Z R (alpha R)) :
    False := by
  have hA : K ≤ stabilizer R c.alpha1 :=
    hK.trans (fun _ hx => hx.2 c.alpha1 (adjacent_symm R c.adjacent_back))
  exact s.small_backward_contradiction_of_commutator_line h u hfull hb c hindex K hA hline
    (c.fixed_backward_le_B s h u hfull hb K hK hmove)
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

theorem critical_kernel_eq_fixed {a e : Vertex R} (p : CriticalPath R s.geometry a e) :
    Z R e ⊓ Q R a = Z R e ⊓ centralizer (Z R a : Set (FreeAmalgam R)) := by
  apply le_antisymm
  · exact inf_le_inf_left _ (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a p.start_color)))
  · rintro x ⟨hxe,hxc⟩
    refine ⟨hxe,?_⟩
    rw [←s.C_eq_Q a p.start_color]
    exact ⟨critical_Z_le_stabilizer R s.geometry a p.start_color
      (by rw [s.geometry.distance_constant a p.start_color]; exact s.criticalDistance_pos) p.critical hxe,hxc⟩

theorem critical_last_edge_inputs (hb : 2 < s.geometry.b R) {a e : Vertex R}
    (p : CriticalPath R s.geometry a e) :
    Adjacent R e (p.walk.getVert (p.walk.length-1)) ∧
      Q R (p.walk.getVert (p.walk.length-2)) ≤ Q R (p.walk.getVert (p.walk.length-1)) ∧
      Z R a ≤ Q R (p.walk.getVert (p.walk.length-1)) := by
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hct : Adjacent R e (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i:=p.walk.length-1) (by omega)
    have hi : p.walk.length-1+1 = p.walk.length := by omega
    rw [hi,p.walk.getVert_length] at hh
    exact adjacent_symm R ((cosetGraph_adj R _ _).mp hh)
  have ht : color R (p.walk.getVert (p.walk.length-1)) = true := by
    have hh := adjacent_color_ne R hct
    rw [p.end_color] at hh
    cases hc : color R (p.walk.getVert (p.walk.length-1)) <;> simp_all
  have het : Adjacent R (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i:=p.walk.length-2) (by omega)
    have hi : p.walk.length-2+1 = p.walk.length-1 := by omega
    rw [hi] at hh
    exact (cosetGraph_adj R _ _).mp hh
  refine ⟨hct,Q_le_adjacent_h R ht het,?_⟩
  apply Z_le_Q_of_dist_lt R a (s.geometry.exists_critical a p.start_color)
  rw [p.dist_start (Nat.sub_le _ _),s.geometry.distance_constant a p.start_color]
  change p.walk.length-1 < s.geometry.b R
  rw [←p.length_eq_b]
  omega

theorem small_critical_fixedIndex_le_two (h : NativeCentralLayer s) {a e : Vertex R}
    (p : CriticalPath R s.geometry a e)
    (hsmall : (Q R e).relIndex (Z R a) < 4) :
    (centralizer (Z R a : Set (FreeAmalgam R))).relIndex (U R e) ≤ 2 := by
  let := finite_Z R e
  let : Finite (U R e) := Finite.of_injective (inclusion (DistanceEight.U_le_Z R e))
    (inclusion_injective _)
  have hQ : Q R a ≤ centralizer (Z R a : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a p.start_color))
  calc
    (centralizer (Z R a : Set (FreeAmalgam R))).relIndex (U R e) ≤
        (Q R a).relIndex (U R e) := relIndex_le_of_le_left hQ index_ne_zero_of_finite
    _ ≤ (Q R a).relIndex (Z R e) :=
      relIndex_le_of_le_right (DistanceEight.U_le_Z R e) index_ne_zero_of_finite
    _ = 2 := (s.small_critical_indices h p hsmall).2

theorem CoordinatedChoice.small_backward_not_le_of_fixed_edge
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {e : Vertex R}
    {p : CriticalPath R s.geometry (alpha R) e} {delta : Vertex R}
    (c : s.CoordinatedChoice p delta)
    (hindex : 2 < (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R delta))
    (hsmall : (Q R e).relIndex (Z R (alpha R)) < 4)
    (hfixed : let K := Z R e ⊓ centralizer (Z R (alpha R) : Set (FreeAmalgam R))
      ⁅K,Q R (p.walk.getVert (p.walk.length-1))⁆ ≤ ⁅U R e,Z R (alpha R)⁆ ∧
      Q R (p.walk.getVert (p.walk.length-1)) ⊓ centralizer (K : Set (FreeAmalgam R)) ≤
        Q R e ⊔ Z R (alpha R)) :
    ¬ Z R c.alpha1 ≤ Q R (p.walk.getVert (p.walk.length-2)) := by
  intro hbad
  let K := Z R e ⊓ Q R (alpha R)
  have hKfixed : K = Z R e ⊓ centralizer (Z R (alpha R) : Set (FreeAmalgam R)) :=
    s.critical_kernel_eq_fixed p
  change _ ∧ _ at hfixed
  rw [←hKfixed] at hfixed
  have hYt : Z R c.alpha1 ≤ Q R (p.walk.getVert (p.walk.length-1)) :=
    hbad.trans (s.critical_last_edge_inputs hb p).2.1
  have hK : K ≤ Q R c.beta1 := inf_le_right.trans
    (Q_le_adjacent_h R c.edge_color c.adjacent_start)
  have hcomm : ⁅U R e,Z R (alpha R)⁆ ≤ ⁅Z R (alpha R),Z R e⁆ := by
    rw [commutator_comm]
    exact commutator_mono le_rfl (DistanceEight.U_le_Z R e)
  have hcritical_le : ⁅Z R (alpha R),Z R e⁆ ≤ Z R (alpha R) :=
    ((s.critical_Z_commutator_le_moving p).trans inf_le_left).trans
      (DistanceEight.U_le_Z R (alpha R))
  let := finite_Z R (alpha R)
  let : Finite (⁅Z R (alpha R),Z R e⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hcritical_le) (inclusion_injective _)
  apply c.small_false_of_line_and_movement s h u hfull hb hindex K hK
  · have hle : ⁅Z R c.alpha1,K⁆ ≤ ⁅Z R (alpha R),Z R e⁆ := by
      rw [commutator_comm]
      exact ((commutator_mono le_rfl hYt).trans hfixed.1).trans hcomm
    exact (card_le_of_le hle).trans_eq (s.small_critical_commutator_card h p hsmall)
  · have hF : Z R c.alpha1 ⊓ centralizer (K : Set (FreeAmalgam R)) ≤
        Q R e ⊔ Z R (alpha R) :=
      (inf_le_inf_right _ hYt).trans hfixed.2
    have hQ : Q R e ≤ centralizer (Z R e : Set (FreeAmalgam R)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R e p.end_color))
    have hA : Z R (alpha R) ≤ normalizer (Z R e : Set (FreeAmalgam R)) :=
      (Z_le_stabilizer_of_dist_le (alpha R) _ p.critical.1.le).trans (Z_normalized R e)
    have he := commutator_eq_of_centralizing_sup (V:=Z R e) (X:=Z R (alpha R))
      (C:=Q R e) rfl hQ hA
    rw [commutator_comm]
    exact (commutator_mono le_rfl hF).trans (he.symm.le.trans
      (by simpa only [commutator_comm] using hcritical_le))
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

/-- The small-image backward noncontainment, with the two local edge facts
supplied by the natural point-core action. -/
theorem CoordinatedChoice.small_backward_not_le
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {e : Vertex R}
    {p : CriticalPath R s.geometry (alpha R) e} {delta : Vertex R}
    (c : s.CoordinatedChoice p delta)
    (hindex : 2 < (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R delta))
    (hsmall : (Q R e).relIndex (Z R (alpha R)) < 4) :
    ¬ Z R c.alpha1 ≤ Q R (p.walk.getVert (p.walk.length-2)) := by
  apply c.small_backward_not_le_of_fixed_edge s h u hfull hb hindex hsmall
  have hpoint : R.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    simpa only [Model.pointCore_eq_exceptional] using hfull
  have hedge := s.critical_last_edge_inputs hb p
  exact s.small_edge_fixed_at h u hpoint p.end_color hedge.1
    (Z R (alpha R)) hedge.2.2 p.critical.2 (s.small_critical_fixedIndex_le_two h p hsmall)

/-- Both critical-image branches of source (5.7), on the same coordinated
backward vertex. -/
theorem CoordinatedChoice.backward_critical
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {e : Vertex R}
    {p : CriticalPath R s.geometry (alpha R) e} {delta : Vertex R}
    (c : s.CoordinatedChoice p delta)
    (hindex : 2 < (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R delta)) :
    CriticalPair R c.alpha1 (p.walk.getVert (p.walk.length-2))
      (s.geometry.exists_critical c.alpha1 c.back_color) := by
  by_cases hlarge : 4 ≤ (Q R e).relIndex (Z R (alpha R))
  · exact c.large_backward_critical s h u hfull hb (by omega) hlarge
  · exact c.backward_critical_of_not_le s hb
      (c.small_backward_not_le s h u hfull hb hindex (by omega))

/-- The literal source set `A_delta` contains a backward critical vertex. -/
theorem CoordinatedChoice.exists_backward_critical
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {e : Vertex R}
    {p : CriticalPath R s.geometry (alpha R) e} {delta : Vertex R}
    (c : s.CoordinatedChoice p delta)
    (hindex : 2 < (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R delta)) :
    ∃ a ∈ c.backwardVertices, ∃ ha : color R a = false,
      CriticalPair R a (p.walk.getVert (p.walk.length-2))
        (s.geometry.exists_critical a ha) :=
  ⟨c.alpha1,Or.inl rfl,c.back_color,c.backward_critical s h u hfull hb hindex⟩

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L ⊔ d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

/-- The original characteristic replacement discharges the natural layer
and full point-core marking for both branches of the backward critical step. -/
theorem reducedSource_block_or_backward_critical
    (r : CharacteristicReduction (L.subgroupOf J) R) {e : Vertex r.radical}
    {p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e}
    {delta : Vertex r.radical}
    (c : ((originalSource d hm).reduce r).CoordinatedChoice p delta)
    (hb : 2 < ((originalSource d hm).reduce r).geometry.b r.radical)
    (hindex : 2 < (B r.radical (alpha r.radical)
      (((originalSource d hm).reduce r).geometry.Z_normal _)).relIndex (U r.radical delta)) :
    IsAlternatingBlock L 6 ∨
      CriticalPair r.radical c.alpha1 (p.walk.getVert (p.walk.length-2))
        (((originalSource d hm).reduce r).geometry.exists_critical c.alpha1 c.back_color) := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock | hfull
  · exact Or.inl hblock
  · right
    apply c.backward_critical ((originalSource d hm).reduce r)
      (reduced_nativeCentralLayer d hm r) d.relabeler.val⁻¹ _ hb hindex
    simpa only [Model.pointCore_eq_exceptional] using hfull
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
