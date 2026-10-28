module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardKernel
public import Theory.GroupTheory.Commutator.NormalClosure
/-!
# Forward-kernel closure in the native symplectic source

The layers two steps before a critical endpoint lie in the forward hyperplane
kernel. A subgroup of the initial radius layer which centralizes these inner
layers has its critical commutator in the starting seed. This follows from
the large-image bound or the small-image pointwise fixer, respectively.

Taking a normal closure under a line centralizer then rules out a line which
both generates the initial stabilizer with the opposite seed and fails to
centralize that seed. This is the closure argument in the first paragraph of
Meierfrankenfeld--Stellmacher (1993), (5.9), printed pp.920--921. Its applications
supply the actual forward-kernel line and its conjugate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise

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

private theorem exists_normal_span_with_commutator {G : Type*} [Group G]
    (P A T D V : Subgroup G) (hAP : A ≤ P) (hAV : A ≤ V)
    (hTP : T ≤ P) (hDP : D ≤ P)
    (hPT : P ≤ normalizer (T : Set G)) (hPD : P ≤ normalizer (D : Set G))
    (hPV : P ≤ normalizer (V : Set G)) (hcomm : ⁅A,T⁆ ≤ D) :
    ∃ Y : Subgroup G, A ≤ Y ∧ Y ≤ V ∧ P ≤ normalizer (Y : Set G) ∧ ⁅Y,T⁆ ≤ D := by
  let Y₀ := normalClosure (A.subgroupOf P : Set P)
  let Y := Y₀.map P.subtype
  let : (T.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hPT
  let : (D.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hPD
  let : (V.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hPV
  have hAY : A ≤ Y := by
    intro a ha
    exact ⟨⟨a,hAP ha⟩,subset_normalClosure ha,rfl⟩
  have hYV : Y ≤ V := by
    apply map_le_iff_le_comap.mpr
    change Y₀ ≤ V.subgroupOf P
    exact normalClosure_le_normal (fun a ha => hAV ha)
  have hPY : P ≤ normalizer (Y : Set G) := by
    have hh := Y₀.le_normalizer_map P.subtype
    intro p hp
    apply hh
    exact ⟨⟨p,hp⟩,by rw [normalizer_eq_top]; exact mem_top _,rfl⟩
  have hcomm₀ : ⁅T.subgroupOf P,A.subgroupOf P⁆ ≤ D.subgroupOf P := by
    apply commutator_le.mpr
    intro t ht a ha
    change ⁅(t:G),(a:G)⁆ ∈ D
    rw [commutator_comm] at hcomm
    exact hcomm (commutator_mem_commutator ht ha)
  have hm := map_mono (f := P.subtype) (commutator_normalClosure_le_of_normal
    (T.subgroupOf P) (A.subgroupOf P) (D.subgroupOf P) hcomm₀)
  rw [map_commutator,map_subgroupOf_eq_of_le hTP,map_subgroupOf_eq_of_le hDP,
    commutator_comm] at hm
  exact ⟨Y,hAY,hYV,hPY,hm⟩

open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

theorem critical_radius_le_predecessor_stabilizer (hb : 2 < s.geometry.b R)
    {e : Vertex R} (p : CriticalPath R s.geometry (alpha R) e) :
    V R (alpha R) ≤ stabilizer R (p.walk.getVert (p.walk.length-2)) := by
  apply (V_le_iff R rfl _).mpr
  intro d hd hdist
  apply Z_le_stabilizer_of_dist_le d (s.geometry.exists_critical d hd)
  rw [s.geometry.distance_constant d hd]
  change (cosetGraph R).dist d (p.walk.getVert (p.walk.length-2)) ≤ s.geometry.b R
  have ht := (cosetGraph_connected R).dist_triangle (u:=d) (v:=alpha R)
    (w:=p.walk.getVert (p.walk.length-2))
  rw [p.dist_start (Nat.sub_le _ _)] at ht
  have hl := p.length_eq_b
  omega

theorem critical_commutator_le_start_of_predecessor_fixed
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (Y : Subgroup (FreeAmalgam R)) (hYV : Y ≤ V R (alpha R))
    (hYc : Y ≤ centralizer
      (Z R (p.walk.getVert (p.walk.length-2)) : Set (FreeAmalgam R)))
    (hYK : Y ≤ centralizer (Z R e ⊓ Q R (alpha R) : Set (FreeAmalgam R))) :
    ⁅Y,Z R e⁆ ≤ Z R (alpha R) := by
  have hc : color R (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := s.geometry.even (alpha R) rfl
    change Even (s.geometry.b R) at he
    rw [←p.length_eq_b,Nat.even_iff] at he
    rw [Nat.even_iff]
    omega
  have hYQ : Y ≤ Q R (p.walk.getVert (p.walk.length-2)) := by
    rw [←s.C_eq_Q _ hc]
    exact le_inf (hYV.trans (s.critical_radius_le_predecessor_stabilizer hb p)) hYc
  have hpoint : R.map s.projection =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom := by
    simpa only [Model.pointCore_eq_exceptional] using hfull
  by_cases hlarge : 4 ≤ (Q R e).relIndex (Z R (alpha R))
  · exact (commutator_mono (le_inf hYV hYQ) le_rfl).trans
      (s.critical_radius_commutator_le_Z_of_two_lt h u hpoint.le hb p hlarge)
  · have hedge := s.critical_last_edge_inputs hb p
    have hfix := (s.small_edge_fixed_at h u hpoint p.end_color hedge.1
      (Z R (alpha R)) hedge.2.2 p.critical.2
      (s.small_critical_fixedIndex_le_two h p (Nat.lt_of_not_ge hlarge))).2
    change Q R (p.walk.getVert (p.walk.length-1)) ⊓ centralizer
      (Z R e ⊓ centralizer (Z R (alpha R) : Set (FreeAmalgam R)) :
        Set (FreeAmalgam R)) ≤ Q R e ⊔ Z R (alpha R) at hfix
    have hCK := congrArg (fun D : Subgroup (FreeAmalgam R) =>
      centralizer (D : Set (FreeAmalgam R))) (s.critical_kernel_eq_fixed p)
    have hY : Y ≤ Q R e ⊔ Z R (alpha R) :=
      (le_inf (hYQ.trans hedge.2.1) (hYK.trans hCK.le)).trans hfix
    have hZaGe : Z R (alpha R) ≤ stabilizer R e :=
      Z_le_stabilizer_of_dist_le (alpha R) _ p.critical.1.le
    have hQe : Q R e ≤ centralizer (Z R e : Set (FreeAmalgam R)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q R e p.end_color))
    have heq := commutator_sup_centralized_left (Q R e) (Z R (alpha R)) (Z R e)
      (hZaGe.trans (Q_normalized R e)) hQe (hZaGe.trans (Z_normalized R e))
    exact ((commutator_mono hY le_rfl).trans_eq heq).trans
      ((s.critical_Z_commutator_le_moving p).trans inf_le_left |>.trans
        (DistanceEight.U_le_Z R (alpha R)))


theorem critical_forward_kernel_contains_inner_layers
    (hb : 4 < s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    Z R (p.walk.getVert (p.walk.length-2)) ⊔ (Z R e ⊓ Q R (alpha R)) ≤
      Q R (alpha R) ⊓ centralizer
        (U R (p.walk.getVert 2) ⊓ B R (alpha R) (s.geometry.Z_normal _) :
          Set (FreeAmalgam R)) := by
  have hl := p.length_eq_b
  have hc : color R (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := s.geometry.even (alpha R) rfl
    change Even (s.geometry.b R) at he
    rw [Nat.even_iff] at he ⊢
    omega
  have hd : color R (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega : 2 ≤ p.walk.length)).mpr (by decide)
  have hcd : (cosetGraph R).dist (p.walk.getVert 2)
      (p.walk.getVert (p.walk.length-2)) ≤ p.walk.length-4 := by
    have hh := SimpleGraph.dist_le ((p.walk.drop 2).take (p.walk.length-4))
    rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length,
      inf_eq_left.mpr (by omega : p.walk.length-4 ≤ p.walk.length-2),
      SimpleGraph.Walk.drop_getVert,show 2+(p.walk.length-4)=p.walk.length-2 by omega] at hh
    exact hh
  have hQc : Z R (p.walk.getVert (p.walk.length-2)) ≤ Q R (alpha R) := by
    apply Z_le_Q_of_dist_lt R _ (s.geometry.exists_critical _ hc)
    rw [s.geometry.distance_constant _ hc,SimpleGraph.dist_comm,
      p.dist_start (Nat.sub_le _ _)]
    change p.walk.length-2 < s.geometry.b R
    omega
  have hdc : Z R (p.walk.getVert (p.walk.length-2)) ≤ Q R (p.walk.getVert 2) := by
    apply Z_le_Q_of_dist_lt R _ (s.geometry.exists_critical _ hc)
    rw [s.geometry.distance_constant _ hc,SimpleGraph.dist_comm]
    change (cosetGraph R).dist (p.walk.getVert 2) (p.walk.getVert (p.walk.length-2)) < s.geometry.b R
    omega
  have hde : Z R e ≤ Q R (p.walk.getVert 2) := by
    apply Z_le_Q_of_dist_lt R e (s.geometry.exists_critical e p.end_color)
    rw [s.geometry.distance_constant e p.end_color,SimpleGraph.dist_comm,p.dist_end]
    change p.walk.length-2 < s.geometry.b R
    omega
  have hcentral : Q R (p.walk.getVert 2) ≤ centralizer
      (U R (p.walk.getVert 2) ⊓ B R (alpha R) (s.geometry.Z_normal _) :
        Set (FreeAmalgam R)) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q R _ hd))).trans
      (centralizer_le (inf_le_left.trans (DistanceEight.U_le_Z R _)))
  exact le_inf (sup_le hQc inf_le_right)
    ((sup_le hdc (inf_le_left.trans hde)).trans hcentral)


theorem critical_controlled_line_false
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 4 < s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (A T₀ H₁ : Subgroup (FreeAmalgam R))
    (hAV : A ≤ V R (alpha R)) (hAB : ¬ A ≤ B R (alpha R) (s.geometry.Z_normal _))
    (hTQ : T₀ ≤ Q R (alpha R))
    (hTN : stabilizer R (alpha R) ≤ normalizer (T₀ : Set (FreeAmalgam R)))
    (hHZ : H₁ ≤ Z R (alpha R)) (hcard : Nat.card H₁ ≤ 2)
    (hHe : ¬ H₁ ≤ centralizer (Z R e : Set (FreeAmalgam R)))
    (hgen : (stabilizer R (alpha R) ⊓ centralizer (H₁ : Set (FreeAmalgam R))) ⊔
      Z R e = stabilizer R (alpha R))
    (hcomm : ⁅A,T₀⁆ ≤ H₁)
    (hinner : Z R (p.walk.getVert (p.walk.length-2)) ⊔ (Z R e ⊓ Q R (alpha R)) ≤ T₀) :
    False := by
  have hb2 : 2 < s.geometry.b R := by omega
  let P := stabilizer R (alpha R) ⊓ centralizer (H₁ : Set (FreeAmalgam R))
  have hVQ := s.geometry.V_le_Q hb2 (alpha R) rfl
  have hVG := s.geometry.V_local (alpha R) rfl hb2
  have hZQ : Z R (alpha R) ≤ centralizer (Q R (alpha R) : Set (FreeAmalgam R)) :=
    commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R (alpha R) rfl)
  have hQH : Q R (alpha R) ≤ centralizer (H₁ : Set (FreeAmalgam R)) :=
    (le_centralizer_iff.mp hZQ).trans (centralizer_le hHZ)
  have hZaV : Z R (alpha R) ≤ V R (alpha R) := by
    exact le_iSup_of_le (alpha R) (le_iSup_of_le (by simp :
      (cosetGraph R).dist (alpha R) (alpha R) ≤ 2) le_rfl)
  have hAZ : ⁅Z R (alpha R) ⊔ A,T₀⁆ ≤ H₁ := by
    rw [commutator_sup_centralized_left (Z R (alpha R)) A T₀
      ((hAV.trans hVG).trans (Z_normalized R (alpha R)))
      (hZQ.trans (centralizer_le hTQ)) ((hAV.trans hVG).trans hTN)]
    exact hcomm
  have hAP : Z R (alpha R) ⊔ A ≤ P :=
    le_inf ((sup_le hZaV hAV).trans hVG)
      ((sup_le hZaV hAV).trans (hVQ.trans hQH))
  have hTP : T₀ ≤ P := le_inf (hTQ.trans (fun _ hx => hx.1)) (hTQ.trans hQH)
  have hHP : H₁ ≤ P := le_inf (hHZ.trans (Z_le_stabilizer R (alpha R)))
    (hHZ.trans (hZaV.trans (hVQ.trans hQH)))
  obtain ⟨Y,hAY,hYV,hPY,hYT⟩ := exists_normal_span_with_commutator
    P (Z R (alpha R) ⊔ A) T₀ H₁ (V R (alpha R)) hAP (sup_le hZaV hAV) hTP hHP
    (inf_le_left.trans hTN) (inf_le_right.trans (centralizer_le_normalizer H₁))
    (inf_le_left.trans (DistanceEight.V_normalized R (alpha R))) hAZ
  let F := Z R (p.walk.getVert (p.walk.length-2)) ⊔ (Z R e ⊓ Q R (alpha R))
  have hc : color R (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := s.geometry.even (alpha R) rfl
    change Even (s.geometry.b R) at he
    rw [Nat.even_iff] at he ⊢
    have hl := p.length_eq_b
    omega
  have hFVc : F ≤ V R (p.walk.getVert (p.walk.length-2)) := by
    refine sup_le ?_ (inf_le_left.trans ?_)
    · exact le_iSup_of_le _ (le_iSup_of_le (by simp :
        (cosetGraph R).dist (p.walk.getVert (p.walk.length-2))
          (p.walk.getVert (p.walk.length-2)) ≤ 2) le_rfl)
    · refine le_iSup_of_le e (le_iSup_of_le ?_ le_rfl)
      rw [SimpleGraph.dist_comm,p.dist_end]
      omega
  have hYFVc : ⁅Y,F⁆ ≤ V R (p.walk.getVert (p.walk.length-2)) :=
    (commutator_mono le_rfl hFVc).trans
      (le_normalizer_iff_commutator_le_right.mp
        ((hYV.trans (s.critical_radius_le_predecessor_stabilizer hb2 p)).trans
          (DistanceEight.V_normalized R _)))
  have hVcQe : V R (p.walk.getVert (p.walk.length-2)) ≤ Q R e := by
    apply V_le_Q_of_dist_add_two_lt R hc
    rw [p.dist_end]
    have hl := p.length_eq_b
    omega
  have hQeC : Q R e ≤ centralizer (Z R e : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q R e p.end_color))
  have hYF : ⁅Y,F⁆ = ⊥ := by
    by_contra hn
    let := finite_Z R (alpha R)
    let : Finite H₁ := Finite.of_injective (inclusion hHZ) (inclusion_injective _)
    have hle : ⁅Y,F⁆ ≤ H₁ := (commutator_mono le_rfl hinner).trans hYT
    let : Finite (⁅Y,F⁆ : Subgroup (FreeAmalgam R)) :=
      Finite.of_injective (inclusion hle) (inclusion_injective _)
    have hpos := (one_lt_card_iff_ne_bot (⁅Y,F⁆ : Subgroup (FreeAmalgam R))).mpr hn
    have he : ⁅Y,F⁆ = H₁ := eq_of_le_of_card_ge hle (by omega)
    exact hHe (he ▸ hYFVc.trans (hVcQe.trans hQeC))
  have hYfix := commutator_eq_bot_iff_le_centralizer.mp hYF
  have hYe : ⁅Y,Z R e⁆ ≤ Z R (alpha R) :=
    s.critical_commutator_le_start_of_predecessor_fixed h u hfull hb2 p Y hYV
      (hYfix.trans (centralizer_le (show Z R (p.walk.getVert (p.walk.length-2)) ≤ F from le_sup_left)))
      (hYfix.trans (centralizer_le (show (Z R e ⊓ Q R (alpha R) :
        Subgroup (FreeAmalgam R)) ≤ F from le_sup_right)))
  have hZeY : Z R e ≤ normalizer (Y : Set (FreeAmalgam R)) :=
    le_normalizer_iff_commutator_le_left.mpr (hYe.trans (le_sup_left.trans hAY))
  have hGY : stabilizer R (alpha R) ≤ normalizer (Y : Set (FreeAmalgam R)) := by
    rw [←hgen]
    exact sup_le hPY hZeY
  exact hAB (le_sup_right.trans (hAY.trans
    (s.normalized_radius_le_B_of_critical_commutator u hfull hb2 p Y hYV hGY hYe)))
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
