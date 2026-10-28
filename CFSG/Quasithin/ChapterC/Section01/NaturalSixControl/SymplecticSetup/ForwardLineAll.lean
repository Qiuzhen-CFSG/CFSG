module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardFixedLine

/-!
# The forward fixed line at every nonminimal critical distance

The line-centralizer closure argument needs only critical distance greater
than two. First its commutator with the predecessor seed lies both in the
controlled line and in a subgroup centralizing the opposite seed, so it
vanishes. The closure then enters the predecessor kernel. Its commutator
with the opposite critical kernel now lies in the abelian opposite seed,
and the same line argument makes this commutator vanish as well.

Consequently the forward hyperplane-kernel commutator lies in the starting
fixed core also at distance four. This supplies the fixed-line input to the
terminal MS93 (5.12) argument, using the closure mechanism of (5.9), printed
pp.920--921, without the unnecessary strict distance-four bound.
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

private theorem centralizer_line_eq_singleton {G : Type*} [Group G]
    (H : Subgroup G) [Finite H] (hcard : Nat.card H ≤ 2)
    {z : G} (hz : z ∈ H) (hzn : z ≠ 1) :
    centralizer (H : Set G) = centralizer ({z} : Set G) := by
  have hne : H ≠ ⊥ := by intro he; exact hzn (mem_bot.mp (he ▸ hz))
  have hpos := (one_lt_card_iff_ne_bot H).mpr hne
  obtain ⟨w,hw,huniq⟩ := (Nat.card_eq_two_iff' (1:H)).mp (by omega)
  have hz' : (⟨z,hz⟩:H) ≠ 1 := fun he => hzn (congrArg Subtype.val he)
  apply le_antisymm (centralizer_le (Set.singleton_subset_iff.mpr hz))
  intro x hx y hy
  by_cases he : y=1
  · simp [he]
  · have hy' : (⟨y,hy⟩:H) ≠ 1 := fun hh => he (congrArg Subtype.val hh)
    have heq : y=z := congrArg Subtype.val ((huniq _ hy').trans (huniq _ hz').symm)
    exact heq ▸ hx z (Set.mem_singleton _)

open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

theorem critical_forward_kernel_contains_inner_layers_of_two_lt
    (hb : 2 < s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    Z R (p.walk.getVert (p.walk.length-2)) ⊔ (Z R e ⊓ Q R (alpha R)) ≤
      Q R (alpha R) ⊓ centralizer
        (U R (p.walk.getVert 2) ⊓ B R (alpha R) (s.geometry.Z_normal _) :
          Set (FreeAmalgam R)) := by
  have hl := p.length_eq_b
  have hb4 : 4 ≤ p.walk.length := by
    have he := s.geometry.even (alpha R) rfl
    change Even (s.geometry.b R) at he
    rw [Nat.even_iff] at he
    omega
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


theorem critical_controlled_line_false_of_two_lt
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {e : Vertex R}
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
  have hQeC : Q R e ≤ centralizer (Z R e : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q R e p.end_color))
  have hpreQe : Z R (p.walk.getVert (p.walk.length-2)) ≤ Q R e := by
    apply Z_le_Q_of_dist_lt R _ (s.geometry.exists_critical _ hc)
    rw [s.geometry.distance_constant _ hc,p.dist_end]
    have hl := p.length_eq_b
    change p.walk.length-(p.walk.length-2) < s.geometry.b R
    omega
  have hkill (D : Subgroup (FreeAmalgam R)) (hDH : D ≤ H₁)
      (hDe : D ≤ centralizer (Z R e : Set (FreeAmalgam R))) : D = ⊥ := by
    by_contra hn
    let := finite_Z R (alpha R)
    let : Finite H₁ := Finite.of_injective (inclusion hHZ) (inclusion_injective _)
    let : Finite D := Finite.of_injective (inclusion hDH) (inclusion_injective _)
    have hpos := (one_lt_card_iff_ne_bot D).mpr hn
    have he : D = H₁ := eq_of_le_of_card_ge hDH (by omega)
    exact hHe (he ▸ hDe)
  have hYpre : ⁅Y,Z R (p.walk.getVert (p.walk.length-2))⁆ = ⊥ := by
    apply hkill _ ((commutator_mono le_rfl (le_sup_left.trans hinner)).trans hYT)
    exact (le_normalizer_iff_commutator_le_right.mp
      ((hYV.trans (s.critical_radius_le_predecessor_stabilizer hb p)).trans
        (Z_normalized R _))).trans (hpreQe.trans hQeC)
  have hYpreC := commutator_eq_bot_iff_le_centralizer.mp hYpre
  have hYpreQ : Y ≤ Q R (p.walk.getVert (p.walk.length-2)) := by
    rw [←s.C_eq_Q _ hc]
    exact le_inf (hYV.trans (s.critical_radius_le_predecessor_stabilizer hb p)) hYpreC
  have hYeG : Y ≤ stabilizer R e := by
    have hedge := s.critical_last_edge_inputs hb p
    exact (hYpreQ.trans hedge.2.1).trans (fun _ hx => hx.2 _ (adjacent_symm R hedge.1))
  have hYK : ⁅Y,Z R e ⊓ Q R (alpha R)⁆ = ⊥ := by
    let := s.geometry.Z_elementary s.criticalDistance_pos e p.end_color
    apply hkill _ ((commutator_mono le_rfl (le_sup_right.trans hinner)).trans hYT)
    exact ((commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp (hYeG.trans (Z_normalized R e)))).trans
        (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hYfix : Y ≤ centralizer (F : Set (FreeAmalgam R)) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp hYpreC)
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hYK))
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
theorem critical_forward_commutator_le_fixedCore_of_two_lt
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (hindex : (B R (alpha R) (s.geometry.Z_normal _)).relIndex
      (U R (p.walk.getVert 2)) ≤ 2) :
    let T₀ := Q R (alpha R) ⊓ centralizer
      (U R (p.walk.getVert 2) ⊓ B R (alpha R) (s.geometry.Z_normal _) : Set (FreeAmalgam R))
    ⁅U R (p.walk.getVert 2),T₀⁆ ≤ fixedCore R (alpha R) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T₀ := Q R (alpha R) ⊓ centralizer
    (U R c ⊓ B R (alpha R) (s.geometry.Z_normal _) : Set (FreeAmalgam R))
  let H := ⁅U R c,T₀⁆
  change H ≤ fixedCore R (alpha R)
  have hb2 : 2 < s.geometry.b R := by omega
  have hl := p.length_eq_b
  have hc : color R c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent R (alpha R) t := by
    apply (cosetGraph_adj R _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) (by omega)
  have hct : Adjacent R c t := adjacent_symm R ((cosetGraph_adj R _ _).mp
    (p.walk.adj_getVert_succ (i:=1) (by omega)))
  have hV : U R c ≤ V R (alpha R) := (DistanceEight.U_le_Z R c).trans
    (le_iSup_of_le c (le_iSup_of_le (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)]) le_rfl))
  have hB : ¬ U R c ≤ B R (alpha R) (s.geometry.Z_normal _) := by
    intro he
    have hn := s.forward_moving_index_two_le h u hfull hb2 p
    have hh := relIndex_eq_one.mpr he
    change (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R c) = 1 at hh
    change 2 ≤ (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R c) at hn
    omega
  obtain ⟨hcard,hseed⟩ := s.moving_hyperplane_commutator_le_seed h u hfull rfl hc hat hct hindex
  have hHZ : H ≤ Z R (alpha R) := hseed.trans (adjacent_Z_le R rfl hat)
  have hTN : stabilizer R (alpha R) ≤ normalizer (T₀ : Set (FreeAmalgam R)) :=
    s.moving_hyperplane_kernel_normalized hb2 rfl hat hct
  intro z hz
  by_contra hzn
  obtain ⟨g,hg,hgen,hgne⟩ := s.exists_noncentral_seed_generator h u hfull p (hHZ hz) hzn
  have hgG := Ltilde_le_stabilizer (alpha R) hg
  let f := (MulAut.conj g).toMonoidHom
  let A := (U R c).map f
  let H₁ := H.map f
  have hVm : (V R (alpha R)).map f = V R (alpha R) :=
    mem_normalizer_iff_map_conj_eq.mp ((DistanceEight.V_normalized R (alpha R)) hgG)
  have hBm : (B R (alpha R) (s.geometry.Z_normal _)).map f = B R (alpha R) (s.geometry.Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized hb2 (alpha R) rfl hgG)
  have hTm : T₀.map f = T₀ := mem_normalizer_iff_map_conj_eq.mp (hTN hgG)
  have hZm : (Z R (alpha R)).map f = Z R (alpha R) :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized R (alpha R) hgG)
  have hAZ : A ≤ V R (alpha R) := hVm ▸ map_mono hV
  have hAB : ¬ A ≤ B R (alpha R) (s.geometry.Z_normal _) := by
    intro he
    apply hB
    apply (map_le_map_iff_of_injective (f:=f) (MulAut.conj g).injective).mp
    rwa [hBm]
  have hH₁Z : H₁ ≤ Z R (alpha R) := hZm ▸ map_mono hHZ
  have hcard₁ : Nat.card H₁ ≤ 2 := by
    rw [show Nat.card H₁ = Nat.card H from card_map_of_injective (MulAut.conj g).injective]
    exact hcard
  let := finite_Z R (alpha R)
  let : Finite H₁ := Finite.of_injective (inclusion hH₁Z) (inclusion_injective _)
  have hz₁ : g*z*g⁻¹ ∈ H₁ := mem_map_of_mem f hz
  have hz₁n : g*z*g⁻¹ ≠ 1 := fun he => hgne (he ▸ (centralizer (Z R e : Set (FreeAmalgam R))).one_mem)
  have hC := centralizer_line_eq_singleton H₁ hcard₁ hz₁ hz₁n
  have hgen₁ : (stabilizer R (alpha R) ⊓ centralizer (H₁ : Set (FreeAmalgam R))) ⊔
      Z R e = stabilizer R (alpha R) := by rw [hC]; exact hgen
  have hcomm : ⁅A,T₀⁆ ≤ H₁ := by
    change ⁅(U R c).map f,T₀⁆ ≤ H.map f
    rw [show H = ⁅U R c,T₀⁆ from rfl,map_commutator,hTm]
  exact s.critical_controlled_line_false_of_two_lt h u hfull hb p A T₀ H₁ hAZ hAB inf_le_left hTN
    hH₁Z hcard₁ (fun he => hgne (he hz₁)) hgen₁ hcomm
    (s.critical_forward_kernel_contains_inner_layers_of_two_lt hb p)
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L ⊔ d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

theorem reducedSource_block_or_forward_fixed_line_of_two_lt
    (r : CharacteristicReduction (L.subgroupOf J) R) {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e)
    (hb : 2 < ((originalSource d hm).reduce r).geometry.b r.radical)
    (hindex : (B r.radical (alpha r.radical) (((originalSource d hm).reduce r).geometry.Z_normal _)).relIndex
      (U r.radical (p.walk.getVert 2)) ≤ 2) :
    IsAlternatingBlock L 6 ∨
      (let T₀ := Q r.radical (alpha r.radical) ⊓ centralizer
         (U r.radical (p.walk.getVert 2) ⊓ B r.radical (alpha r.radical)
           (((originalSource d hm).reduce r).geometry.Z_normal _) : Set (FreeAmalgam r.radical))
       ⁅U r.radical (p.walk.getVert 2),T₀⁆ ≤ fixedCore r.radical (alpha r.radical)) := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock | hfull
  · exact Or.inl hblock
  · right
    let s := (originalSource d hm).reduce r
    have h := reduced_nativeCentralLayer d hm r
    have hf : r.radical.map s.projection = Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    exact s.critical_forward_commutator_le_fixedCore_of_two_lt h _ hf hb p hindex
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
