module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.CoordinatedChoices
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Rigidity.Moving
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.CriticalImage
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.EdgeLayer
public import Theory.GroupAction.SymmetricSixSmallSection
/-!
# Backward critical geometry for a large symplectic image

The chosen backward Z-product has index at most eight over the starting
Z-layer. If the opposite critical layer normalized it, the recorded
neighbor generation would make it normal in the starting stabilizer.
An S6 quotient with a two-group kernel acts trivially by its two-residual
on such a small section, placing the backward layer in B and contradicting
the original transported index.

For a critical image of order at least four, the point-core moved-space
fixer calculation controls the radius commutator at every distance greater
than two. Backward containment would supply the forbidden normalization.
Thus the very same coordinated backward vertex forms a critical pair with
the second predecessor of the original endpoint. The small-image branch
and the subsequent terminal argument remain separate source obligations.

Source: Meierfrankenfeld--Stellmacher (1993), (5.7), printed p.919;
Aschbacher--Smith C.1.37 and 13.7.4(1).
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)
variable {e : Vertex R} {p : CriticalPath R s.geometry (alpha R) e} {delta : Vertex R}

theorem CoordinatedChoice.back_color (c : s.CoordinatedChoice p delta) :
    color R c.alpha1 = false := by
  have h1 := adjacent_color_ne R c.adjacent_start
  have h2 := adjacent_color_ne R c.adjacent_back
  change false ≠ color R c.beta1 at h1
  cases hc : color R c.alpha1 <;> cases hc' : color R c.beta1 <;> simp_all

theorem CoordinatedChoice.edge_color (c : s.CoordinatedChoice p delta) :
    color R c.beta1 = true := by
  have h1 := adjacent_color_ne R c.adjacent_start
  change false ≠ color R c.beta1 at h1
  cases hc : color R c.beta1 <;> simp_all

theorem CoordinatedChoice.back_distance_le_two (c : s.CoordinatedChoice p delta) :
    (cosetGraph R).dist c.alpha1 (alpha R) ≤ 2 := by
  have h1 : (cosetGraph R).dist c.alpha1 c.beta1 = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr c.adjacent_back)
  have h2 : (cosetGraph R).dist c.beta1 (alpha R) = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj R _ _).mpr (adjacent_symm R c.adjacent_start))
  have hh := (cosetGraph_connected R).dist_triangle (u := c.alpha1) (v := c.beta1) (w := alpha R)
  simpa only [h1,h2] using hh

theorem CoordinatedChoice.back_layer_le_radius (c : s.CoordinatedChoice p delta) :
    Z R c.alpha1 ≤ V R (alpha R) :=
  (Z_le_localZSpan R c.alpha1 (alpha R)).trans
    (localZSpan_le_V R c.back_distance_le_two)

theorem CoordinatedChoice.backward_product_normalized
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (c : s.CoordinatedChoice p delta)
    (hn : Z R e ≤ normalizer ((Z R c.alpha1 ⊔ Z R (alpha R) : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R))) :
    stabilizer R (alpha R) ≤
      normalizer ((Z R c.alpha1 ⊔ Z R (alpha R) : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  rw [←c.generation,s.selectedCriticalLayer_eq h u hfull p]
  apply sup_le _ hn
  apply le_trans (le_inf _ _) (normalizer_inf_normalizer_le_normalizer_sup _ _)
  · have hq : Q R c.beta1 ≤ stabilizer R c.alpha1 :=
      fun _ hx => hx.2 c.alpha1 (adjacent_symm R c.adjacent_back)
    exact hq.trans (Z_normalized R c.alpha1)
  · have hq : Q R c.beta1 ≤ stabilizer R (alpha R) :=
      fun _ hx => hx.2 (alpha R) (adjacent_symm R c.adjacent_start)
    exact hq.trans (Z_normalized R (alpha R))

theorem CoordinatedChoice.backward_product_index_le_eight
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (c : s.CoordinatedChoice p delta) :
    (Z R (alpha R)).relIndex (Z R c.alpha1 ⊔ Z R (alpha R)) ≤ 8 := by
  let := finite_Z R (alpha R)
  let := finite_Z R c.alpha1
  have hza : Z R (alpha R) ≤ Q R c.beta1 :=
    (s.Z_le_X.trans (omegaCenter_le _)).trans
      (Q_le_adjacent_h R c.edge_color c.adjacent_start)
  have hn : Z R (alpha R) ≤ normalizer (Z R c.alpha1 : Set (FreeAmalgam R)) :=
    (hza.trans (fun _ hx => hx.2 c.alpha1 (adjacent_symm R c.adjacent_back))).trans
      (Z_normalized R c.alpha1)
  rw [relIndex_sup_of_normalizes _ _ hn]
  have hsmall := relIndex_le_of_le_left (adjacent_Z_le R rfl c.adjacent_start)
    (index_ne_zero_of_finite : (Z R c.beta1).relIndex (Z R c.alpha1) ≠ 0)
  have hpoint : R.map s.projection =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom := by
    simpa only [Model.pointCore_eq_exceptional] using hfull
  exact hsmall.trans_eq (s.edge_Z_index_eight_at h u hpoint c.back_color c.adjacent_back)
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

omit [Finite M] in
private theorem normalized_comap_normal (J : Subgroup (FreeAmalgam R))
    (hJ : stabilizer R (alpha R) ≤ normalizer (J : Set (FreeAmalgam R))) :
    (J.comap (embedM R)).Normal := by
  constructor
  intro n hn g
  change embedM R (g*n*g⁻¹) ∈ J
  rw [map_mul,map_mul,map_inv]
  exact (le_normalizer_iff.mp hJ (embedM R g)
    (by change embedM R g ∈ stabilizer R (mVertex R 1); rw [stabilizer_m_base]; exact ⟨g,rfl⟩)) _ hn

theorem normal_radius_subgroup_le_B_of_index
    (hq : Function.Surjective s.projection) (hb : 2 < s.geometry.b R)
    (D : Subgroup (FreeAmalgam R)) (hD : D ≤ V R (alpha R))
    (hn : stabilizer R (alpha R) ≤ normalizer (D : Set (FreeAmalgam R)))
    (hindex : (Z R (alpha R)).relIndex D ≤ 8) :
    D ≤ B R (alpha R) (s.geometry.Z_normal _) := by
  let f := embedM R
  let D₀ := D.comap f
  let Z₀ := (Z R (alpha R)).comap f
  let : D₀.Normal := normalized_comap_normal _ hn
  let : Z₀.Normal := normalized_comap_normal _ (Z_normalized R (alpha R))
  have hVQ : V R (alpha R) ≤ Q R (alpha R) := V_le_Q R rfl hb
  have hVrange : V R (alpha R) ≤ f.range :=
    (hVQ.trans (fun _ hx => hx.1)).trans_eq (stabilizer_m_base R)
  have hDm : D₀.map f = D := map_comap_eq_self (hD.trans hVrange)
  have hZm : Z₀.map f = Z R (alpha R) :=
    map_comap_eq_self ((Z_le_stabilizer R (alpha R)).trans_eq (stabilizer_m_base R))
  have hDker : D₀ ≤ s.projection.ker := by
    rw [s.projection_kernel]
    apply (map_le_map_iff_of_injective (embedM_injective R)).mp
    rw [hDm,←Q_alpha R s.two_group s.core_le]
    exact hD.trans hVQ
  have hp : IsPGroup 2 s.projection.ker := by
    rw [s.projection_kernel]
    exact pCore_isPGroup
  have hi₀ : Z₀.relIndex D₀ ≤ 8 := by
    rw [relIndex_comap,hDm]
    exact hindex
  have hh := map_mono (f := f)
    (commutator_pResidual_le_of_symmetricSix_small_section s.projection hq hp D₀ Z₀ hDker hi₀)
  rw [map_commutator,hDm,hZm,←Ltilde_alpha] at hh
  intro x hx
  apply (mem_B_iff R _ (s.geometry.Z_normal _) (hVQ.trans (fun _ hy => hy.1)) x).mpr
  refine ⟨hD hx,fun l hl => ?_⟩
  apply hh
  rw [commutator_comm]
  exact commutator_mem_commutator hl hx

variable {e : Vertex R} {p : CriticalPath R s.geometry (alpha R) e} {delta : Vertex R}

theorem CoordinatedChoice.backward_layer_le_B_of_normalization
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) (c : s.CoordinatedChoice p delta)
    (hn : Z R e ≤ normalizer
      ((Z R c.alpha1 ⊔ Z R (alpha R) : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R))) :
    Z R c.alpha1 ≤ B R (alpha R) (s.geometry.Z_normal _) := by
  apply le_trans le_sup_left
  exact s.normal_radius_subgroup_le_B_of_index
    (s.projection_surjective_of_radical_image_le_conjugate u hfull.le) hb
    (Z R c.alpha1 ⊔ Z R (alpha R))
    (sup_le c.back_layer_le_radius (Z_le_VBall R (alpha R) 2))
    (c.backward_product_normalized s h u hfull hn)
    (c.backward_product_index_le_eight s h u hfull)

theorem CoordinatedChoice.backward_opposite_not_normalizes
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) (c : s.CoordinatedChoice p delta)
    (hindex : 1 < (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R delta)) :
    ¬ Z R e ≤ normalizer
      ((Z R c.alpha1 ⊔ Z R (alpha R) : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  intro hn
  have hU : U R c.alpha1 ≤ B R (alpha R) (s.geometry.Z_normal _) :=
    (DistanceEight.U_le_Z R c.alpha1).trans
      (c.backward_layer_le_B_of_normalization s h u hfull hb hn)
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
open Theory.SpecificGroups.SymmetricSix.BinaryFlags

theorem critical_radius_commutator_le_Z_of_two_lt (h : NativeCentralLayer s) (u : S)
    (hR : R.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {a a' : Vertex R}
    (p : CriticalPath R s.geometry a a')
    (hcard : 4 ≤ (Q R a').relIndex (Z R a)) :
    ⁅V R a ⊓ Q R (p.walk.getVert (p.walk.length-2)),Z R a'⁆ ≤ Z R a := by
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  let t := p.walk.getVert (p.walk.length-1)
  have hct : Adjacent R a' t := by
    have hh := p.walk.adj_getVert_succ (i:=p.walk.length-1) (by omega)
    have hi : p.walk.length-1+1 = p.walk.length := by omega
    rw [hi,p.walk.getVert_length] at hh
    exact adjacent_symm R ((cosetGraph_adj R _ _).mp hh)
  have ht : color R t = true := by
    have hh := adjacent_color_ne R hct
    rw [p.end_color] at hh
    cases hc : color R t <;> simp_all
  have het : Adjacent R (p.walk.getVert (p.walk.length-2)) t := by
    have hh := p.walk.adj_getVert_succ (i:=p.walk.length-2) (by omega)
    have hi : p.walk.length-2+1 = p.walk.length-1 := by omega
    rw [hi] at hh
    exact (cosetGraph_adj R _ _).mp hh
  have hAt : Z R a ≤ Q R t := by
    apply Z_le_Q_of_dist_lt R a (s.geometry.exists_critical a p.start_color)
    have hd : (cosetGraph R).dist a t = p.walk.length-1 := p.dist_start (by omega)
    rw [hd,s.geometry.distance_constant a p.start_color]
    change p.walk.length-1 < s.geometry.b R
    rw [←p.length_eq_b]
    omega
  have hYt : V R a ⊓ Q R (p.walk.getVert (p.walk.length-2)) ≤ Q R t :=
    inf_le_right.trans (Q_le_adjacent_h R ht het)
  have hcomm : ⁅U R a',Z R a⁆ ≤ ⁅Z R a,Z R a'⁆ := by
    rw [commutator_comm]
    exact commutator_mono le_rfl (DistanceEight.U_le_Z R a')
  have hRZa : ⁅Z R a,Z R a'⁆ ≤ Z R a :=
    ((s.critical_Z_commutator_le_moving p).trans inf_le_left).trans (DistanceEight.U_le_Z R a)
  let := s.geometry.Z_elementary (by omega : 0 < s.geometry.b R) a p.start_color
  have hAA : ⁅U R a',Z R a⁆ ≤ centralizer (Z R a : Set (FreeAmalgam R)) :=
    (hcomm.trans hRZa).trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hAY : ⁅U R a',Z R a⁆ ≤ centralizer
      (V R a ⊓ Q R (p.walk.getVert (p.walk.length-2)) : Set (FreeAmalgam R)) :=
    hcomm.trans (le_centralizer_iff.mp (s.critical_radius_intersection_centralizes hb p))
  have hh := s.edge_commutator_control_at h u hR a' t p.end_color hct
    (Z R a) _ hAt hYt hcard hAA hAY
  rw [commutator_comm (Z R a') (Z R a)] at hh
  rw [commutator_comm]
  exact hh.trans hRZa

omit [Finite M] [L.Normal] [W.Normal] s in
private theorem normalizes_product_of_commutator_le
    (A B C : Subgroup (FreeAmalgam R))
    (hAC : A ≤ normalizer (C : Set (FreeAmalgam R))) (hAB : ⁅A,B⁆ ≤ C) :
    A ≤ normalizer ((B ⊔ C : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  rw [le_normalizer_iff]
  intro a ha x hx
  have hm : (B ⊔ C).map (MulAut.conj a).toMonoidHom ≤ B ⊔ C := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rintro _ ⟨b,hb,rfl⟩
      have hc : ⁅a,b⁆ ∈ C := hAB (commutator_mem_commutator ha hb)
      have he : (MulAut.conj a) b = ⁅a,b⁆*b := by simp [MulAut.conj_apply,commutatorElement_def,mul_assoc]
      change (MulAut.conj a) b ∈ B ⊔ C
      rw [he]
      exact mul_mem (mem_sup_right hc) (mem_sup_left hb)
    · rw [MulEquiv.toMonoidHom_eq_coe,mem_normalizer_iff_map_conj_eq.mp (hAC ha)]
      exact le_sup_right
  exact hm (mem_map_of_mem (MulAut.conj a).toMonoidHom hx)

theorem CoordinatedChoice.large_backward_not_le
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {e : Vertex R}
    {p : CriticalPath R s.geometry (alpha R) e} {delta : Vertex R}
    (c : s.CoordinatedChoice p delta)
    (hindex : 1 < (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R delta))
    (hlarge : 4 ≤ (Q R e).relIndex (Z R (alpha R))) :
    ¬ Z R c.alpha1 ≤ Q R (p.walk.getVert (p.walk.length-2)) := by
  intro hbad
  apply c.backward_opposite_not_normalizes s h u hfull hb hindex
  have hpoint : R.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom := by
    simpa only [Model.pointCore_eq_exceptional] using hfull.le
  have hcomm : ⁅Z R c.alpha1,Z R e⁆ ≤ Z R (alpha R) :=
    (commutator_mono (le_inf c.back_layer_le_radius hbad) le_rfl).trans
      (s.critical_radius_commutator_le_Z_of_two_lt h u hpoint hb p hlarge)
  apply normalizes_product_of_commutator_le
  · exact (critical_Z_le_stabilizer R s.geometry (alpha R) rfl
      s.criticalDistance_pos p.critical).trans (Z_normalized R (alpha R))
  · rwa [commutator_comm]

theorem CoordinatedChoice.large_backward_critical
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {e : Vertex R}
    {p : CriticalPath R s.geometry (alpha R) e} {delta : Vertex R}
    (c : s.CoordinatedChoice p delta)
    (hindex : 1 < (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R delta))
    (hlarge : 4 ≤ (Q R e).relIndex (Z R (alpha R))) :
    CriticalPair R c.alpha1 (p.walk.getVert (p.walk.length-2))
      (s.geometry.exists_critical c.alpha1 c.back_color) := by
  have hn := c.large_backward_not_le s h u hfull hb hindex hlarge
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

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L ⊔ d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

/-- The original characteristic replacement supplies all marked inputs for
the large-image backward critical step, or already gives the alternating block. -/
theorem reducedSource_block_or_large_backward_critical
    (r : CharacteristicReduction (L.subgroupOf J) R) {e : Vertex r.radical}
    {p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e}
    {delta : Vertex r.radical}
    (c : ((originalSource d hm).reduce r).CoordinatedChoice p delta)
    (hb : 2 < ((originalSource d hm).reduce r).geometry.b r.radical)
    (hindex : 1 < (B r.radical (alpha r.radical)
      (((originalSource d hm).reduce r).geometry.Z_normal _)).relIndex (U r.radical delta))
    (hlarge : 4 ≤ (Q r.radical e).relIndex (Z r.radical (alpha r.radical))) :
    IsAlternatingBlock L 6 ∨
      CriticalPair r.radical c.alpha1 (p.walk.getVert (p.walk.length-2))
        (((originalSource d hm).reduce r).geometry.exists_critical c.alpha1 c.back_color) := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock | hfull
  · exact Or.inl hblock
  · right
    apply c.large_backward_critical ((originalSource d hm).reduce r)
      (reduced_nativeCentralLayer d hm r) d.relabeler.val⁻¹ _ hb hindex hlarge
    simpa only [Model.pointCore_eq_exceptional] using hfull
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
