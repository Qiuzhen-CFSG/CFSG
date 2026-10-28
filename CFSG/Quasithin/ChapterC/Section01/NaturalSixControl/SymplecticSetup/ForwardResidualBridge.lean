module
public import Theory.SpecificGroups.SymmetricSix.ResidualSmallIndex
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardMovedSpanNatural
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardCoreEndpoint
/-!
# Residual containment from the terminal endpoint action

At critical distance four write P for the forward normal span, P0=[P,L_alpha]
and Q0=[Q_alpha,L_alpha]. The faithful natural central quotient P0/Z(P0)
shows that the critical endpoint cannot commute with P0 modulo U_alpha.
An index-at-most-two subgroup D=Q0 intersect Q_c whose endpoint commutator
lies in U_alpha therefore satisfies Q0=D P0. The finite local symmetric-six
quotient and the odd endpoint image then contract Q0 into U_alpha P0.

The selected endpoint orbit supplies the required commutator bound through
ForwardCoreEndpoint. The source-data and original Chapter13 consumers keep
the actual characteristic replacement and its SQTK hypothesis. This proves
the sufficient containment, without asserting equality of Q0 and P0.

Source: MS93 (3.10)(i), printed p.880, in the terminal configuration of
(5.12), printed p.927.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

/-- The endpoint acts nontrivially on the intrinsic central quotient of the moved span. -/
theorem forward_moved_span_endpoint_commutator_not_le_U
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hsq : IsSQTK KnownSimple.IsKnownSimple M)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    ¬ ⁅forwardMovedSpan R (p.walk.getVert 2),Z R e⁆≤U R (alpha R) := by
  let c := p.walk.getVert 2
  let P₀ := forwardMovedSpan R c
  obtain ⟨E,τ,hE⟩ := s.forward_moved_span_natural_data h u hfull hsq hb p
  have hPQ : P₀≤Q R (alpha R) := (forwardMovedSpan_le R c).trans
    ((s.forward_span_le_hyperplane_kernel (by omega) p).trans inf_le_left)
  have hUC : U R (alpha R)≤centralizer (P₀:Set (FreeAmalgam R)) :=
    (DistanceEight.U_le_Z R _).trans
      ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R (alpha R) rfl)).trans
        (centralizer_le hPQ))
  have hpnt : R.map s.projection≤Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
      (MulAut.conj u).toMonoidHom := by
    simpa only [Model.pointCore_eq_exceptional] using hfull.le
  obtain ⟨a,ha,hodd⟩ := SetLike.not_le_iff_exists.mp
    (s.critical_opposite_image_not_le_alternating h u hpnt p)
  obtain ⟨m,hm,rfl⟩ := ha
  have hn : s.projection m≠1 := fun he => hodd (he ▸ (alternatingGroup (Fin 6)).one_mem)
  intro hcomm
  have hfixed (x:P₀) : QuotientGroup.mk' (center P₀) (forwardMovedSpanAction R c m x)=
      QuotientGroup.mk' (center P₀) x := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    have hh := hUC (hcomm (by
      rw [commutator_comm]
      exact commutator_mem_commutator hm x.property)) y y.property
    change (y:FreeAmalgam R)*(embedM R m*(x:FreeAmalgam R)*(embedM R m)⁻¹/(x:FreeAmalgam R))=
      (embedM R m*(x:FreeAmalgam R)*(embedM R m)⁻¹/(x:FreeAmalgam R))*(y:FreeAmalgam R)
    simpa only [div_eq_mul_inv,commutatorElement_def] using hh
  have hrep : BinaryPermutation.naturalRepresentation (Fin 6) (τ (s.projection m))=1 := by
    apply LinearMap.ext
    intro v
    obtain ⟨z,hz⟩ := E.surjective (Multiplicative.ofAdd v)
    obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (center P₀) z
    have hv : (E (QuotientGroup.mk' (center P₀) x)).toAdd=v := by rw [hx,hz]; rfl
    have he := hE m x
    rw [hfixed] at he
    change BinaryPermutation.naturalRepresentation (Fin 6) (τ (s.projection m)) v=v
    rw [←hv]
    exact he.symm
  have ht : τ (s.projection m)=1 :=
    (BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide))
      (hrep.trans (map_one (BinaryPermutation.naturalRepresentation (Fin 6))).symm)
  exact hn (τ.injective (ht.trans τ.map_one.symm))

omit [Finite M] in
private theorem normalized_comap_normal (J : Subgroup (FreeAmalgam R))
    (hJ : stabilizer R (alpha R)≤normalizer (J:Set (FreeAmalgam R))) :
    (J.comap (embedM R)).Normal := by
  constructor
  intro n hn g
  change embedM R (g*n*g⁻¹)∈J
  rw [map_mul,map_mul,map_inv]
  exact (le_normalizer_iff.mp hJ (embedM R g)
    (by change embedM R g∈stabilizer R (mVertex R 1); rw [stabilizer_m_base]; exact ⟨g,rfl⟩)) _ hn

/-- The index-two endpoint action contracts the residual into the moving layer and span. -/
theorem core_commutator_le_moving_sup_forward_moved_span
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hsq : IsSQTK KnownSimple.IsKnownSimple M)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (hactor : ⁅⁅Q R (alpha R),Ltilde R (alpha R)⁆⊓Q R (p.walk.getVert 2),Z R e⁆≤U R (alpha R)) :
    ⁅Q R (alpha R),Ltilde R (alpha R)⁆≤U R (alpha R)⊔forwardMovedSpan R (p.walk.getVert 2) := by
  let c := p.walk.getVert 2
  let Q₀ := ⁅Q R (alpha R),Ltilde R (alpha R)⁆
  let P₀ := forwardMovedSpan R c
  let D := Q₀⊓Q R c
  let f := embedM R
  let Qm := ⁅pCore 2 M,pResidual 2 M⁆
  let Um := (U R (alpha R)).comap f
  let Wm := P₀.comap f
  let Dm := D.comap f
  let Am := (Z R e).comap f
  have hQf : Qm.map f=Q₀ := by
    dsimp only [Qm,Q₀,f]
    rw [map_commutator,←Q_alpha R s.two_group s.core_le,←Ltilde_alpha]
  have hGa : stabilizer R (alpha R)=f.range := stabilizer_m_base R
  have hQGa : Q R (alpha R)≤stabilizer R (alpha R) := fun _ hx => hx.1
  have hPQ : P₀≤Q R (alpha R) := (forwardMovedSpan_le R c).trans
    ((s.forward_span_le_hyperplane_kernel (by omega) p).trans inf_le_left)
  have hP₀Q₀ : P₀≤Q₀ := commutator_mono
    ((s.forward_span_le_hyperplane_kernel (by omega) p).trans inf_le_left) le_rfl
  have hPf : Wm.map f=P₀ := map_comap_eq_self (hPQ.trans (hQGa.trans_eq hGa))
  have hUf : Um.map f=U R (alpha R) := map_comap_eq_self
    ((DistanceEight.U_le_Z R _).trans ((Z_le_stabilizer R _).trans_eq hGa))
  have hQ₀Ga : Q₀≤stabilizer R (alpha R) :=
    ((s.core_commutator_le_forward_hyperplane_kernel u hfull (by omega) p).trans inf_le_left).trans hQGa
  have hDf : Dm.map f=D := map_comap_eq_self (inf_le_left.trans (hQ₀Ga.trans_eq hGa))
  have hAf : Am.map f=Z R e := map_comap_eq_self
    ((critical_Z_le_stabilizer R s.geometry (alpha R) rfl s.criticalDistance_pos p.critical).trans_eq hGa)
  have hQm : Q₀.comap f=Qm := by
    rw [←hQf,comap_map_eq_self_of_injective (embedM_injective R)]
  let : Um.Normal := normalized_comap_normal _ (U_normalized (R:=R) _)
  let : Wm.Normal := normalized_comap_normal _ (forwardMovedSpan_normalized R _)
  have hWQ : Wm≤Qm := by rw [←hQm]; exact comap_mono hP₀Q₀
  have hDQ : Dm≤Qm := by rw [←hQm]; exact comap_mono inf_le_left
  have hi : Dm.relIndex Qm≤2 := by
    rw [relIndex_comap,hQf]
    simpa only [D,inf_relIndex_left] using s.core_commutator_second_vertex_index_le_two h u hfull hb p
  have hmove : ⁅Qm,pResidual 2 M⁆=Qm :=
    commutator_isPPerfect_idempotent _ _ (isPPerfect_pResidual 2) pCore_isPGroup le_normalizer_of_normal
  have hDA : ⁅Dm,Am⁆≤Um := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator,hDf,hAf]
    exact hactor
  have hnot : ¬Wm≤Dm := by
    intro he
    have hPD : P₀≤D := by rw [←hPf,←hDf]; exact map_mono he
    exact s.forward_moved_span_endpoint_commutator_not_le_U h u hfull hsq hb p
      ((commutator_mono hPD le_rfl).trans hactor)
  have hpnt : R.map s.projection≤Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
      (MulAut.conj u).toMonoidHom := by
    simpa only [Model.pointCore_eq_exceptional] using hfull.le
  have hresult := residual_moved_le_of_symmetricSix_odd_small_index s.projection
    (s.projection_surjective_of_radical_image_le_conjugate u hfull.le)
    (by rw [s.projection_kernel]; exact pCore_isPGroup)
    Qm Um Wm Dm Am hWQ hDQ hi hmove hDA hnot
    (s.critical_opposite_image_not_le_alternating h u hpnt p)
  have hh := map_mono (f:=f) hresult
  rwa [hQf,Subgroup.map_sup,hUf,hPf] at hh

/-- The selected endpoint orbit discharges the actor bound. -/
theorem core_commutator_le_moving_sup_forward_moved_span_of_orbit
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hsq : IsSQTK KnownSimple.IsKnownSimple M)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (g : FreeAmalgam R) (hg : g∈stabilizer R (p.walk.getVert 2))
    (he : act R g (alpha R)=e)
    (hindex : (B R (p.walk.getVert 2) (s.geometry.Z_normal _)).relIndex (U R e)≤2) :
    ⁅Q R (alpha R),Ltilde R (alpha R)⁆≤U R (alpha R)⊔forwardMovedSpan R (p.walk.getVert 2) :=
  s.core_commutator_le_moving_sup_forward_moved_span h u hfull hsq hb p
    (s.core_endpoint_small_action_of_orbit h u hfull hb p g hg he hindex).2
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K] {L W : Subgroup K} [L.Normal] [W.Normal]
  {T : Sylow 2 K} (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L⊔d.B : Subgroup K)

theorem reducedSource_block_or_core_commutator_le_moving_sup_forward_moved_span
    (r : CharacteristicReduction (L.subgroupOf J) (d.B.subgroupOf J)) {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e)
    (hb : ((originalSource d hm).reduce r).geometry.b r.radical=4)
    (hactor : ⁅⁅Q r.radical (alpha r.radical),Ltilde r.radical (alpha r.radical)⁆⊓
      Q r.radical (p.walk.getVert 2),Z r.radical e⁆≤U r.radical (alpha r.radical)) :
    IsAlternatingBlock L 6 ∨
      ⁅Q r.radical (alpha r.radical),Ltilde r.radical (alpha r.radical)⁆≤
        U r.radical (alpha r.radical)⊔forwardMovedSpan r.radical (p.walk.getVert 2) := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock|hfull
  · exact Or.inl hblock
  · right
    let s := (originalSource d hm).reduce r
    have hf : r.radical.map s.projection=Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    exact s.core_commutator_le_moving_sup_forward_moved_span (reduced_nativeCentralLayer d hm r) _ hf
      ((d.sqtk.subgroup J).subgroup r.overgroup) hb p hactor

theorem reducedSource_block_or_core_commutator_le_moving_sup_forward_moved_span_of_orbit
    (r : CharacteristicReduction (L.subgroupOf J) (d.B.subgroupOf J)) {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e)
    (hb : ((originalSource d hm).reduce r).geometry.b r.radical=4)
    (g : FreeAmalgam r.radical) (hg : g∈stabilizer r.radical (p.walk.getVert 2))
    (he : act r.radical g (alpha r.radical)=e)
    (hindex : (B r.radical (p.walk.getVert 2)
      (((originalSource d hm).reduce r).geometry.Z_normal _)).relIndex (U r.radical e)≤2) :
    IsAlternatingBlock L 6 ∨
      ⁅Q r.radical (alpha r.radical),Ltilde r.radical (alpha r.radical)⁆≤
        U r.radical (alpha r.radical)⊔forwardMovedSpan r.radical (p.walk.getVert 2) := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock|hfull
  · exact Or.inl hblock
  · right
    let s := (originalSource d hm).reduce r
    have hf : r.radical.map s.projection=Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    exact s.core_commutator_le_moving_sup_forward_moved_span_of_orbit
      (reduced_nativeCentralLayer d hm r) _ hf ((d.sqtk.subgroup J).subgroup r.overgroup) hb p g hg he hindex
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
