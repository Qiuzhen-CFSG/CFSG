module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRawComparison
/-!
# Selecting a genuine next critical path after the raw comparison

Retain a critical path a--v--c--t--z with generating midpoint edges and a
strict backward midpoint slice. If every conjugate of c whose preceding
edge generates with Q_v lay in Q_c, the raw comparison would control its
commutator with Z_z. The normalized selector's switch preserves Q_v, so
the same comparison controls the commutator with the switched endpoint.
The joint generation equation then makes the candidate seed joined with
Z_a normal in G_a. The normal-radius theorem puts this join in B_a.
Transporting back contradicts the already proved eligibility of U_c.

Thus some candidate escapes Q_c. Minimum critical distance makes its
literal four-edge walk critical. Both generating edges, the actual
transporter and the full-kernel comparison hold on that same new path.
The outer selection supplies the required midpoint conditions without any
new next-path or next-slice premise. Whole-core and literal C.1.32
applications retain the original projection with kernel E, its odd E/Q,
the original proper radical and both full moving covers.

This proves the critical-candidate selection following MS93 (5.12)(1).
The later small-slice and terminal calculations, the remaining distance
and Borel branches, both core exhaustions and final reconstruction remain.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.12), printed p.925, the paragraph following (1);
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Representation Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk


local notation "M" => (L ⊔ R : Subgroup G)
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)

include h e hz hk in
private theorem plane_generating_critical_candidate_base
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hmidgen : Q Rg (p.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 3) =
      stabilizer Rg (p.walk.getVert 2))
    (hback : 2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (alpha Rg))) :
    ∃ g ∈ stabilizer Rg (alpha Rg),
      Q Rg (act Rg g (p.walk.getVert 1)) ⊔ Q Rg (p.walk.getVert 1) =
        stabilizer Rg (alpha Rg) ∧
      ¬ Z Rg (act Rg g (p.walk.getVert 2)) ≤ Q Rg (p.walk.getVert 2) := by
  classical
  by_contra! hn
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hav : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hcv : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨s,has,r,hr,hgen,hpair,hfix,hnorm,hinside,hcomm⟩ :=
    remaining_small_critical_normalized_plane_selectors h e hz hk u (Or.inl hR)
      p (hsmall _ _ p)
  let x := (embedM Rg r)⁻¹
  have hx : x ∈ stabilizer Rg (alpha Rg) := by
    change x ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨r⁻¹,by rw [map_inv]⟩
  have hxa : act Rg x (alpha Rg) = alpha Rg := hx
  have hxia : act Rg x⁻¹ (alpha Rg) = alpha Rg :=
    (stabilizer Rg (alpha Rg)).inv_mem hx
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl has] at hgen
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hav] at hnorm hinside
  have hgs : Q Rg s ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg (alpha Rg) := by
    apply le_antisymm
    · exact sup_le (fun _ hv => hv.2 _ (adjacent_symm Rg has))
        (fun _ hv => hv.2 _ (adjacent_symm Rg hav))
    · rw [←hgen]
      exact sup_le (sup_le le_sup_left ((le_sup_left.trans hinside).trans le_sup_right))
        ((le_sup_right.trans hinside).trans le_sup_right)
  obtain ⟨g,hg,hgv⟩ := stabilizer_transitive_neighbors Rg (alpha Rg) hav has
  have line {w : Vertex Rg}
      (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) w) :
      ⁅Z Rg (alpha Rg),Z Rg w⁆ ≤ Z Rg (alpha Rg) :=
    le_normalizer_iff_commutator_le_left.mp
      ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
        (sourceDistance_pos h) q.critical).trans (Z_normalized Rg _))
  have control (k : FreeAmalgam Rg) (hkG : k ∈ stabilizer Rg (alpha Rg))
      (hkg : Q Rg (act Rg k (p.walk.getVert 1)) ⊔ Q Rg (p.walk.getVert 1) =
        stabilizer Rg (alpha Rg)) :
      ⁅Z Rg (act Rg k (p.walk.getVert 2)),Z Rg z⁆ ≤ Z Rg (alpha Rg) := by
    have hks : Adjacent Rg (alpha Rg) (act Rg k (p.walk.getVert 1)) := by
      simpa only [show act Rg k (alpha Rg) = alpha Rg from hkG] using
        (adjacent_act_iff Rg k _ _).mpr hav
    have hkds : Adjacent Rg (act Rg k (p.walk.getVert 2))
        (act Rg k (p.walk.getVert 1)) := (adjacent_act_iff Rg k _ _).mpr hcv
    exact (plane_raw_shifted_kernels_of_midpoint_generation h e hz hk u hR hb4 hsmall
      p hkds hks (Z Rg (act Rg k (p.walk.getVert 2)))
      (le_inf le_rfl (hn k hkG hkg)) hkg k hkG rfl hmidgen hback).2.trans (line p)
  have hggen : Q Rg (act Rg g (p.walk.getVert 1)) ⊔ Q Rg (p.walk.getVert 1) =
      stabilizer Rg (alpha Rg) := by rwa [hgv]
  have hkg : Q Rg (act Rg (g*x⁻¹) (p.walk.getVert 1)) ⊔ Q Rg (p.walk.getVert 1) =
      stabilizer Rg (alpha Rg) := by
    have hQx : (Q Rg (p.walk.getVert 1)).map (MulAut.conj x).toMonoidHom =
        Q Rg (p.walk.getVert 1) := mem_normalizer_iff_map_conj_eq.mp hnorm
    have he := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hggen
    rw [Subgroup.map_sup,hQx] at he
    have he' : Q Rg (act Rg x⁻¹ (act Rg g (p.walk.getVert 1))) ⊔
        Q Rg (p.walk.getVert 1) = stabilizer Rg (act Rg x⁻¹ (alpha Rg)) := by
      simpa only [Q_act,stabilizer_act,inv_inv] using he
    simpa only [hxia,←act_mul] using he'
  have hmove := control g hg hggen
  have hmove' := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom)
    (control (g*x⁻¹) ((stabilizer Rg (alpha Rg)).mul_mem hg
      ((stabilizer Rg (alpha Rg)).inv_mem hx)) hkg)
  rw [map_commutator,←Z_act,←Z_act,←Z_act,hxa,←act_mul,
    mul_assoc,inv_mul_cancel,mul_one] at hmove'
  let d := act Rg g (p.walk.getVert 2)
  have hds : Adjacent Rg d s := by
    rw [←hgv]
    exact (adjacent_act_iff Rg g _ _).mpr hcv
  have hda : (cosetGraph Rg).dist d (alpha Rg) ≤ 2 := by
    let w : (cosetGraph Rg).Walk d (alpha Rg) :=
      .cons ((cosetGraph_adj Rg _ _).mpr hds)
        (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg has)) .nil)
    exact (cosetGraph Rg).dist_le w
  have hZV : Z Rg d ≤ V Rg (alpha Rg) :=
    le_iSup_of_le d (le_iSup_of_le hda le_rfl)
  let Y := Z Rg d ⊔ Z Rg (alpha Rg)
  have endpoint {w : Vertex Rg}
      (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (hm : ⁅Z Rg d,Z Rg w⁆ ≤ Z Rg (alpha Rg)) :
      ⁅Y,Z Rg w⁆ ≤ Z Rg (alpha Rg) := by
    apply commutator_sup_le_of_relative_normal (stabilizer Rg (alpha Rg))
      (Z Rg d) (Z Rg (alpha Rg)) (Z Rg w) (Z Rg (alpha Rg))
      (Z_normalized Rg _) (hZV.trans ((sourceGeometry h).V_local _ rfl hb))
      (Z_le_stabilizer Rg _) hm
    exact line q
  have hp' : ∃ p' : CriticalPath Rg (sourceGeometry h)
      (act Rg x (alpha Rg)) (act Rg x z), True := ⟨p.act x,trivial⟩
  rw [hxa] at hp'
  obtain ⟨p',_⟩ := hp'
  have hYn : stabilizer Rg (alpha Rg) ≤ normalizer (Y : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (le_inf
        ((show Q Rg s ≤ stabilizer Rg d from
          fun _ hv => hv.2 _ (adjacent_symm Rg hds)).trans (Z_normalized Rg d))
        ((show Q Rg s ≤ stabilizer Rg (alpha Rg) from
          fun _ hv => hv.2 _ (adjacent_symm Rg has)).trans (Z_normalized Rg _))).trans
            (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact le_normalizer_iff_commutator_le_left.mpr ((endpoint p hmove).trans le_sup_right)
    · exact le_normalizer_iff_commutator_le_left.mpr ((endpoint p' hmove').trans le_sup_right)
  have hYB : Y ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    normalized_radius_le_slice_of_critical_commutator h e hz hb p Y
      (sup_le hZV (Z_le_VBall Rg _ 2)) hYn (endpoint p hmove)
  have hBmap : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hg))
  apply (plane_critical_paths h e hz hk u hR p).2.2.2
  apply (map_le_map_iff_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective).mp
  rw [←U_act,hBmap]
  exact (DistanceEight.U_le_Z Rg d).trans (le_sup_left.trans hYB)

include h e hz hk in
/-- A generating preceding candidate escapes the original midpoint core.
The statement retains the actual graph transporter at every vertex. -/
theorem plane_generating_critical_candidate
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hmidgen : Q Rg (p.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 3) =
      stabilizer Rg (p.walk.getVert 2))
    (hback : 2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg a)) :
    ∃ g ∈ stabilizer Rg a,
      Q Rg (act Rg g (p.walk.getVert 1)) ⊔ Q Rg (p.walk.getVert 1) =
        stabilizer Rg a ∧
      ¬ Z Rg (act Rg g (p.walk.getVert 2)) ≤ Q Rg (p.walk.getVert 2) := by
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hc : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  obtain ⟨f,ha⟩ := exists_mVertex_of_color Rg p.start_color
  have hfa : act Rg f (alpha Rg) = a := by
    simpa only [alpha,act_mVertex,one_mul] using ha.symm
  have hfia : act Rg f⁻¹ a = alpha Rg := by
    rw [←hfa,←act_mul,mul_inv_cancel,act_one]
  have hp0 : ∃ p₀ : CriticalPath Rg (sourceGeometry h)
      (act Rg f⁻¹ a) (act Rg f⁻¹ z),
      ∀ i, p₀.walk.getVert i = act Rg f⁻¹ (p.walk.getVert i) :=
    ⟨p.act f⁻¹,fun _ => by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hfia] at hp0
  obtain ⟨p₀,hverts⟩ := hp0
  have hmid : Q Rg (p₀.walk.getVert 1) ⊔ Q Rg (p₀.walk.getVert 3) =
      stabilizer Rg (p₀.walk.getVert 2) := by
    rw [hverts 1,hverts 3,hverts 2,Q_act,Q_act,stabilizer_act,←Subgroup.map_sup,hmidgen]
  have hU : U Rg (alpha Rg) = (U Rg a).map (MulAut.conj f).toMonoidHom := by
    rw [←hfia,U_act,inv_inv]
  have hs : 2 < (B Rg (p₀.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (alpha Rg)) := by
    rw [hverts 2,Escape.PairingControl.FirstPairing.B_act hb f⁻¹ _ hc,hU,
      inv_inv,relIndex_map_map_of_injective _ _ (MulAut.conj f).injective]
    exact hback
  obtain ⟨k,hkG,hgen,hne⟩ :=
    plane_generating_critical_candidate_base h e hz hk u hR hb4 hsmall p₀ hmid hs
  let g := (MulAut.conj f⁻¹) k
  have hgG : g ∈ stabilizer Rg a := by
    have hh := mem_map_of_mem (MulAut.conj f⁻¹).toMonoidHom hkG
    rwa [←stabilizer_act,hfa] at hh
  have hcancel (v : Vertex Rg) : act Rg f (act Rg f⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have htransport (v : Vertex Rg) :
      act Rg f (act Rg k (act Rg f⁻¹ v)) = act Rg g v := by
    rw [←act_mul,←act_mul]
    simp only [g,MulAut.conj_apply,inv_inv,mul_assoc]
  refine ⟨g,hgG,?_,?_⟩
  · have he := congrArg (Subgroup.map (MulAut.conj f⁻¹).toMonoidHom) hgen
    rw [Subgroup.map_sup,←Q_act,←Q_act,←stabilizer_act,hfa,hverts 1,
      hcancel,htransport] at he
    exact he
  · intro hbad
    apply hne
    apply (map_le_map_iff_of_injective (f := (MulAut.conj f⁻¹).toMonoidHom) (MulAut.conj f⁻¹).injective).mp
    rw [←Z_act,←Q_act,hverts 2,hcancel,htransport]
    exact hbad

include h e hz hk in
/-- Construct the next critical path, generation and transporter together,
then apply the raw comparison on that same literal path. -/
theorem plane_selected_critical_comparison
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hmidgen : Q Rg (p.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 3) =
      stabilizer Rg (p.walk.getVert 2))
    (hback : 2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg a)) :
    ∃ s, Adjacent Rg a s ∧
      Q Rg s ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg a ∧
      ∃ g ∈ stabilizer Rg a, act Rg g (p.walk.getVert 1) = s ∧
        ∃ q : CriticalPath Rg (sourceGeometry h)
          (act Rg g (p.walk.getVert 2)) (p.walk.getVert 2),
          q.walk.getVert 1 = s ∧ q.walk.getVert 2 = a ∧
          ∀ K : Subgroup (FreeAmalgam Rg),
            K ≤ Z Rg (act Rg g (p.walk.getVert 2)) ⊓ Q Rg (p.walk.getVert 2) →
            ⁅K,Z Rg z ⊓ Q Rg a⁆ = ⊥ ∧ ⁅K,Z Rg z⁆ ≤ ⁅Z Rg a,Z Rg z⁆ := by
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hav : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hcv : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨g,hg,hgen,hn⟩ :=
    plane_generating_critical_candidate h e hz hk u hR hb4 hsmall p hmidgen hback
  let s := act Rg g (p.walk.getVert 1)
  let d := act Rg g (p.walk.getVert 2)
  have has : Adjacent Rg a s := by
    simpa only [show act Rg g a = a from hg] using
      (adjacent_act_iff Rg g _ _).mpr hav
  have hds : Adjacent Rg d s := (adjacent_act_iff Rg g _ _).mpr hcv
  have hd : color Rg d = false := (action_preserves_color Rg g _).trans
    ((p.vertex_color (by omega)).mpr (by decide))
  let w : (cosetGraph Rg).Walk d a :=
    .cons ((cosetGraph_adj Rg _ _).mpr hds)
      (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg has)) .nil)
  have hw : w.length = 2 := rfl
  have hns : ¬ Z Rg d ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    simpa only [hl,Nat.reduceSub] using hn
  let q := p.prepend_two (Nat.le_of_lt hb) hd w hw hns
  have he : p.walk.getVert (p.walk.length-2) = p.walk.getVert 2 := by rw [hl]
  have hq : ∃ q : CriticalPath Rg (sourceGeometry h) d
      (p.walk.getVert (p.walk.length-2)),
      q.walk.getVert 1 = s ∧ q.walk.getVert 2 = a := by
    refine ⟨q,?_,?_⟩
    · simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
        hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
        SimpleGraph.Walk.getVert_zero]
    · simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using
        p.prepend_two_overlap (Nat.le_of_lt hb) hd w hw hns (i := 0) (by omega)
  rw [he] at hq
  obtain ⟨q,hq1,hq2⟩ := hq
  refine ⟨s,has,hgen,g,hg,rfl,q,hq1,hq2,?_⟩
  intro K hK
  exact plane_raw_shifted_kernels_of_midpoint_generation h e hz hk u hR hb4 hsmall
    p hds has K hK hgen g hg rfl hmidgen hback


include h e hz hk in
/-- The original outer selector now admits a next genuine critical path,
with the same generating edges, actual transporter and full-kernel comparison.
There is no additional next-path or next-slice premise. -/
theorem plane_selected_successive_critical_comparison
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2))) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf (L ⊔ R),
      let x := (embedM Rg r)⁻¹
      ∃ p' : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
        (∀ i, p'.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
        (Q Rg t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        Q Rg t ⊔ Q Rg (act Rg x t) = stabilizer Rg (alpha Rg) ∧
        ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
          let d := act Rg g (p.walk.getVert 2)
          let comparison := fun w (v : CriticalPath Rg (sourceGeometry h) (alpha Rg) w) =>
            ∃ q : CriticalPath Rg (sourceGeometry h) d (v.walk.getVert 2),
              q.walk.getVert 1 = t ∧
              (∀ i ≤ 2, q.walk.getVert (i+2) = v.walk.getVert i) ∧
              ∃ s, Adjacent Rg d s ∧
                Q Rg s ⊔ Q Rg (q.walk.getVert 1) = stabilizer Rg d ∧
                ∃ k ∈ stabilizer Rg d, act Rg k (q.walk.getVert 1) = s ∧
                  ∃ q' : CriticalPath Rg (sourceGeometry h)
                    (act Rg k (q.walk.getVert 2)) (q.walk.getVert 2),
                    q'.walk.getVert 1 = s ∧ q'.walk.getVert 2 = d ∧
                  ∀ K : Subgroup (FreeAmalgam Rg),
                    K ≤ Z Rg (act Rg k (q.walk.getVert 2)) ⊓ Q Rg (q.walk.getVert 2) →
                    ⁅K,Z Rg (v.walk.getVert 2) ⊓ Q Rg d⁆ = ⊥ ∧
                      ⁅K,Z Rg (v.walk.getVert 2)⁆ ≤ ⁅Z Rg d,Z Rg (v.walk.getVert 2)⁆
          comparison z p ∨ comparison (act Rg x z) p' := by
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have ha1 : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hc1 : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨t,hat,r,hr,p',hverts,hps,hgen,hpair,hnorm,hinside,g,hg,hgt,hstrict,halt⟩ :=
    plane_small_critical_backward_shift h e hz hk u hR p (hsmall _ _ p) hc1 hs
  let x := (embedM Rg r)⁻¹
  have hx : x ∈ stabilizer Rg (alpha Rg) := by
    change x ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨r⁻¹,by rw [map_inv]⟩
  have hat' : Adjacent Rg (alpha Rg) (act Rg x t) := by
    rw [←show act Rg x (alpha Rg) = alpha Rg from hx]
    exact (adjacent_act_iff Rg x _ _).mpr hat
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hat] at hgen hpair
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hat'] at hpair
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl ha1] at hnorm hinside
  have hfirst : Q Rg t ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg (alpha Rg) := by
    apply le_antisymm
    · exact sup_le (fun _ hv => hv.2 _ (adjacent_symm Rg hat))
        (fun _ hv => hv.2 _ (adjacent_symm Rg ha1))
    · rw [←hgen]
      exact sup_le (sup_le le_sup_left ((le_sup_left.trans hinside).trans le_sup_right))
        ((le_sup_right.trans hinside).trans le_sup_right)
  have hQfirst : Q Rg (p'.walk.getVert 1) = Q Rg (p.walk.getVert 1) := by
    rw [hverts 1,Q_act]
    exact mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (Q Rg (p.walk.getVert 1) : Set (FreeAmalgam Rg))).inv_mem hnorm)
  have hc : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  refine ⟨t,hat,r,hr,p',hverts,hgen,hpair,g,hg,hgt,?_⟩
  have hl' : p'.walk.length = 4 := p'.length_eq_b.trans hb4
  have cast_end {d v w : Vertex Rg} (q : CriticalPath Rg (sourceGeometry h) d v)
      (he : v = w) : ∃ q' : CriticalPath Rg (sourceGeometry h) d w,
        ∀ i, q'.walk.getVert i = q.walk.getVert i := by
    subst w
    exact ⟨q,fun _ => rfl⟩
  have finish {w : Vertex Rg}
      (v : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (q : CriticalPath Rg (sourceGeometry h) (act Rg g (p.walk.getVert 2)) (v.walk.getVert 2))
      (hq1 : q.walk.getVert 1 = t)
      (hqv : ∀ i ≤ 2, q.walk.getVert (i+2) = v.walk.getVert i)
      (hgenq : Q Rg t ⊔ Q Rg (v.walk.getVert 1) = stabilizer Rg (alpha Rg))
      :
      ∃ s, Adjacent Rg (act Rg g (p.walk.getVert 2)) s ∧
        Q Rg s ⊔ Q Rg (q.walk.getVert 1) =
          stabilizer Rg (act Rg g (p.walk.getVert 2)) ∧
        ∃ k ∈ stabilizer Rg (act Rg g (p.walk.getVert 2)),
          act Rg k (q.walk.getVert 1) = s ∧
          ∃ q' : CriticalPath Rg (sourceGeometry h)
            (act Rg k (q.walk.getVert 2)) (q.walk.getVert 2),
            q'.walk.getVert 1 = s ∧ q'.walk.getVert 2 = (act Rg g (p.walk.getVert 2)) ∧
          ∀ K : Subgroup (FreeAmalgam Rg),
            K ≤ Z Rg (act Rg k (q.walk.getVert 2)) ⊓ Q Rg (q.walk.getVert 2) →
            ⁅K,Z Rg (v.walk.getVert 2) ⊓ Q Rg (act Rg g (p.walk.getVert 2))⁆ = ⊥ ∧
              ⁅K,Z Rg (v.walk.getVert 2)⁆ ≤
                ⁅Z Rg (act Rg g (p.walk.getVert 2)),Z Rg (v.walk.getVert 2)⁆ := by
    have hqa : q.walk.getVert 2 = alpha Rg := by
      simpa only [SimpleGraph.Walk.getVert_zero] using hqv 0 (by omega)
    apply plane_selected_critical_comparison h e hz hk u hR hb4 hsmall q
    · rw [hqa,hq1,hqv 1 (by omega)]
      exact hgenq
    · simpa only [hqa] using hstrict
  rcases halt with ⟨q,hq1,hqv⟩ | ⟨q,hq1,hqv⟩
  · obtain ⟨q',hq'⟩ := cast_end q (show p.walk.getVert (p.walk.length-2) =
        p.walk.getVert 2 by rw [hl])
    have hqv' : ∀ i ≤ 2, q'.walk.getVert (i+2) = p.walk.getVert i :=
      fun i hi => (hq' (i+2)).trans (hqv i (by omega))
    have hq1' := (hq' 1).trans hq1
    exact Or.inl ⟨q',hq1',hqv',finish p q' hq1' hqv' hfirst⟩
  · obtain ⟨q',hq'⟩ := cast_end q (show p'.walk.getVert (p'.walk.length-2) =
        p'.walk.getVert 2 by rw [hl'])
    have hqv' : ∀ i ≤ 2, q'.walk.getVert (i+2) = p'.walk.getVert i :=
      fun i hi => (hq' (i+2)).trans (hqv i (by omega))
    have hq1' := (hq' 1).trans hq1
    exact Or.inr ⟨q',hq1',hqv',finish p' q' hq1' hqv' (by rwa [hQfirst])⟩

omit hk in
include h e hz in
/-- Whole-core application of the next genuine critical selection and
comparison, retaining both full moving covers and the original cubic kernel. -/
theorem coreExhaustion_or_cubic_selected_critical_comparison :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
          ∀ z (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) →
        ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf (L ⊔ R),
          let x := (embedM Rg r)⁻¹
          ∃ p' : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
            (∀ i, p'.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
            (Q Rg t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
            Q Rg t ⊔ Q Rg (act Rg x t) = stabilizer Rg (alpha Rg) ∧
            ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
              let d := act Rg g (p.walk.getVert 2)
              let comparison := fun w (v : CriticalPath Rg (sourceGeometry h) (alpha Rg) w) =>
                ∃ q : CriticalPath Rg (sourceGeometry h) d (v.walk.getVert 2),
                  q.walk.getVert 1 = t ∧
                  (∀ i ≤ 2, q.walk.getVert (i+2) = v.walk.getVert i) ∧
                  ∃ s, Adjacent Rg d s ∧
                    Q Rg s ⊔ Q Rg (q.walk.getVert 1) = stabilizer Rg d ∧
                    ∃ k ∈ stabilizer Rg d, act Rg k (q.walk.getVert 1) = s ∧
                      ∃ q' : CriticalPath Rg (sourceGeometry h)
                        (act Rg k (q.walk.getVert 2)) (q.walk.getVert 2),
                        q'.walk.getVert 1 = s ∧ q'.walk.getVert 2 = d ∧
                      ∀ K : Subgroup (FreeAmalgam Rg),
                        K ≤ Z Rg (act Rg k (q.walk.getVert 2)) ⊓ Q Rg (q.walk.getVert 2) →
                        ⁅K,Z Rg (v.walk.getVert 2) ⊓ Q Rg d⁆ = ⊥ ∧
                          ⁅K,Z Rg (v.walk.getVert 2)⁆ ≤ ⁅Z Rg d,Z Rg (v.walk.getVert 2)⁆
              comparison z p ∨ comparison (act Rg x z) p')) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · refine Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,?_⟩⟩
    intro hb4 hsmall z p hstrict
    exact plane_selected_successive_critical_comparison h e hz hk u hplane hb4 hsmall p hstrict

omit hk in
include h e hz in
/-- Literal C.1.32 application of the successive comparison, with the
original projection, radical, full attachments and both covers retained. -/
theorem rankTwo_or_cubic_selected_critical_comparison :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
          ∀ z (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) →
        ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf (L ⊔ R),
          let x := (embedM Rg r)⁻¹
          ∃ p' : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
            (∀ i, p'.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
            (Q Rg t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
            Q Rg t ⊔ Q Rg (act Rg x t) = stabilizer Rg (alpha Rg) ∧
            ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
              let d := act Rg g (p.walk.getVert 2)
              let comparison := fun w (v : CriticalPath Rg (sourceGeometry h) (alpha Rg) w) =>
                ∃ q : CriticalPath Rg (sourceGeometry h) d (v.walk.getVert 2),
                  q.walk.getVert 1 = t ∧
                  (∀ i ≤ 2, q.walk.getVert (i+2) = v.walk.getVert i) ∧
                  ∃ s, Adjacent Rg d s ∧
                    Q Rg s ⊔ Q Rg (q.walk.getVert 1) = stabilizer Rg d ∧
                    ∃ k ∈ stabilizer Rg d, act Rg k (q.walk.getVert 1) = s ∧
                      ∃ q' : CriticalPath Rg (sourceGeometry h)
                        (act Rg k (q.walk.getVert 2)) (q.walk.getVert 2),
                        q'.walk.getVert 1 = s ∧ q'.walk.getVert 2 = d ∧
                      ∀ K : Subgroup (FreeAmalgam Rg),
                        K ≤ Z Rg (act Rg k (q.walk.getVert 2)) ⊓ Q Rg (q.walk.getVert 2) →
                        ⁅K,Z Rg (v.walk.getVert 2) ⊓ Q Rg d⁆ = ⊥ ∧
                          ⁅K,Z Rg (v.walk.getVert 2)⁆ ≤ ⁅Z Rg d,Z Rg (v.walk.getVert 2)⁆
              comparison z p ∨ comparison (act Rg x z) p')) :=
  (coreExhaustion_or_cubic_selected_critical_comparison h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
