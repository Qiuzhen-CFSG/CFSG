module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.WholeSection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.FullRadical
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.FixedAttachment
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.CriticalRootRadical
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.PairedRadical
public import Theory.Representation.BinarySylowFixedSpace
public import Theory.SpecificGroups.SymplecticFour.QuadraticSmallMovers
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedIndex

/-!
# The full Sylow central layer and the large critical images

The whole core modulo its complete component-fixed subgroup contains the
natural module with trivial quotient and has no global fixed vectors.
Averaging a Sylow-fixed vector over the odd number of Sylow cosets therefore
places that vector in the natural submodule. When the actual radical image
is Sylow, lift it through the original two-core kernel at each incident edge.
Every generating edge omega-center then lies in U C_Q(L). Its fixed factor
is retained in the common edge center, proving Z = U Z_t without an order-q
critical-image assumption.

Fixed-vector lifting through the original natural cover bounds critical
movement on U by q squared. The full fixed supplement makes this the index
on Z as well. Reciprocal critical indices consequently are both q or both
q squared. Combining this with the proved parabolic and order-q centrality
arguments shows that failure of full-radical centrality forces the Sylow
case and two images of order q squared, on the same actual critical path.

Source: Meierfrankenfeld--Stellmacher (1993), MS93 (3.7)(1), printed p.873,
the reduction preceding the fixed-centralizer count. The exact count
|C_(Z'/(Z' intersect Q))(T)| = q is still needed for the source contradiction.
Normality and order q squared alone do not imply it. No critical-pair
selection or final field restriction is asserted here.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
open Theory.SpecificGroups.SymplecticFour
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem component_eq_top (g : Geometry d.radical) (hb : 0 < g.b d.radical) :
    replacementComponent d = ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  have hh := congrArg (fun A : Subgroup d.overgroup => A.map q)
    (replacement_inner_of_positive h d g hb)
  rw [Subgroup.map_sup,show (pCore 2 d.overgroup).map q = ⊥ from
    (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
  exact hh

namespace EdgeMarking
variable {h d} {a t : Vertex d.radical} (c : EdgeMarking h d a t)

omit [Finite F] [CharP F 2] in
/-- A Sylow image lifts through the literal full two-core kernel. -/
theorem exists_edge_sylow (S : Sylow 2 (Sp F))
    (hS : (S : Subgroup (Sp F)) = c.action.range) :
    ∃ P : Sylow 2 (stabilizer d.radical a),
      (P : Subgroup (stabilizer d.radical a)) =
        (Q d.radical t).subgroupOf (stabilizer d.radical a) := by
  have hk : c.quotient.ker = (Q d.radical a).subgroupOf (stabilizer d.radical a) := by
    rw [←c.kernel,subgroupOf_map_subtype_eq]
  have hP : IsPGroup 2 c.quotient.ker := by
    rw [hk,←c.core_eq]
    exact (pCore_isPGroup.map c.embedding).comap_subtype
  refine ⟨S.comapOfKerIsPGroup c.quotient hP
    (by rw [MonoidHom.range_eq_top.mpr c.onto]; exact le_top),?_⟩
  change (S : Subgroup (Sp F)).comap c.quotient = _
  rw [hS,action,MonoidHom.range_comp,inclusion_range,comap_map_eq_self]
  rw [hk]
  exact comap_mono c.core_le_edge

end EdgeMarking

/-- Odd coset averaging puts every Sylow-fixed core element in the natural
subgroup times the complete component-fixed attachment. -/
theorem sylow_fixed_core_le_moving_sup_fixed
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a : Vertex d.radical} (ha : color d.radical a = false)
    (P : Sylow 2 (stabilizer d.radical a)) :
    Q d.radical a ⊓ centralizer
      (((P : Subgroup (stabilizer d.radical a)).map (stabilizer d.radical a).subtype :
        Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ≤
      U d.radical a ⊔ fixedCore d.radical a := by
  obtain ⟨E,hE,s,γ,hγ,i,hi,hd,hrange,_⟩ := wholeKernel_natural_dualCover h d g hb ha
  have hγonto : Function.Surjective γ := by
    apply MonoidHom.range_eq_top.mp
    rw [hγ,component_eq_top h d g (by omega)]
  let τ := s.action.comp s.quotient
  let W := i.toLinearMap.range
  have htrivial (k : stabilizer d.radical a) (v : s.Carrier) : τ k v-v ∈ W := by
    obtain ⟨l,hl⟩ := hγonto (s.quotient k)
    change s.action (s.quotient k) v-v ∈ W
    rw [←hl]
    exact hd.1 l v
  let := finite_stabilizer d.radical a
  intro x hx
  let v := (s.sectionData.coordinates ⟨x,hx.1⟩).toAdd
  have hv : v ∈ fixedSpace τ (P : Subgroup (stabilizer d.radical a)) := by
    intro k
    have hc := hx.2 k.val.val (mem_map_of_mem (stabilizer d.radical a).subtype k.property)
    have hh := s.sectionData.equivariant k.val ⟨x,hx.1⟩
    have he : (⟨k.val.val*x*k.val.val⁻¹,
        (mem_normalizer_iff.mp (s.sectionData.normalized k.val.property) x).mp hx.1⟩ :
        Q d.radical a) = ⟨x,hx.1⟩ := by
      apply Subtype.ext
      change k.val.val*x*k.val.val⁻¹=x
      rw [hc,mul_inv_cancel_right]
    rw [he] at hh
    exact hh.symm
  obtain ⟨w,hw,hvw⟩ := BinarySylowFixedSpace.fixed_lift_mod_trivial_quotient
    τ P W htrivial v hv
  have hw0 : w=0 := by
    apply hd.2.le
    intro l
    obtain ⟨k,hk⟩ := s.quotient_surjective (γ l)
    change s.action (γ l) w=w
    rw [←hk]
    exact hw k
  rw [hw0,sub_zero] at hvw
  obtain ⟨u,hu,huv⟩ := (hrange v).mp hvw
  have hk : x*(u : FreeAmalgam d.radical)⁻¹ ∈ fixedCore d.radical a := by
    apply (s.sectionData.coordinates_eq_one_iff
      (⟨x,hx.1⟩*u⁻¹)).mp
    rw [map_mul,map_inv]
    have he : s.sectionData.coordinates u = s.sectionData.coordinates ⟨x,hx.1⟩ :=
      Multiplicative.toAdd.injective huv
    rw [he,mul_inv_cancel]
  have hm := (U d.radical a ⊔ fixedCore d.radical a).mul_mem
    (mem_sup_right hk) (mem_sup_left hu)
  simpa only [inv_mul_cancel_right] using hm

/-- Each generating edge omega-center lies in U C_Q(L) when the original
marked full radical image is Sylow. The complete attachment remains. -/
theorem Z_le_moving_sup_fixed_of_sylow
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (c : EdgeMarking h d a t) (S : Sylow 2 (Sp F))
    (hS : (S : Subgroup (Sp F)) = c.action.range) :
    Z d.radical a ≤ U d.radical a ⊔ fixedCore d.radical a := by
  have hZQ : Z d.radical a ≤ Q d.radical a :=
    (g.omega_bound a ha (by rw [g.distance_constant a ha]; change 0 < g.b d.radical; omega)).trans
      (omegaCenter_le _)
  rw [Z,if_pos ha]
  apply iSup_le
  intro b
  apply iSup_le
  intro hab
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) ha hab
  obtain ⟨P,hP⟩ := c'.exists_edge_sylow S (hS.trans (c.action_range.trans c'.action_range.symm))
  have hPm : (P : Subgroup (stabilizer d.radical a)).map
      (stabilizer d.radical a).subtype = Q d.radical b := by
    rw [hP,map_subgroupOf_eq_of_le c'.edge_le]
  apply (show edgeOmega d.radical b ≤ Q d.radical a ⊓
      centralizer (Q d.radical b : Set (FreeAmalgam d.radical)) from ?_).trans
    (by rw [←hPm]; exact sylow_fixed_core_le_moving_sup_fixed h d g hb ha P)
  exact le_inf ((show edgeOmega d.radical b ≤ Z d.radical a from by
    rw [Z,if_pos ha]
    exact le_iSup_of_le b (le_iSup_of_le hab le_rfl)).trans hZQ)
      (fun x hx => (mem_omegaCenter_iff.mp hx).2.2)

/-- The full Sylow case has Z = U Z_t before any order-q critical pair is
selected. The fixed factor is included in the actual midpoint omega-center. -/
theorem Z_eq_moving_sup_edge_of_sylow
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (c : EdgeMarking h d a t) (S : Sylow 2 (Sp F))
    (hS : (S : Subgroup (Sp F)) = c.action.range) :
    Z d.radical a = U d.radical a ⊔ Z d.radical t := by
  have hZX := g.omega_bound a ha (by
    rw [g.distance_constant a ha]; change 0 < g.b d.radical; omega)
  have hUZ : U d.radical a ≤ Z d.radical a := U_le_Z a
  have hUD : U d.radical a ≤ centralizer (fixedCore d.radical a : Set (FreeAmalgam d.radical)) :=
    (hUZ.trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a ha))).trans (centralizer_le inf_le_left)
  apply le_antisymm ?_ (sup_le hUZ (Sp4Four.edge_Z_le_endpoint d.radical ha hat))
  intro x hx
  have hprod := Z_le_moving_sup_fixed_of_sylow h d g hb ha c S hS hx
  rw [←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _
    (hUD.trans (Subgroup.centralizer_le_normalizer _))] at hprod
  obtain ⟨u,hu,v,hv,rfl⟩ := hprod
  have hvX : v ∈ X d.radical a := by
    have hh := (X d.radical a).mul_mem
      ((X d.radical a).inv_mem (hZX (hUZ hu))) (hZX hx)
    simpa only [inv_mul_cancel_left] using hh
  exact mul_mem (mem_sup_left hu) (mem_sup_right
    (replacement_fixed_X_le_edge h d (g := g) (by omega) ha hat ⟨hvX,hv.2⟩))

omit h d in
private theorem centralizer_index_of_central_factor {G : Type*} [Group G]
    (T A B C : Subgroup G) [Finite T]
    (hAB : A ⊔ B = T) (hTC : T ≤ normalizer (C : Set G))
    (hAC : A ≤ centralizer (C : Set G)) :
    (centralizer (C : Set G)).relIndex T =
      (centralizer (C : Set G)).relIndex B := by
  let N := (centralizer (C : Set G)).subgroupOf T
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (hTC.trans (normalizer_le_normalizer_centralizer C))
  have hBT : B ≤ T := le_sup_right.trans_eq hAB
  have htop : B.subgroupOf T ⊔ N = ⊤ := by
    apply top_unique
    have hAT : A ≤ T := le_sup_left.trans_eq hAB
    have hjoin : A.subgroupOf T ⊔ B.subgroupOf T = ⊤ := by
      rw [←subgroupOf_sup hAT hBT,hAB,subgroupOf_self]
    rw [←hjoin]
    exact sup_le (fun x hx => mem_sup_right (hAC hx)) le_sup_left
  calc
    _ = N.relIndex (⊤ : Subgroup T) := by rw [relIndex_top_right]; rfl
    _ = N.relIndex (B.subgroupOf T) := by rw [←htop,relIndex_sup_right]
    _ = _ := relIndex_subgroupOf hBT

open Representation.SymplecticFourOrthogonalCover in
private theorem critical_moving_centralizer_index_le_square
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : 0 < g.b d.radical) :
    (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z) ≤ (2^n)^2 := by
  let := replacementComponent_normal h d
  let s := replacementMovedSection h d
  obtain ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.end_color
  have hFc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  have hCtop := component_eq_top h d g hb
  let κC := κ.codRestrict (replacementComponent d) (fun x => hCtop ▸ mem_top (κ x))
  have hZS : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (g.exists_critical a path.start_color) path.critical.1.le
  let β := e.groupEquiv.toMonoidHom.comp (κC.comp (inclusion hZS))
  have hβ (x : Z d.radical a) (v : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (β x) v)) =
        x.val*j (Multiplicative.ofAdd v)*x.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC (inclusion hZS x)))) v)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj (inclusion hZS x) v
  let α := (commutator (Sp E.Carrier)).subtype.comp β
  have hαr : α.range=β.range.map (commutator (Sp E.Carrier)).subtype :=
    MonoidHom.range_comp _ _
  have hquad := CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_embedded_natural_actor_quadratic
    path hb (MovedSection.coverAction s e) (MovedSection.coverProjection s e) he
    j hj hjr β hβ
  have hquadα : ∀ x ∈ α.range, ∀ y ∈ α.range, ∀ v : Vector E.Carrier,
      x • (y • v-v)=y • v-v := by
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ v
    exact hquad (β x) ⟨x,rfl⟩ (β y) ⟨y,rfl⟩ v
  have hbound := quadratic_natural_fixed_index_le_square α.range hquadα
  have hi := embedded_centralizer_index (MovedSection.coverAction s e)
    (U d.radical z) (Z d.radical a) j hj hjr β hβ
  rw [hi,fixedCodim_of_binaryCover (MovedSection.coverProjection s e) he]
  let τ := restrictScalars (k := ZMod 2) (symplecticNatural (k := E.Carrier) 2)
  have hm := fixedCodim_map_equivariant (binaryNatural (K := E.Carrier)) τ
    (commutator (Sp E.Carrier)).subtype (LinearEquiv.refl _ _) (fun _ _ => rfl) β.range
  rw [←hαr] at hm
  rw [hm]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hFc] at hbound
  exact hbound

/-- The original natural quadratic action bounds the full critical Z-image
by q squared, using the full Sylow central-layer decomposition. -/
theorem critical_index_le_field_square_of_sylow
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (S : Sylow 2 (Sp F))
    (hS : (S : Subgroup (Sp F)) = c.action.range) :
    (Q d.radical z).relIndex (Z d.radical a) ≤ (2^n)^2 := by
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  have hZaS : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (g.exists_critical a path.start_color) path.critical.1.le
  have hZzT : Z d.radical z ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
      g.distance_constant z path.end_color]
    change 1 < g.b d.radical
    omega
  have ht : color d.radical t = true := by
    have hn := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all [path.start_color]
  have hZt : Z d.radical t = omegaCenter (Q d.radical t) := by simp [Z,ht,edgeOmega]
  have hfix : Z d.radical t ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) := by
    rw [hZt]
    intro x hx y hy
    exact (mem_omegaCenter_iff.mp hx).2.2 y (hZzT hy)
  let := finite_Z d.radical a
  have hi := centralizer_index_of_central_factor (Z d.radical a) (Z d.radical t)
    (U d.radical a) (Z d.radical z)
    (by rw [sup_comm]; exact (Z_eq_moving_sup_edge_of_sylow h d g hb path.start_color hat c S hS).symm)
    (hZaS.trans (Z_normalized d.radical z)) hfix
  have hCZ : (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).subgroupOf
      (Z d.radical a) = (Q d.radical z).subgroupOf (Z d.radical a) := by
    rw [←MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) z path.end_color]
    ext x
    exact ⟨fun hx => ⟨hZaS x.property,hx⟩,fun hx => hx.2⟩
  have he : (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical a) = (Q d.radical z).relIndex (Z d.radical a) := by
    change ((centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).subgroupOf
      (Z d.radical a)).index = _
    rw [hCZ]
    rfl
  rw [he] at hi
  rw [hi]
  exact critical_moving_centralizer_index_le_square h d rev (by omega)

/-- The two literal critical images are simultaneously of order q or of
order q squared in the full Sylow branch. -/
theorem paired_critical_indices_of_sylow
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (S : Sylow 2 (Sp F))
    (hS : (S : Subgroup (Sp F)) = c.action.range) :
    ((Q d.radical z).relIndex (Z d.radical a) = 2^n ∧
      (Q d.radical a).relIndex (Z d.radical z) = 2^n) ∨
    ((Q d.radical z).relIndex (Z d.radical a) = (2^n)^2 ∧
      (Q d.radical a).relIndex (Z d.radical z) = (2^n)^2) := by
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hS' : (S : Subgroup (Sp F)) = c'.action.range :=
    hS.trans (c.action_range.trans c'.action_range.symm)
  have ha := critical_index_le_field_square_of_sylow h d path hb hat hzt c S hS
  have hz := critical_index_le_field_square_of_sylow h d rev hb hzt hat c' S hS'
  by_cases hsmall : (Q d.radical z).relIndex (Z d.radical a) < (2^n)^2
  · exact Or.inl (replacement_critical_indices_eq_field_of_small h d path (by omega) hsmall)
  by_cases hsmall' : (Q d.radical a).relIndex (Z d.radical z) < (2^n)^2
  · exact Or.inl (replacement_critical_indices_eq_field_of_small h d rev (by omega) hsmall').symm
  exact Or.inr ⟨by omega,by omega⟩

/-- The first reduction in source (3.7)(1): noncentrality forces the Sylow
case, both full central-layer decompositions and both critical image orders
q squared. The separate fixed-centralizer count is not assumed or concluded. -/
theorem noncentral_full_radical_has_large_critical_images
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hnc : ¬ ⁅Z d.radical z,Q d.radical t⁆ ≤ Q d.radical a) :
    ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) = c.action.range ∧
      Z d.radical a = U d.radical a ⊔ Z d.radical t ∧
      Z d.radical z = U d.radical z ⊔ Z d.radical t ∧
      (Q d.radical z).relIndex (Z d.radical a) = (2^n)^2 ∧
      (Q d.radical a).relIndex (Z d.radical z) = (2^n)^2 := by
  have hZzT : Z d.radical z ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
      g.distance_constant z path.end_color]
    change 1 < g.b d.radical
    omega
  obtain ⟨S,hS⟩ : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) = c.action.range := by
    rcases marked_radical_elementary_or_sylow h d g (by omega) hsat with he | hs
    · let : IsElementaryAbelian 2 c.action.range := c.action_range.symm ▸ he
      exact False.elim (hnc ((commutator_mono hZzT le_rfl).trans
        (c.full_radical_commutator_le_core inferInstance)))
    · simpa only [c.action_range] using hs
  have hlarge : (Q d.radical z).relIndex (Z d.radical a) = (2^n)^2 ∧
      (Q d.radical a).relIndex (Z d.radical z) = (2^n)^2 := by
    rcases paired_critical_indices_of_sylow h d path hb hat hzt c S hS with he | he
    · exact False.elim (hnc (full_radical_centralizes_critical_root h d path hb c c' he.1).1)
    · exact he
  exact ⟨S,hS,Z_eq_moving_sup_edge_of_sylow h d g hb path.start_color hat c S hS,
    Z_eq_moving_sup_edge_of_sylow h d g hb path.end_color hzt c' S
      (hS.trans (c.action_range.trans c'.action_range.symm)),hlarge⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
