module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.SmallRadicalEdges
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.PairedOrbit
public import Theory.Representation.BinaryConjugationSection.CentralDisplacement
public import Theory.Representation.DualCoverFromConjugationSection
public import Theory.Representation.BinaryConjugationSection.FixedIndex

/-!
# The whole two-core in the field-sized replacement branch

At distance two, Frattini detection identifies the full commutator core with
U at every original-color vertex. Central elementary displacement then makes
Q/C_Q(L) an elementary section, even when Q itself is nonabelian. Its action
descends through the literal vertex quotient, with all component-fixed
attachments retained in the kernel. The original natural cover embeds its
natural quotient in this section.

If the replacement image has order q, the paired edge calculation bounds
its whole-kernel critical centralizer index by q. Four conjugates of that
critical root generate the component, bounding the section dimension by 4n.
The embedded natural module attains this bound, so Q = U C_Q(L). The final
consumer discharges the order-q premise in the proper nonsylow branch of
the original odd-index comparison. This does not assert radical saturation,
vanishing of the fixed factor, or the field-degree restriction.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.6)--(3.7), printed pp.870--877; the four-root bound is (1.1)(ii)(1).
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

include h

/-- The whole commutator core equals the original moving layer at every original-color vertex. -/
theorem replacement_core_eq_U_of_distance_two
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a : Vertex d.radical} (ha : color d.radical a = false) :
    core d.radical a = U d.radical a := by
  have he : core d.radical (alpha d.radical) = U d.radical (alpha d.radical) := by
    let := replacement_component_normal h d
    have hp : IsPPerfect 2 (K.subgroupOf d.overgroup) := by
      rw [←replacement_residual h d]
      exact isPPerfect_pResidual 2
    have hc := commutator_eq_of_le_frattini_sup_of_isPPerfect
      (pCore 2 d.overgroup) (K.subgroupOf d.overgroup)
      (omegaCenterIn (pCore 2 d.overgroup)) pCore_isPGroup hp
      (map_subtype_le _) (replacement_frattini_small_of_graph h d
        (replacement_graph_core_frattini_bound h d g hb))
    rw [core_alpha d.radical (replacement_isPGroup h d) (replacement_core_le h d)
      (replacement_residual h d),hc,←replacement_initialCore_eq h d]
    rw [U,Z_alpha_eq_omegaOrbit,Ltilde_alpha,replacement_residual h d,←map_commutator]
  obtain ⟨v,rfl⟩ := exists_mVertex_of_color d.radical ha
  have hv : mVertex d.radical v = act d.radical v (alpha d.radical) := by
    simp [alpha,act_mVertex]
  rw [hv,core_act,U_act,he]


universe u v
/-- The actual two-core modulo its entire component centralizer. -/
structure WholeKernelQuotient {M : Type u} [Group M]
    (T : Subgroup M) (a : Vertex T) (J : Type v) [Group J] where
  Carrier : Type u
  [addCommGroup : AddCommGroup Carrier]
  [moduleInst : Module (ZMod 2) Carrier]
  [finite : Finite Carrier]
  quotient : stabilizer T a →* J
  quotient_surjective : Function.Surjective quotient
  quotient_kernel : quotient.ker.map (stabilizer T a).subtype = Q T a
  action : Representation (ZMod 2) J Carrier
  sectionData : BinaryConjugationSection (stabilizer T a) (Q T a)
    (Q T a ⊓ centralizer (Ltilde T a : Set (FreeAmalgam T))) (action.comp quotient)
  fixed_eq_bot : fixedSpace action
    (((Ltilde T a).subgroupOf (stabilizer T a)).map quotient) = ⊥
attribute [instance] WholeKernelQuotient.addCommGroup WholeKernelQuotient.moduleInst
  WholeKernelQuotient.finite

/-- The whole two-core admits the original local quotient action after dividing
by its full fixed subgroup; no elementary structure of the two-core is assumed. -/
theorem replacement_wholeKernelQuotient_over
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a : Vertex d.radical} (ha : color d.radical a = false)
    {J : Type*} [Group J] (κ : stabilizer d.radical a →* J)
    (hκ : Function.Surjective κ)
    (hκQ : κ.ker.map (stabilizer d.radical a).subtype = Q d.radical a) :
    ∃ s : WholeKernelQuotient d.radical a J, s.quotient = κ := by
  let S := stabilizer d.radical a
  let A := Q d.radical a
  let L₀ := Ltilde d.radical a
  let U₀ := U d.radical a
  let C₀ := A ⊓ centralizer (L₀ : Set (FreeAmalgam d.radical))
  have hAS : A ≤ S := fun _ hx => hx.1
  have hLS : L₀ ≤ S := Ltilde_le_stabilizer _
  have hSL : S ≤ normalizer (L₀ : Set (FreeAmalgam d.radical)) := by
    have ht := le_normalizer_map (H := pResidual 2 S) S.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at ht
    exact ht
  have hSN : S ≤ normalizer (C₀ : Set (FreeAmalgam d.radical)) :=
    (le_inf (Q_normalized d.radical a)
      (hSL.trans (normalizer_le_normalizer_centralizer L₀))).trans
      inf_normalizer_le_normalizer_inf
  let : (C₀.subgroupOf A).Normal :=
    normal_subgroupOf_of_le_normalizer (hAS.trans hSN)
  have hN : C₀.subgroupOf A =
      (centralizer (L₀ : Set (FreeAmalgam d.radical))).subgroupOf A := by
    ext x
    exact ⟨fun hx => hx.2,fun hx => ⟨x.property,hx⟩⟩
  let : ((centralizer (L₀ : Set (FreeAmalgam d.radical))).subgroupOf A).Normal :=
    hN ▸ inferInstance
  have hmove : ⁅A,L₀⁆ ≤ U₀ := (replacement_core_eq_U_of_distance_two h d g hb ha).le
  have hc : U₀ ≤ centralizer (A : Set (FreeAmalgam d.radical)) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (le_antisymm ((commutator_mono (U_le_Z a) le_rfl).trans_eq
        (Z_centralizes_Q d.radical a ha)) bot_le)
  let : IsElementaryAbelian 2 U₀ := replacement_vertex_moving_elementary h d ha
  let : IsElementaryAbelian 2
      (A ⧸ (centralizer (L₀ : Set (FreeAmalgam d.radical))).subgroupOf A) :=
    central_displacement_quotient_elementary A L₀ U₀ hmove hc
  let : IsElementaryAbelian 2 (A ⧸ C₀.subgroupOf A) :=
    IsElementaryAbelian.of_surjective (QuotientGroup.quotientMulEquivOfEq hN).symm.toMonoidHom
      (QuotientGroup.quotientMulEquivOfEq hN).symm.surjective
  have hrot : ⁅⁅A,L₀⁆,A⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hmove.trans hc)
  have hAA : ⁅A,A⁆ ≤ centralizer (L₀ : Set (FreeAmalgam d.radical)) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (commutator_commutator_eq_bot_of_rotate hrot (by rwa [commutator_comm L₀ A]))
  obtain ⟨σ,c,_⟩ := BinaryConjugationSection.exists_descended_actor S A C₀ hAS inf_le_left
    (Q_normalized d.radical a) hSN κ hκ (by
      intro x hx y hy
      have hxA : (x : FreeAmalgam d.radical) ∈ A :=
        by
          change (x : FreeAmalgam d.radical) ∈ Q d.radical a
          rw [←hκQ]
          exact mem_map_of_mem S.subtype hx
      have hm := commutator_mem_commutator hxA hy
      exact ⟨(Subgroup.commutator_le_sup A A |>.trans (sup_idem A).le) hm,hAA hm⟩)
  let : Group.IsPerfect (K.subgroupOf d.overgroup) := (replacement_component h d).perfect
  let : Group.IsPerfect L₀ := by
    obtain ⟨v,rfl⟩ := exists_mVertex_of_color d.radical ha
    have hv : mVertex d.radical v = act d.radical v (alpha d.radical) := by
      simp [alpha,act_mVertex]
    have he : L₀ = ((K.subgroupOf d.overgroup).map (embedM d.radical)).map
        (MulAut.conj v⁻¹).toMonoidHom := by
      dsimp only [L₀]
      rw [hv,Ltilde_act,Ltilde_alpha,replacement_residual h d]
    let : Group.IsPerfect ((K.subgroupOf d.overgroup).map (embedM d.radical)) := Group.IsPerfect.map _
    exact he.symm ▸ Group.IsPerfect.map _
  have hfixed := BinaryConjugationSection.fixed_section_eq_bot S A L₀ hLS
    (hAS.trans hSL) κ σ c
  let : Finite S := finite_stabilizer _ _
  let : Finite A := Finite.of_injective (inclusion hAS) (inclusion_injective _)
  exact ⟨{
    Carrier := Additive (A ⧸ C₀.subgroupOf A)
    quotient := κ
    quotient_surjective := hκ
    quotient_kernel := hκQ
    action := σ
    sectionData := c
    fixed_eq_bot := hfixed },rfl⟩

omit h [Finite H] in
private theorem wholeKernelDualCover_of_marked_cover
    {E J V : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    [Group J] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]
    (a : Vertex d.radical) (s₀ : MovedSection ρ B)
    (e : ActionEquiv (s₀.action.comp B.subtype) (binaryNatural (K := E)))
    (he : IsCover (MovedSection.coverProjection s₀ e))
    (j : Multiplicative s₀.space.toSubmodule →* FreeAmalgam d.radical)
    (hjr : j.range = U d.radical a)
    (s : WholeKernelQuotient d.radical a J)
    (hκL : ((Ltilde d.radical a).subgroupOf
      (stabilizer d.radical a)).map s.quotient = B)
    (hconj : ∀ (g : stabilizer d.radical a) (v : s₀.space.toSubmodule),
      j (Multiplicative.ofAdd (s₀.space.toRepresentation (s.quotient g) v)) =
        (g : FreeAmalgam d.radical)*j (Multiplicative.ofAdd v)*(g : FreeAmalgam d.radical)⁻¹)
    (hker : ∀ v : s₀.space.toSubmodule, MovedSection.coverProjection s₀ e v = 0 ↔
      j (Multiplicative.ofAdd v) ∈
        centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)))
    (hZQ : Z d.radical a ≤ Q d.radical a)
    (hcomm : ⁅Q d.radical a,Ltilde d.radical a⁆ ≤
      U d.radical a) :
    let γ : L (K := E) →* J := B.subtype.comp e.groupEquiv.symm.toMonoidHom
    ∃ i : (binaryNatural (K := E)).IntertwiningMap (s.action.comp γ),
      Function.Injective i ∧ IsDualCover i.range ∧
      ∀ w, w ∈ i.toLinearMap.range ↔
        ∃ x : Q d.radical a, (x : FreeAmalgam d.radical) ∈
          U d.radical a ∧ (s.sectionData.coordinates x).toAdd = w := by
  let γ : L (K := E) →* J := B.subtype.comp e.groupEquiv.symm.toMonoidHom
  have hγ : γ.range = B := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.groupEquiv.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  let L₀ := Ltilde d.radical a
  let S := stabilizer d.radical a
  have hLS : L₀ ≤ S := Ltilde_le_stabilizer _
  let f₀ : L₀ →* B := (s.quotient.comp (inclusion hLS)).codRestrict B (by
    intro l
    exact hκL.le (mem_map_of_mem s.quotient (show inclusion hLS l ∈ L₀.subgroupOf S from l.property)))
  have hf₀ : Function.Surjective f₀ := by
    intro c
    obtain ⟨l,hl,he⟩ := (hκL.symm ▸ c.property : c.val ∈ (L₀.subgroupOf S).map s.quotient)
    exact ⟨⟨l.val,hl⟩,Subtype.ext he⟩
  let f := e.groupEquiv.toMonoidHom.comp f₀
  have hf : Function.Surjective f := e.groupEquiv.surjective.comp hf₀
  have hγf (l : L₀) : γ (f l) = s.quotient (inclusion hLS l) := by
    change (e.groupEquiv.symm (e.groupEquiv (f₀ l)) : J) = _
    rw [e.groupEquiv.symm_apply_apply]
    rfl
  let σ := s.action.comp γ
  let π := s.sectionData.coordinates
  have hUA : U d.radical a ≤ Q d.radical a :=
    (U_le_Z _).trans hZQ
  have hLA : L₀ ≤ normalizer (Q d.radical a : Set (FreeAmalgam d.radical)) :=
    hLS.trans (Q_normalized _ _)
  have hact (l : L₀) (a : Q d.radical a) :
      (π ⟨(l : FreeAmalgam d.radical)*a*(l : FreeAmalgam d.radical)⁻¹,
        (mem_normalizer_iff.mp (hLA l.property) a).mp a.property⟩).toAdd =
          σ (f l) (π a).toAdd := by
    change _ = s.action (γ (f l)) (π a).toAdd
    rw [hγf]
    exact s.sectionData.equivariant (inclusion hLS l) a
  have hjact (l : L₀) (v : s₀.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s₀ e (f l) v)) =
        (l : FreeAmalgam d.radical)*j (Multiplicative.ofAdd v)*(l : FreeAmalgam d.radical)⁻¹ := by
    change j (Multiplicative.ofAdd (s₀.space.toRepresentation (γ (f l)) v)) = _
    rw [hγf]
    exact hconj (inclusion hLS l) v
  have hkernel (v : s₀.space.toSubmodule) : MovedSection.coverProjection s₀ e v = 0 ↔
      π ⟨j (Multiplicative.ofAdd v),hUA (hjr ▸ ⟨Multiplicative.ofAdd v,rfl⟩)⟩ = 1 := by
    have hvU : j (Multiplicative.ofAdd v) ∈ U d.radical a :=
      hjr ▸ ⟨Multiplicative.ofAdd v,rfl⟩
    have hvQ : j (Multiplicative.ofAdd v) ∈ Q d.radical a :=
      hUA hvU
    apply (hker v).trans
    exact (show (j (Multiplicative.ofAdd v) ∈ centralizer (L₀ : Set (FreeAmalgam d.radical))) ↔
      j (Multiplicative.ofAdd v) ∈ Q d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
      from ⟨fun hv => ⟨hUA hvU,hv⟩,fun hv => hv.2⟩).trans
      (s.sectionData.coordinates_eq_one_iff ⟨j (Multiplicative.ofAdd v),hUA hvU⟩).symm
  have hmap : ((Ltilde d.radical a).subgroupOf S).map s.quotient = B := by
    exact hκL
  have hfixed : OneCohomology.fixed σ = ⊥ := by
    apply bot_unique
    intro v hv
    apply s.fixed_eq_bot.le
    intro c
    have hc : c.val ∈ B := hmap.le c.property
    obtain ⟨g,hg⟩ := (hγ.symm ▸ hc : c.val ∈ γ.range)
    change s.action c.val v = v
    rw [←hg]
    exact hv g
  obtain ⟨i,hi,hdual,_,hrange⟩ := exists_dualCover_of_conjugation_section
    (Q d.radical a) (U d.radical a) L₀ hUA hLA
    hcomm
    (MovedSection.coverAction s₀ e) σ (binaryNatural (K := E))
    (MovedSection.coverProjection s₀ e) he.1 j hjr π s.sectionData.onto f hf hjact hact hkernel hfixed
  exact ⟨i,hi,hdual,hrange⟩



omit h d in
private theorem section_fixedCodim_le_centralizer_index
    {G J W : Type*} [Group G] [Group J] [AddCommGroup W] [Module (ZMod 2) W]
    (S A D B : Subgroup G) [Finite A]
    (κ : S →* J) (σ : Representation (ZMod 2) J W)
    (c : BinaryConjugationSection S A D (σ.comp κ))
    (hDS : S ≤ normalizer (D : Set G)) (hBS : B ≤ S) :
    2 ^ fixedCodim σ ((B.subgroupOf S).map κ) ≤
      (centralizer (B : Set G)).relIndex A := by
  let : Finite W := Finite.of_surjective (fun a : A => (c.coordinates a).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let C := commutatorPreimage A B D
  let E : Subgroup (Multiplicative W) :=
    AddSubgroup.toSubgroup' (fixedSpace (σ.comp κ) (B.subgroupOf S)).toAddSubgroup
  have hm : (C.subgroupOf A).map c.coordinates = E := by
    ext v
    change v.toAdd ∈ c.imageSpace C ↔
      v.toAdd ∈ fixedSpace (σ.comp κ) (B.subgroupOf S)
    rw [c.fixed_image_eq B hBS (c.section_le.trans hDS)]
  have hDC : D ≤ C := le_commutatorPreimage c.kernel_le
    (by
      rw [commutator_comm]
      exact le_normalizer_iff_commutator_le_right.mp (hBS.trans hDS))
  have hker : c.coordinates.ker ≤ C.subgroupOf A := by
    rw [c.kernel_eq]
    exact comap_mono hDC
  have hi : E.index = C.relIndex A := by
    rw [←hm,index_map_eq _ c.onto hker]
    rfl
  have hc := E.card_mul_index
  have hE : Nat.card E = 2 ^ Module.finrank (ZMod 2)
      (fixedSpace (σ.comp κ) (B.subgroupOf S)) := by
    exact (Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := fixedSpace (σ.comp κ) (B.subgroupOf S))).trans (by rw [Nat.card_zmod])
  have hW : Nat.card (Multiplicative W) = 2 ^ Module.finrank (ZMod 2) W := by
    exact (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)).trans
      (by rw [Nat.card_zmod])
  rw [hE,hW,←fixedCodim_add_finrank (σ.comp κ) (B.subgroupOf S),add_comm,pow_add] at hc
  have he : C.relIndex A = 2 ^ fixedCodim σ ((B.subgroupOf S).map κ) := by
    rw [←hi]
    have hh := Nat.eq_of_mul_eq_mul_left (by positivity) hc
    have hfix : fixedSpace (σ.comp κ) (B.subgroupOf S) =
        fixedSpace σ ((B.subgroupOf S).map κ) := by
      ext v
      constructor
      · intro hv a
        obtain ⟨x,hx,he⟩ := a.property
        change σ a.val v = v
        rw [←he]
        exact hv ⟨x,hx⟩
      · intro hv a
        exact hv ⟨κ a.val,mem_map_of_mem κ a.property⟩
    change E.index = 2 ^ Module.finrank (ZMod 2) (W ⧸ fixedSpace σ ((B.subgroupOf S).map κ))
    rw [←hfix]
    exact hh
  rw [←he,←inf_relIndex_right (centralizer (B : Set G)) A]
  apply relIndex_le_of_le_left
  · apply le_commutatorPreimage inf_le_right
    rw [commutator_eq_bot_iff_le_centralizer.mpr inf_le_left]
    exact bot_le
  · exact index_ne_zero_of_finite


/-- In the field-sized replacement branch, the entire two-core is its
moving subgroup times its full component centralizer. -/
theorem replacement_field_sized_Q_decomposition
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    Q d.radical a = U d.radical a ⊔
      (Q d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))) := by
  let := replacementComponent_normal h d
  let s₀ := replacementMovedSection h d
  obtain ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.start_color
  have hFc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  obtain ⟨s,hs⟩ := replacement_wholeKernelQuotient_over h d g hb path.start_color κ hκ hκQ
  let B := (K.subgroupOf d.overgroup).map (QuotientGroup.mk' (pCore 2 d.overgroup))
  let γ := B.subtype.comp e.groupEquiv.symm.toMonoidHom
  have hZQ : Z d.radical a ≤ Q d.radical a :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
      (omegaCenter_le _)
  obtain ⟨i,hi,hdual,hrange⟩ := wholeKernelDualCover_of_marked_cover d a s₀ e he j hjr s
    (by rw [hs]; exact hκL) (by intro x v; rw [hs]; exact hconj x v) hker hZQ
    (replacement_core_eq_U_of_distance_two h d g hb path.start_color).le
  let σ := s.action.comp γ
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  have haq := (replacement_field_sized_edge_factorization h d rev hb hzt hat hsize).1
  have hzq := (replacement_field_sized_edge_factorization h d path hb hat hzt hsize).1
  have hZA : Z d.radical z ≤ stabilizer d.radical a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  let δ := κ.comp (inclusion hZA)
  have hδcard : Nat.card δ.range = Nat.card E.Carrier :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hZA κ hκQ).trans (hzq.trans hFc.symm)
  have hδ : ∀ x : Z d.radical z, ∀ v : s₀.space.toSubmodule,
      j (Multiplicative.ofAdd (s₀.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam d.radical)*j (Multiplicative.ofAdd v)*(x : FreeAmalgam d.radical)⁻¹ :=
    fun x v => hconj (inclusion hZA x) v
  obtain ⟨β,hβcard,hβmark,hβ,hβdim,hβquad⟩ := inner_root_actor_of_field_index rev (by omega)
    (MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) z path.end_color)
    h.nonbinary hFc s₀ e he (replacement_component_image_structure h d).2.2.2.2
    j hj hjr δ hδ hδcard (haq.trans hFc.symm)
  have hmap : ((Z d.radical z).subgroupOf (stabilizer d.radical a)).map κ = β.range.map γ := by
    have heq : γ.comp β = δ := by
      ext x
      exact hβmark x
    rw [←MonoidHom.range_comp,heq]
    apply le_antisymm
    · rintro y ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx⟩,rfl⟩
    · rintro y ⟨x,rfl⟩
      exact ⟨inclusion hZA x,x.property,rfl⟩
  have hSN : stabilizer d.radical a ≤ normalizer
      ((Q d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :
        Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
    have hSL : stabilizer d.radical a ≤ normalizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) := by
      have ht := le_normalizer_map (H := pResidual 2 (stabilizer d.radical a))
        (stabilizer d.radical a).subtype
      rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at ht
      exact ht
    exact (le_inf (Q_normalized d.radical a)
      (hSL.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  let := finite_stabilizer d.radical a
  let : Finite (Q d.radical a) := Finite.of_injective
    (inclusion (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1))
    (inclusion_injective _)
  have hbound : fixedCodim σ β.range ≤ Module.finrank (ZMod 2) E.Carrier := by
    have hi := section_fixedCodim_le_centralizer_index (stabilizer d.radical a)
      (Q d.radical a) _ (Z d.radical z) s.quotient s.action s.sectionData hSN hZA
    rw [hs,hmap,replacement_field_sized_whole_kernel_index h d path hb hat hzt hsize] at hi
    have hie : fixedCodim s.action (β.range.map γ) = fixedCodim σ β.range := by
      have he : fixedSpace σ β.range = fixedSpace s.action (β.range.map γ) := by
        ext v
        constructor
        · intro hv a
          obtain ⟨x,hx,he⟩ := a.property
          change s.action a.val v = v
          rw [←he]
          exact hv ⟨x,hx⟩
        · intro hv a
          exact hv ⟨γ a.val,mem_map_of_mem γ a.property⟩
      exact congrArg (fun A : Submodule (ZMod 2) s.Carrier =>
        Module.finrank (ZMod 2) (s.Carrier ⧸ A)) he.symm
    rw [hie] at hi
    have hdegree : Module.finrank (ZMod 2) E.Carrier = n := by
      have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E.Carrier)
      rw [Nat.card_zmod,hFc] at hc
      exact (Nat.pow_right_injective (by decide : 1 < 2) hc).symm
    rw [hdegree]
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hi
  have hcard : 2 < Nat.card E.Carrier := by
    rw [hFc]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  obtain ⟨f,hf⟩ := derived_four_conjugates_of_displacement_one hcard β.range hβcard hβdim hβquad
  have hdim := fixedCodim_le_card_mul_of_subgroup_conjugates σ ⊤ β.range f hf.ge
  have hfixed : fixedSpace σ ⊤ = ⊥ := by
    apply bot_unique
    intro v hv
    exact hdual.2.le (fun x => hv ⟨x,mem_top _⟩)
  have htotal := fixedCodim_add_finrank σ ⊤
  rw [hfixed,finrank_bot,add_zero] at htotal
  rw [htotal,Fintype.card_fin] at hdim
  have htotalBound : Module.finrank (ZMod 2) s.Carrier ≤ 4 * Module.finrank (ZMod 2) E.Carrier :=
    hdim.trans (Nat.mul_le_mul_left 4 hbound)
  have hdimI : Module.finrank (ZMod 2) i.toLinearMap.range =
      4 * Module.finrank (ZMod 2) E.Carrier := by
    rw [LinearMap.finrank_range_of_inj hi]
    simp [Natural,Module.finrank_pi_fintype]
  have hfull : i.toLinearMap.range = ⊤ := Submodule.eq_top_of_finrank_eq
    (le_antisymm i.toLinearMap.range.finrank_le (htotalBound.trans_eq hdimI.symm))
  have hUQ : U d.radical a ≤ Q d.radical a := (U_le_Z a).trans hZQ
  apply le_antisymm
  · intro x hx
    obtain ⟨u,hu,heq⟩ := (hrange (s.sectionData.coordinates ⟨x,hx⟩).toAdd).mp
      (hfull.symm ▸ Submodule.mem_top)
    have hc : (u⁻¹ * ⟨x,hx⟩ : Q d.radical a) ∈ s.sectionData.coordinates.ker := by
      change s.sectionData.coordinates (u⁻¹ * ⟨x,hx⟩) = 1
      rw [map_mul,map_inv,Multiplicative.toAdd.injective heq,inv_mul_cancel]
    rw [s.sectionData.kernel_eq] at hc
    have he : x = u.val * (u.val⁻¹*x) := by simp
    rw [he]
    exact mul_mem (mem_sup_left hu) (mem_sup_right hc)
  · exact sup_le hUQ inf_le_left

/-- Application to the original odd-index comparison, without a new radicality premise. -/
theorem replacement_proper_nonsylow_Q_decomposition
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hnsyl : ¬ ∃ S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F),
      (S : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) =
        (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    Q d.radical a = U d.radical a ⊔
      (Q d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))) :=
  replacement_field_sized_Q_decomposition h d path hb hat hzt
    (replacement_proper_nonsylow_card h d g hb hnsyl hne)


/-- The full-kernel decomposition in the literal replacement overgroup,
with the original restricted component and its full centralizer. -/
theorem replacement_field_sized_core_decomposition
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    pCore 2 d.overgroup = ⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆ ⊔
      (pCore 2 d.overgroup ⊓ centralizer (K.subgroupOf d.overgroup : Set d.overgroup)) := by
  obtain ⟨z,⟨path⟩⟩ := CriticalPath.exists_from (R := d.radical) (geometry := g)
    (a := alpha d.radical) rfl
  have hd : (cosetGraph d.radical).dist (alpha d.radical) z = 2 :=
    path.critical.1.trans ((g.distance_constant _ path.start_color).trans hb)
  obtain ⟨t,hat,hzt⟩ := exists_common_neighbor_of_dist_two d.radical (alpha d.radical) z hd
  have he := replacement_field_sized_Q_decomposition h d path hb hat hzt hsize
  rw [←replacement_core_eq_U_of_distance_two h d g hb rfl,
    core_alpha d.radical (replacement_isPGroup h d) (replacement_core_le h d)
      (replacement_residual h d),Q_alpha d.radical (replacement_isPGroup h d)
      (replacement_core_le h d),Ltilde_alpha,replacement_residual h d] at he
  let f := embedM d.radical
  have hfix : (pCore 2 d.overgroup).map f ⊓
      centralizer ((K.subgroupOf d.overgroup).map f : Set (FreeAmalgam d.radical)) =
        (pCore 2 d.overgroup ⊓ centralizer (K.subgroupOf d.overgroup : Set d.overgroup)).map f := by
    apply le_antisymm
    · rintro y ⟨⟨x,hx,rfl⟩,hc⟩
      refine ⟨x,⟨hx,?_⟩,rfl⟩
      intro k hk
      apply embedM_injective d.radical
      simpa only [map_mul] using hc (f k) (mem_map_of_mem f hk)
    · rintro y ⟨x,⟨hx,hc⟩,rfl⟩
      refine ⟨mem_map_of_mem f hx,?_⟩
      rintro y ⟨k,hk,rfl⟩
      simpa only [map_mul] using congrArg f (hc k hk)
  change (pCore 2 d.overgroup).map f =
    (⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆).map f ⊔ _ at he
  rw [hfix,←Subgroup.map_sup] at he
  exact map_injective (embedM_injective d.radical) he

/-- Original-witness application of the literal two-core factorization. -/
theorem replacement_proper_nonsylow_core_decomposition
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F),
      (S : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) =
        (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    pCore 2 d.overgroup = ⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆ ⊔
      (pCore 2 d.overgroup ⊓ centralizer (K.subgroupOf d.overgroup : Set d.overgroup)) :=
  replacement_field_sized_core_decomposition h d g hb
    (replacement_proper_nonsylow_card h d g hb hnsyl hne)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
