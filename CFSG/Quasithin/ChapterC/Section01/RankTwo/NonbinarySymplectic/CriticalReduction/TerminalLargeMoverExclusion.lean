module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TerminalKernelSaturation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SmallMoverKernels
public import Theory.Representation.SymplecticFourOrthogonalCover.RootNormalizerFixed

/-!
# Excluding the full large-mover terminal branch

Suppose the smaller-mover join at an edge has full-layer fixed index
larger than q squared. The maximum-family dichotomy makes this join the
whole edge kernel. At a field-sized critical pair, the quotient action
of that kernel centralizes the critical actor. Its natural displacement
is a line. A two-group normalizing this line fixes it pointwise, and
fixed-vector lifting through the full central cover fixes its entire
preimage. Hence the full critical commutator lies in the first edge seed.

Apply this on the actual saturated terminal sequence. The first-edge
intersection is precisely the retained moving central kernel, while the
critical commutator has central index q. This is a contradiction. Edge
transitivity then bounds the smaller-mover fixed index at every literal
edge. Applying the existing maximizing-parabolic theorem now puts the
entire smaller-mover join in the chosen parabolic core, without an extra
branch premise, whenever the replacement critical distance exceeds four.

This closes the large-mover branch of the MS93 (5.10) comparison by using
the proved full-cover root-normalizer theorem. The unequal-contained
neighbor comparison and terminal (5.11)--(5.12) exclusions remain needed
for the actual minimum-replacement distance-two witness. Every original
nonbinary degree, quotient kernel, and central attachment is retained;
no original-radical characteristic-control assertion is made.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3), (5.4), (5.10), printed pp.866--867,915,922--923.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open ChapterB.QuasisimpleSource MSCentralOrbit
open CentralRootGeometry.SmallMovers
private theorem embedded_normalizing_image_centralizes_displacement
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (π : σ.IntertwiningMap (binaryNatural (K := F))) (he : IsCover π)
    (U T A : Subgroup G) (hAT : A ≤ T) (hT : IsPGroup 2 T)
    (j : Multiplicative W →* G) (hjr : j.range=U) (β : T →* L (K := F))
    (hact : ∀ (y : T) (w : W), j (Multiplicative.ofAdd (σ (β y) w))=
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹)
    (hn : β.range ≤ normalizer ((β.comp (inclusion hAT)).range : Set (L (K := F))))
    (hd : Module.finrank F (displacementSpace
      ((β.comp (inclusion hAT)).range.map (commutator (Sp F)).subtype)) ≤ 1) :
    ⁅U,A⁆ ≤ centralizer (T : Set G) := by
  let βA := β.comp (inclusion hAT)
  rw [commutator_comm]
  apply commutator_le.mpr
  intro y hy u hu
  obtain ⟨v,rfl⟩ := (hjr.symm ▸ hu : u ∈ j.range)
  let w := σ (βA ⟨y,hy⟩) v.toAdd-v.toAdd
  have hw : π w ∈ displacementSpace (βA.range.map (commutator (Sp F)).subtype) := by
    rw [show π w=binaryNatural (βA ⟨y,hy⟩) (π v.toAdd)-π v.toAdd by
      rw [show w=σ (βA ⟨y,hy⟩) v.toAdd-v.toAdd from rfl,map_sub,π.isIntertwining]]
    exact Coinvariants.sub_mem_ker
      (ρ := (symplecticNatural 2).comp (βA.range.map (commutator (Sp F)).subtype).subtype)
      ⟨(βA ⟨y,hy⟩).val,mem_map_of_mem _ ⟨_,rfl⟩⟩ _
  have hwval : j (Multiplicative.ofAdd w)=⁅y,j v⁆ := by
    dsimp only [w,βA,MonoidHom.comp_apply]
    rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
    rfl
  intro x hx
  have hfix := cover_two_normalizer_fixes_displacement π he βA.range β.range
    (hT.of_surjective β.rangeRestrict β.rangeRestrict_surjective) hn hd ⟨β ⟨x,hx⟩,⟨_,rfl⟩⟩ w hw
  have hh := congrArg (fun w => j (Multiplicative.ofAdd w)) hfix
  rw [hact,hwval,mul_inv_eq_iff_eq_mul] at hh
  exact hh


variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem small_mover_field_commutator_le_Q
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t)
    (A : Subgroup (FreeAmalgam d.radical)) (hAT : A ≤ Q d.radical t)
    (hsmall : (centralizer (A : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) ≤ Nat.card F) :
    ⁅Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2), A⁆ ≤ Q d.radical a := by
  obtain ⟨E,hE,f,hf,hfQ,hTf,hidx⟩ := h.replacement_small_mover_coordinates d geometry hb ha hat
  have hcard : Nat.card E.Carrier = Nat.card F := by rw [E.card_eq,hE,h.field_card]
  let S := stabilizer d.radical a
  let U₀ := (U d.radical a).subgroupOf S
  let T := (Q d.radical t).subgroupOf S
  let A₀ := A.subgroupOf S
  let := finite_stabilizer d.radical a
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hTS : Q d.radical t ≤ S := by
    change Q d.radical t ≤ stabilizer d.radical a
    rw [←hjr,←hjR]
    exact map_le_range j _
  have hQT : Q d.radical a ≤ Q d.radical t := by
    rw [←hjQ,←hjR]
    exact map_mono (h.replacement_core_le d)
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hQeq : f.ker = (Q d.radical a).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le (show Q d.radical a ≤ S from fun _ hx => hx.1)]
  have hkT : f.ker ≤ T := by rw [hQeq]; exact comap_mono hQT
  have hUK : U₀ ≤ centralizer (f.ker : Set S) := by
    intro u hu k hk
    apply Subtype.val_injective
    have hkQ : k.val ∈ Q d.radical a := hfQ ▸ mem_map_of_mem S.subtype hk
    exact ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a ha))
      (U_le_Z a hu) k.val hkQ)
  have hiA : (centralizer (A₀ : Set S)).relIndex U₀ ≤ Nat.card E.Carrier := by
    rw [←Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective U₀ A₀,
      map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le (hAT.trans hTS),hcard]
    exact hsmall
  have hc := Degree.Quotient.join_image_centralizes_field_actor U₀ T f unipotent.subtype
    Subtype.val_injective hkT hUK (by simpa only [range_subtype] using hTf)
    hidx A₀ (comap_mono hAT) hiA
  have hcomm : ⁅Subgroup.SmallMover.join U₀ f.ker T (Nat.card E.Carrier^2), A₀⁆ ≤ f.ker := by
    apply (Subgroup.map_eq_bot_iff _).mp
    rw [map_commutator]
    exact commutator_eq_bot_iff_le_centralizer.mpr hc
  have hm := map_mono (f := S.subtype) hcomm
  rw [map_commutator,Subgroup.SmallMover.join_map S.subtype S.subtype_injective,
    map_subgroupOf_eq_of_le hUS,hfQ,map_subgroupOf_eq_of_le hTS,
    map_subgroupOf_eq_of_le (hAT.trans hTS),hcard] at hm
  exact hm

private theorem large_mover_eq_edge
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t)
    (hlarge : Nat.card F^2 < (centralizer (Subgroup.SmallMover.join
      (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F^2) :
        Set (FreeAmalgam d.radical))).relIndex (U d.radical a)) :
    Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) = Q d.radical t := by
  rcases h.replacement_small_mover_dichotomy d geometry hb ha hat with
    ⟨J,hmax,hjoin⟩ | ⟨_,heq,_⟩
  · have hJ := (show J ∈ Subgroup.SmallMover.Maximal (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2) from hmax.symm ▸ Set.mem_singleton J).1.2.2
    rw [hjoin] at hlarge
    exact False.elim (hlarge.not_ge hJ)
  · exact heq

/-- In the large-mover branch a field-sized critical commutator lies in
its first edge seed, retaining the entire covering kernel. -/
theorem Input.replacement_large_mover_critical_commutator_le_edge
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (hi : (Q d.radical a).relIndex (Z d.radical z)=Nat.card F)
    (hi' : (Q d.radical z).relIndex (Z d.radical a)=Nat.card F)
    (hlarge : Nat.card F^2 < (centralizer (Subgroup.SmallMover.join
      (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F^2) :
        Set (FreeAmalgam d.radical))).relIndex (U d.radical a)) :
    ⁅Z d.radical a,Z d.radical z⁆ ≤ Z d.radical t := by
  let T := Q d.radical t
  let A := Z d.radical z
  have hTS : T ≤ stabilizer d.radical a := fun _ hx => hx.2 a (adjacent_symm _ hat)
  have hAT : A ≤ T := by
    apply Z_le_Q_of_dist_lt _ z (geometry.exists_critical z path.end_color)
    rw [geometry.distance_constant z path.end_color,SimpleGraph.dist_comm,←hfirst,
      path.dist_end,path.length_eq_b]
    change geometry.b d.radical-1 < geometry.b d.radical
    omega
  have hCa := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) z path.end_color
  have hAS : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  have hidx : (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (Z d.radical a)=Nat.card F := by
    rw [←inf_relIndex_left,show Z d.radical a ⊓ centralizer (A : Set (FreeAmalgam d.radical))=
      Z d.radical a ⊓ Q d.radical z from by
        rw [←hCa]; ext x; exact ⟨fun hx => ⟨hx.1,hAS hx.1,hx.2⟩,fun hx => ⟨hx.1,hx.2.2⟩⟩,
      inf_relIndex_left,hi']
  let := finite_Z d.radical a
  have hsmall : (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) ≤ Nat.card F :=
    (relIndex_le_of_le_right (U_le_Z a) index_ne_zero_of_finite).trans_eq hidx
  have hcomm := small_mover_field_commutator_le_Q h d geometry hb path.start_color hat A hAT hsmall
  rw [large_mover_eq_edge h d geometry hb path.start_color hat hlarge] at hcomm
  obtain ⟨ι,hι,hιr,hιR,hιQ,hιU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) path.start_color hat
  have hUT : U d.radical a ≤ T := by
    apply (U_le_Z a).trans
    apply ((Z_le_VBall d.radical a 2).trans (geometry.V_le_Q (by omega) a path.start_color)).trans
    rw [←hιQ,show T=Q d.radical t from rfl,←hιR]
    exact map_mono (h.replacement_core_le d)
  have hT : IsPGroup 2 T := by
    change IsPGroup 2 (Q d.radical t)
    rw [←hιR]
    exact (h.replacement_two_group d).map ι
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup)) := omegaCenterIn_elementary _
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d path.start_color
  have hFc : Nat.card E.Carrier=Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have hFl : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 2 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hCtop : C=⊤ := by
    have hh : C.comap q=⊤ := by
      rw [show C=(K.subgroupOf d.overgroup).map q from rfl,comap_map_eq,QuotientGroup.ker_mk']
      exact h.replacement_inner_of_four_le d geometry hb
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C,hh,
      ←MonoidHom.range_eq_map,MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let κC := κ.codRestrict C (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  let β := γ.comp (inclusion hTS)
  let βA := β.comp (inclusion hAT)
  let σ := MovedSection.coverAction s e
  let π := MovedSection.coverProjection s e
  have hact (y : T) (w : s.space.toSubmodule) : j (Multiplicative.ofAdd (σ (β y) w))=
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC (inclusion hTS y)))) w))=_
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj (inclusion hTS y) w
  have hγker : γ.ker=(Q d.radical a).subgroupOf (stabilizer d.radical a) := by
    ext x
    change e.groupEquiv (κC x)=1 ↔ x.val ∈ Q d.radical a
    rw [e.groupEquiv.map_eq_one_iff]
    rw [show κC x=1 ↔ κ x=1 from Subtype.ext_iff]
    constructor
    · intro hx
      exact hκQ ▸ mem_map_of_mem (stabilizer d.radical a).subtype hx
    · intro hx
      obtain ⟨y,hy,hyx⟩ := hκQ.symm ▸ hx
      exact (show y=x from Subtype.ext hyx) ▸ hy
  have hcard : Nat.card βA.range=Nat.card E.Carrier := by
    have hk : βA.ker=(Q d.radical a).subgroupOf A := by
      ext x
      change γ (inclusion hTS (inclusion hAT x))=1 ↔ _
      exact show inclusion hTS (inclusion hAT x) ∈ γ.ker ↔ _ from by rw [hγker]; rfl
    rw [←index_ker,hk]
    exact hi.trans hFc.symm
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  let rev := (show CriticalSegment geometry from ⟨a,z,path⟩).reverse hedge (by omega)
  have hd := (critical_root_coordinates_of_reciprocal_index_field rev.path (by omega) hCa hFl
    σ π he j hj hjr βA (fun x w => hact (inclusion hAT x) w) hcard (hi'.trans hFc.symm)).1
  have hn : β.range ≤ normalizer (βA.range : Set (L (K := E.Carrier))) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    rintro x ⟨x,rfl⟩ y ⟨y,rfl⟩
    have hxy : ⁅γ (inclusion hTS x),γ (inclusion hTS (inclusion hAT y))⁆=1 := by
      rw [←map_commutatorElement]
      apply show ⁅inclusion hTS x,inclusion hTS (inclusion hAT y)⁆ ∈ γ.ker from ?_
      rw [hγker]
      exact hcomm (commutator_mem_commutator x.property y.property)
    exact (commutatorElement_eq_one_iff_mul_comm.mp hxy).symm
  have hDfix : ⁅U d.radical a,A⁆ ≤ centralizer (T : Set (FreeAmalgam d.radical)) :=
    embedded_normalizing_image_centralizes_displacement π he (U d.radical a) T A
      hAT hT j hjr β hact hn hd.le
  have hD : ⁅Z d.radical a,Z d.radical z⁆=⁅U d.radical a,A⁆ :=
    h.replacement_Z_commutator_eq_U d geometry hb path.start_color A (hAT.trans hTS)
  have hDU : ⁅Z d.radical a,Z d.radical z⁆ ≤ U d.radical a := by
    rw [hD]
    exact le_normalizer_iff_commutator_le_left.mp ((hAT.trans hTS).trans (U_normalized a))
  have ht : color d.radical t ≠ false := fun ht => (adjacent_color_ne _ hat) (path.start_color.trans ht.symm)
  let : IsElementaryAbelian 2 (Z d.radical a) := geometry.Z_elementary (by omega) a path.start_color
  intro x hx
  rw [Z,if_neg ht]
  exact mem_omegaCenter_iff.mpr ⟨hUT (hDU hx),
    elemPow_eq_one_of_isElementaryAbelian _ (U_le_Z a (hDU hx)),hDfix (hD ▸ hx)⟩

omit h in
private theorem mover_index_act {M : Type*} [Group M] [Finite M] {R : Subgroup M}
    (q : ℕ) (g : FreeAmalgam R) (a t : Vertex R) :
    (centralizer (Subgroup.SmallMover.join (U R (act R g a)) (Q R (act R g a))
      (Q R (act R g t)) (q^2) : Set (FreeAmalgam R))).relIndex (U R (act R g a)) =
    (centralizer (Subgroup.SmallMover.join (U R a) (Q R a)
      (Q R t) (q^2) : Set (FreeAmalgam R))).relIndex (U R a) := by
  rw [U_act,Q_act,Q_act,←Subgroup.SmallMover.join_map _ (MulAut.conj g⁻¹).injective,
    coe_map,MulEquiv.coe_toMonoidHom,←Theory.GroupTheory.map_centralizer_equiv]
  exact relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective

omit h in
private theorem mover_index_eq_of_edges {M : Type*} [Group M] [Finite M] {R : Subgroup M}
    (q : ℕ) {a t c w : Vertex R} (ha : color R a=false) (hc : color R c=false)
    (hat : Adjacent R a t) (hcw : Adjacent R c w) :
    (centralizer (Subgroup.SmallMover.join (U R c) (Q R c)
      (Q R w) (q^2) : Set (FreeAmalgam R))).relIndex (U R c) =
    (centralizer (Subgroup.SmallMover.join (U R a) (Q R a)
      (Q R t) (q^2) : Set (FreeAmalgam R))).relIndex (U R a) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color R hc
  obtain ⟨j,hj⟩ := exists_mVertex_of_color R ha
  let y := g⁻¹*j
  have hy : act R y c=a := by
    rw [hg,act_mVertex]
    dsimp [y]
    rw [mul_inv_cancel_left,←hj]
  have had : Adjacent R a (act R y w) := by
    rw [←hy]
    exact (adjacent_act_iff R y _ _).mpr hcw
  obtain ⟨x,hx,hxt⟩ := stabilizer_transitive_neighbors R a had hat
  have hka : act R (y*x) c=a := by rw [act_mul,hy]; exact hx
  have hkt : act R (y*x) w=t := by rw [act_mul,hxt]
  have hh := mover_index_act q (y*x) c w
  rw [hka,hkt] at hh
  exact hh.symm

/-- The full large-mover branch is impossible at critical distance greater
than four. The saturated terminal commutator would lie in its edge seed
and hence in the full vertex center, contrary to its exact critical index. -/
theorem Input.replacement_large_mover_excluded
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical) :
    (centralizer (Subgroup.SmallMover.join (U d.radical p.first)
      (Q d.radical p.first) (Q d.radical (p.path.walk.getVert 1)) (Nat.card F^2) :
        Set (FreeAmalgam d.radical))).relIndex (U d.radical p.first) ≤ Nat.card F^2 := by
  by_contra hnot
  have hJm := Nat.lt_of_not_ge hnot
  obtain ⟨s,hs0,hs,hover,hdata⟩ := h.replacement_large_mover_terminal_saturated_kernels d p hb hJm
  have first_adj (r : CriticalSegment geometry) :
      Adjacent d.radical r.first (r.path.walk.getVert 1) := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (r.path.walk.adj_getVert_succ (by rw [r.path.length_eq_b]; omega : 0 < r.path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hbig : Nat.card F^2 < (centralizer (Subgroup.SmallMover.join
      (U d.radical (s 2).first) (Q d.radical (s 2).first)
      (Q d.radical ((s 2).path.walk.getVert 1)) (Nat.card F^2) :
        Set (FreeAmalgam d.radical))).relIndex (U d.radical (s 2).first) := by
    rw [mover_index_eq_of_edges (Nat.card F) p.path.start_color (s 2).path.start_color
      (first_adj p) (first_adj (s 2))]
    exact hJm
  obtain ⟨hperiod,hedge,hprev,hcard,hprop,hi,hi',hnotB⟩ := hdata 0
  have hD := h.replacement_large_mover_critical_commutator_le_edge d (s 2).path hb.le
    (first_adj (s 2)) rfl hi' hi hbig
  have hc : ⁅Z d.radical (s 2).first,Z d.radical (s 2).last⁆ ≤
      stabilizer d.radical (s 2).first ⊓ centralizer
        (stabilizer d.radical (s 2).first : Set (FreeAmalgam d.radical)) := by
    have hh := (le_inf le_rfl hD).trans hedge.le
    rw [←hperiod] at hh
    exact le_inf ((critical_commutator_le_start_seed (s 2).path).trans
      (Z_le_stabilizer _ _)) (hh.trans inf_le_right)
  have hone := relIndex_eq_one.mpr hc
  rw [h.replacement_critical_commutator_central_index d (s 2).path hb.le,hi] at hone
  have hq : 1 < Nat.card F := Finite.one_lt_card
  omega

/-- The terminal exclusion bounds the full smaller-mover fixed index at
every literal edge, with no critical-path or selector premise. -/
theorem Input.replacement_small_mover_index_le_square_of_four_lt
    (geometry : Geometry d.radical) (hb : 4 < geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) :
    (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2 := by
  obtain ⟨z,hz⟩ := criticalPair_exists d.radical a (geometry.exists_critical a ha)
  let path := CriticalPath.ofPair (geometry := geometry) ha hz
  let p : CriticalSegment geometry := ⟨a,z,path⟩
  have hfirst : Adjacent d.radical a (path.walk.getVert 1) := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  rw [mover_index_eq_of_edges (Nat.card F) ha ha hfirst hat]
  exact h.replacement_large_mover_excluded d p hb

/-- The source maximizing parabolic now contains the entire smaller-mover
join at distance greater than four. This discharges the literal J ≤ Q₁
branch premise while preserving the original marking and full kernel. -/
theorem Input.replacement_maximizing_parabolic_contains_mover_of_four_lt
    (geometry : Geometry d.radical) (hb : 4 < geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ∃ E : BinaryField, E.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp E.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ fixedCodim (restrictScalars (k := ZMod 2)
              (symplecticNatural (k := E.Carrier) 2)) (A.map f)) ∧
        (let P := (CentralRootGeometry.wing (F := E.Carrier) true).map unipotent.subtype
         let Q₁ := P.comap f
         let J := (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
           (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a)
         J ≤ Q₁ ∧
         (planeParabolic.comap f).pCoreIn 2 = Q₁ ∧
         (Q d.radical t).subgroupOf (stabilizer d.radical a) ≤ planeParabolic.comap f ∧
         ⁅⁅(U d.radical a).subgroupOf (stabilizer d.radical a),Q₁⁆,Q₁⁆ = ⊥ ∧
           ∀ x : Sp E.Carrier,
             Nat.card (J ⊓ (P.map (MulAut.conj x).toMonoidHom).comap f :
               Subgroup (stabilizer d.radical a)) ≤ Nat.card (J ⊓ Q₁ :
                 Subgroup (stabilizer d.radical a))) := by
  obtain ⟨E,hE,f,hf,hfQ,hTf,hindex,hcore,hTP,hquad,hmax⟩ :=
    h.replacement_maximizing_parabolic d geometry hb.le ha hat
  have hJ := h.replacement_small_mover_le_maximizing_plane_of_index_le d geometry hb.le
    ha hat E hE f hfQ hTf hindex hmax
      (h.replacement_small_mover_index_le_square_of_four_lt d geometry hb ha hat)
  exact ⟨E,hE,f,hf,hfQ,hTf,hindex,hJ,hcore,hTP,hquad,hmax⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
