module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TerminalPaths

/-!
# Exact full-center quotients of the terminal critical commutators

Symplectic duality identifies the fixed index on the whole Z-layer with
the order of its commutator modulo the full vertex center. The natural
projection maps the entire commutator onto the field displacement space;
its kernel is the actual central intersection, with every attachment
retained. At a critical pair this order is the opposite critical image.

If the critical commutator meets the first edge seed only in the vertex
center, both critical images have order q. Otherwise its quadratic natural
image has a self-orthogonal displacement plane. An edge-fixed nonzero
vector lies in that plane, and fixed-point lifting gives an element of the
literal edge seed inside the commutator with nonzero natural image. This
contradicts the central-intersection hypothesis, without assuming the edge
is a full Sylow or choosing a complement to the cover kernel.

The actual large-mover terminal sequence discharges this intersection
hypothesis by the existing three-center propagation. It now retains both
critical indices and both full-center indices equal to the original field
order, together with the same individual movers, full fixed clauses and
all path overlaps. This proves the first order comparison of MS93 (5.10)
in that branch. The unequal-contained selectors, subsequent terminal
exclusions and actual minimum-replacement distance-two witness remain.
Original-radical characteristic control is a separate obligation.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3), printed pp.866--867, and (5.10), printed p.922.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit

private theorem embedded_commutator_central_index
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U A C : Subgroup G) (j : Multiplicative W →* G) (hj : Function.Injective j)
    (hjr : j.range=U) (β : A →* L (K := F))
    (hact : ∀ (a : A) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (hker : ∀ w : W, p w=0 ↔ j (Multiplicative.ofAdd w) ∈ C) :
    C.relIndex ⁅A,U⁆ = (centralizer (A : Set G)).relIndex U := by
  let α := (commutator (Sp F)).subtype.comp β
  let D := displacementSpace α.range
  let D₀ : Subgroup (Multiplicative (Vector F)) := AddSubgroup.toSubgroup' D.toAddSubgroup
  obtain ⟨π,hπ⟩ := exists_embedded_projection U j hj hjr p.toLinearMap
  have hAU : ⁅A,U⁆ ≤ U := by
    apply commutator_le.mpr
    intro a ha u hu
    obtain ⟨v,rfl⟩ := hjr.symm ▸ hu
    have he : ⁅a,j v⁆=j (Multiplicative.ofAdd (σ (β ⟨a,ha⟩) v.toAdd-v.toAdd)) := by
      rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
      rfl
    rw [he]
    exact hjr ▸ ⟨_,rfl⟩
  have hk : π.ker=C.subgroupOf U := by
    ext u
    obtain ⟨w,hw⟩ := (show u.val ∈ j.range from hjr.symm ▸ u.property)
    have he : u=⟨j w,by rw [←hjr]; exact ⟨w,rfl⟩⟩ := Subtype.ext hw.symm
    subst u
    change π ⟨j w,_⟩=1 ↔ j w ∈ C
    have hπw := hπ w.toAdd
    change π ⟨j w,_⟩ = Multiplicative.ofAdd (p w.toAdd) at hπw
    rw [hπw]
    exact hker w.toAdd
  have hpre : ⁅A,U⁆ ≤ (D₀.comap π).map U.subtype := by
    apply commutator_le.mpr
    intro a ha u hu
    obtain ⟨v,rfl⟩ := hjr.symm ▸ hu
    let w := σ (β ⟨a,ha⟩) v.toAdd-v.toAdd
    refine ⟨⟨j (Multiplicative.ofAdd w),hjr ▸ ⟨_,rfl⟩⟩,?_,?_⟩
    · change π ⟨j (Multiplicative.ofAdd w),_⟩ ∈ D₀
      rw [hπ]
      change p w ∈ D
      dsimp only [w]
      rw [map_sub,p.isIntertwining]
      exact Coinvariants.sub_mem_ker
        (ρ := (symplecticNatural 2).comp α.range.subtype)
        ⟨α ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩⟩ (p v.toAdd)
    · change j (Multiplicative.ofAdd w)=⁅a,j v⁆
      dsimp only [w]
      rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
      rfl
  have hm : (⁅A,U⁆.subgroupOf U).map π=D₀ := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨y,hy,hyx⟩ := hpre hx
      have he : y=x := Subtype.ext hyx
      exact he ▸ hy
    · intro v hv
      obtain ⟨w,hw,hwc⟩ := natural_displacement_lifts U A j hjr β σ hact p hp.1 v.toAdd hv
      refine ⟨⟨j (Multiplicative.ofAdd w),hAU hwc⟩,hwc,?_⟩
      rw [hπ]
      change Multiplicative.ofAdd (p w)=v
      rw [hw,ofAdd_toAdd]
  have hi := embedded_centralizer_index σ U A j hj hjr β hact
  rw [fixedCodim_of_binaryCover p hp] at hi
  have hfixed : fixedSpace (binaryNatural (K := F)) β.range =
      (TwoLocalCover.fixedSpace α.range).restrictScalars (ZMod 2) := by
    ext v
    constructor
    · intro hv x hx
      obtain ⟨a,rfl⟩ := hx
      exact hv ⟨β a,⟨a,rfl⟩⟩
    · intro hv x
      obtain ⟨a,ha⟩ := x.property
      change binaryNatural x.val v=v
      rw [←ha]
      exact hv (α a) ⟨a,rfl⟩
  have hic : 2 ^ fixedCodim (binaryNatural (K := F)) β.range = Nat.card D := by
    change 2 ^ Module.finrank (ZMod 2) (Vector F ⧸ fixedSpace (binaryNatural (K := F)) β.range)=_
    rw [hfixed]
    have hc := Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv (ZMod 2)
      (TwoLocalCover.fixedSpace α.range)).toEquiv
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
    rw [hc,fixed_quotient_card]
    exact (Module.natCard_eq_pow_finrank (K := F) (V := D)).symm
  rw [←relIndex_subgroupOf hAU,←hk,relIndex_ker,hm,hi,hic]
  exact Nat.card_congr {
    toFun := fun x => ⟨x.val.toAdd,x.property⟩
    invFun := fun x => ⟨Multiplicative.ofAdd x.val,x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

private theorem fixed_index_of_central_join {G : Type*} [Group G]
    (X U C A : Subgroup G) [IsMulCommutative X]
    (hUX : U ≤ X) (hsplit : X = U ⊔ C)
    (hCA : C ≤ centralizer (A : Set G)) :
    (centralizer (A : Set G)).relIndex X =
      (centralizer (A : Set G)).relIndex U := by
  let Y := X ⊓ centralizer (A : Set G)
  have hCX : C ≤ X := le_sup_right.trans_eq hsplit.symm
  have hjoin : U ⊔ Y = X := by
    apply le_antisymm (sup_le hUX inf_le_left)
    exact hsplit.le.trans (sup_le le_sup_left
      ((show C ≤ Y from le_inf hCX hCA).trans le_sup_right))
  let : CommGroup X := IsMulCommutative.instCommGroup
  have hh := relIndex_sup_right (U.subgroupOf X) (Y.subgroupOf X)
  rw [←subgroupOf_sup hUX (show Y ≤ X from inf_le_left),hjoin,
    relIndex_subgroupOf le_rfl,relIndex_subgroupOf hUX] at hh
  have he (V : Subgroup G) (hv : V ≤ X) :
      Y.subgroupOf V = (centralizer (A : Set G)).subgroupOf V := by
    ext x
    exact ⟨fun hx => hx.2,fun hx => ⟨hv x.property,hx⟩⟩
  change (Y.subgroupOf X).index = (Y.subgroupOf U).index at hh
  rwa [he X le_rfl,he U hUX] at hh

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Symplectic duality identifies the whole-Z fixed index with the order of
its displacement modulo the full vertex center. Every central attachment
is retained in that intersection. -/
theorem Input.replacement_displacement_central_index
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a : Vertex d.radical} (ha : color d.radical a=false)
    (A : Subgroup (FreeAmalgam d.radical)) (hAS : A ≤ stabilizer d.radical a) :
    (stabilizer d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))).relIndex
      ⁅A,Z d.radical a⁆ =
        (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (Z d.radical a) := by
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup)) := omegaCenterIn_elementary _
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d ha
  have hCtop : C=⊤ := by
    have hh : C.comap q=⊤ := by
      rw [show C=(K.subgroupOf d.overgroup).map q from rfl,comap_map_eq,QuotientGroup.ker_mk']
      exact h.replacement_inner_of_four_le d geometry hb
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C,hh,
      ←MonoidHom.range_eq_map,MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let κC := κ.codRestrict C (fun x => hCtop ▸ mem_top (κ x))
  let β := (e.groupEquiv.toMonoidHom.comp κC).comp (inclusion hAS)
  let σ := MovedSection.coverAction s e
  let p := MovedSection.coverProjection s e
  have hlocal : Ltilde d.radical a ⊔ Q d.radical a=stabilizer d.radical a := by
    obtain ⟨i,hinj,hir,hiL,hiU,hiQ⟩ := Sp4Four.SourceComparison.vertex_coordinates_with_kernel d.radical
      (h.replacement_two_group d) (h.replacement_core_le d) ha
    rw [←hiL,←hiQ,←Subgroup.map_sup,h.replacement_residual d,
      h.replacement_inner_of_four_le d geometry hb,←MonoidHom.range_eq_map,hir]
  have hker' (w : s.space.toSubmodule) : p w=0 ↔
      j (Multiplicative.ofAdd w) ∈ stabilizer d.radical a ⊓
        centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    have hwu : j (Multiplicative.ofAdd w) ∈ U d.radical a := hjr ▸ ⟨_,rfl⟩
    rw [hker]
    refine ⟨fun hw => ⟨(U_le_Z a |>.trans (Z_le_stabilizer d.radical a)) hwu,?_⟩,
      fun hw => centralizer_le (Ltilde_le_stabilizer a) hw.2⟩
    have hL : Ltilde d.radical a ≤ centralizer ({j (Multiplicative.ofAdd w)} : Set _) :=
      fun y hy => mem_centralizer_singleton_iff.mpr (hw y hy)
    have hQ : Q d.radical a ≤ centralizer ({j (Multiplicative.ofAdd w)} : Set _) := by
      intro y hy
      apply mem_centralizer_singleton_iff.mpr
      exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes a ha)) hy _ (U_le_Z a hwu)).symm
    intro y hy
    exact mem_centralizer_singleton_iff.mp ((sup_le hL hQ) (hlocal.symm ▸ hy))
  have heq := embedded_commutator_central_index (F := E.Carrier)
    (W := s.space.toSubmodule) (G := FreeAmalgam d.radical) σ p he (U d.radical a) A
    (stabilizer d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
    j hj hjr β (by
      intro y w
      change j (Multiplicative.ofAdd (s.space.toRepresentation
        (e.groupEquiv.symm (e.groupEquiv (κC (inclusion hAS y)))) w))=_
      rw [e.groupEquiv.symm_apply_apply]
      exact hconj (inclusion hAS y) w) hker'
  rw [commutator_comm A,h.replacement_Z_commutator_eq_U d geometry hb ha A hAS,commutator_comm]
  rw [heq]
  let : IsElementaryAbelian 2 (Z d.radical a) := geometry.Z_elementary (by omega) a ha
  exact (fixed_index_of_central_join (Z d.radical a) (U d.radical a)
    (Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) A
    (U_le_Z a) (h.replacement_Z_eq_U_sup_fixed d geometry hb ha)
    (inf_le_right.trans (centralizer_le hAS))).symm

/-- The exact central quotient of the full critical commutator is the
opposite critical image, through the literal neighborhood kernel. -/
theorem Input.replacement_critical_commutator_central_index
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical) :
    (stabilizer d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))).relIndex
      ⁅Z d.radical a,Z d.radical z⁆ = (Q d.radical z).relIndex (Z d.radical a) := by
  rw [commutator_comm (Z d.radical a),h.replacement_displacement_central_index d geometry hb
    path.start_color (Z d.radical z) (path.endpoint_Z_le_start_stabilizer (by omega))]
  have hAZ : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  have hC := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) z path.end_color
  change ((centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).subgroupOf (Z d.radical a)).index =
    ((Q d.radical z).subgroupOf (Z d.radical a)).index
  congr 1
  rw [←hC]
  ext x
  exact ⟨fun hx => ⟨hAZ x.property,hx⟩,fun hx => hx.2⟩

omit h in
/-- A quadratic edge actor whose displacement meets the edge-fixed seed only
in the full covering kernel has at most field order. This also applies to
the joined actor in the terminal comparison. -/
theorem embedded_actor_card_le_of_central_fixed_intersection
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U A T C E : Subgroup G) [Finite T] (hT : IsPGroup 2 T) (hAT : A ≤ T)
    (j : Multiplicative W →* G) (hjr : j.range=U) (β : T →* L (K := F))
    (hact : ∀ (a : T) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (hker : ∀ w : W, p w=0 ↔ j (Multiplicative.ofAdd w) ∈ C)
    (hfixed : ∀ w : W, (∀ t : T, σ (β t) w=w) → j (Multiplicative.ofAdd w) ∈ E)
    (hcentral : ⁅A,U⁆ ⊓ E ≤ C)
    (hquad : let α := (commutator (Sp F)).subtype.comp (β.comp (inclusion hAT))
      ∀ x ∈ α.range, ∀ y ∈ α.range, ∀ v : Vector F, x • (y • v-v)=y • v-v) :
    Nat.card ((commutator (Sp F)).subtype.comp (β.comp (inclusion hAT))).range ≤ Nat.card F := by
  let αT := (commutator (Sp F)).subtype.comp β
  let α := αT.comp (inclusion hAT)
  by_contra! hlarge
  have hself : (form F).orthogonal (displacementSpace α.range)=displacementSpace α.range :=
    large_quadratic_displacement_self_orthogonal α.range hquad hlarge
  obtain ⟨v,hv,hfix⟩ := Representation.pGroup_fix_nonzero_vector (F := F)
    (by rw [ringChar.eq F 2]; decide) (by simpa only [ringChar.eq F 2] using hT)
    ((symplecticNatural 2).comp αT)
  have hvD : v ∈ displacementSpace α.range := by
    rw [←hself,orthogonal_displacementSpace]
    rintro x ⟨a,rfl⟩
    exact hfix (inclusion hAT a)
  obtain ⟨w,hw,hwcomm⟩ := natural_displacement_lifts U A j hjr (β.comp (inclusion hAT))
    σ (fun a w => hact (inclusion hAT a) w) p hp.1 v hvD
  have hwE : j (Multiplicative.ofAdd w) ∈ E := hfixed w (fun t => by
    apply cover_fixed_of_projection_fixed p hp (β t) w
    rw [hw]
    exact hfix t)
  have hw0 : p w=0 := (hker w).mpr (hcentral ⟨hwcomm,hwE⟩)
  exact hv (hw.symm.trans hw0)

omit h in
private theorem critical_cover_actor_quadratic
    {M F W : Type*} [Group M] [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W]
    {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : Function.Surjective p)
    (j : Multiplicative W →* FreeAmalgam R) (hj : Function.Injective j) (hjr : j.range=U R z)
    (β : Z R a →* L (K := F))
    (hact : ∀ (a : Z R a) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹) :
    let α := (commutator (Sp F)).subtype.comp β
    ∀ x ∈ α.range, ∀ y ∈ α.range, ∀ v : Vector F, x • (y • v-v)=y • v-v := by
  dsimp only
  have hquad := critical_embedded_actor_quadratic path hb σ j hj hjr β hact
  rintro x ⟨x,rfl⟩ y ⟨y,rfl⟩ v
  obtain ⟨w,rfl⟩ := hp v
  have hh := congrArg p (hquad (β x) ⟨x,rfl⟩ (β y) ⟨y,rfl⟩ w)
  change binaryNatural (β x) (binaryNatural (β y) (p w)-p w) =
    binaryNatural (β y) (p w)-p w
  simpa only [map_sub,p.isIntertwining] using hh

omit h in
private theorem embedded_fixed_mem_omegaCenter
    {G D W : Type*} [Group G] [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (T : Subgroup G) (j : Multiplicative W →* G)
    (hjT : j.range ≤ T) (σ : Representation (ZMod 2) D W) (β : T →* D)
    (hact : ∀ (a : T) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (w : W) (hw : ∀ y : T, σ (β y) w=w)
    (hp : j (Multiplicative.ofAdd w)^2=1) :
    j (Multiplicative.ofAdd w) ∈ omegaCenter T := by
  apply mem_omegaCenter_iff.mpr
  refine ⟨hjT ⟨_,rfl⟩,hp,?_⟩
  intro y hy
  have hh := (hact ⟨y,hy⟩ w).symm.trans
    (congrArg (fun w => j (Multiplicative.ofAdd w)) (hw ⟨y,hy⟩))
  exact mul_inv_eq_iff_eq_mul.mp hh

-- The full-cover coordinates take about ten seconds of tactic work.
-- Keep the modest allowance local to this application; all model lemmas
-- and exported assembly theorems use the default budget.
set_option maxHeartbeats 400000 in
private theorem critical_image_le_field_of_central_edge_intersection
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (hcentral : ⁅Z d.radical a,Z d.radical z⁆ ⊓ Z d.radical t ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
    (Q d.radical a).relIndex (Z d.radical z) ≤ Nat.card F := by
  let A := Z d.radical z
  let T := Q d.radical t
  have ht : color d.radical t=true := by
    have hn := adjacent_color_ne d.radical hat
    rw [path.start_color] at hn
    cases hh : color d.radical t <;> simp_all
  have hTS : T ≤ stabilizer d.radical a := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hAT : A ≤ T := by
    apply Z_le_Q_of_dist_lt d.radical z (geometry.exists_critical z path.end_color)
    rw [geometry.distance_constant z path.end_color,SimpleGraph.dist_comm,←hfirst,
      path.dist_end,path.length_eq_b]
    change geometry.b d.radical-1 < geometry.b d.radical
    omega
  have hUT : U d.radical a ≤ T := by
    obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
      (h.replacement_two_group d) (h.replacement_core_le d) path.start_color hat
    apply (U_le_Z a).trans
    apply ((Z_le_VBall d.radical a 2).trans (geometry.V_le_Q (by omega) a path.start_color)).trans
    rw [←hiQ,show T=Q d.radical t from rfl,←hiR]
    exact map_mono (h.replacement_core_le d)
  let := finite_stabilizer d.radical t
  let : Finite T := Finite.of_injective
    (inclusion (show T ≤ stabilizer d.radical t from fun _ hx => hx.1)) (inclusion_injective _)
  have hT : IsPGroup 2 T := by
    obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
      (h.replacement_two_group d) (h.replacement_core_le d) path.start_color hat
    rw [show T=Q d.radical t from rfl,←hiR]
    exact (h.replacement_two_group d).map i
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup)) := omegaCenterIn_elementary _
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d path.start_color
  have hCtop : C=⊤ := by
    have hh : C.comap q=⊤ := by
      rw [show C=(K.subgroupOf d.overgroup).map q from rfl,comap_map_eq,QuotientGroup.ker_mk']
      exact h.replacement_inner_of_four_le d geometry hb
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C,hh,
      ←MonoidHom.range_eq_map,MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let κC := κ.codRestrict C (fun x => hCtop ▸ mem_top (κ x))
  let β := (e.groupEquiv.toMonoidHom.comp κC).comp (inclusion hTS)
  let α := (commutator (Sp E.Carrier)).subtype.comp (β.comp (inclusion hAT))
  let σ := MovedSection.coverAction s e
  let p := MovedSection.coverProjection s e
  have hact (y : T) (w : s.space.toSubmodule) : j (Multiplicative.ofAdd (σ (β y) w))=
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC (inclusion hTS y)))) w))=_
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj (inclusion hTS y) w
  let : IsElementaryAbelian 2 (Z d.radical a) := geometry.Z_elementary (by omega) a path.start_color
  have hfixed (w : s.space.toSubmodule) (hw : ∀ y : T, σ (β y) w=w) :
      j (Multiplicative.ofAdd w) ∈ Z d.radical t := by
    rw [Z,if_neg (by simp [ht])]
    apply embedded_fixed_mem_omegaCenter T j (hjr.le.trans hUT) σ β hact w hw
    exact elemPow_eq_one_of_isElementaryAbelian _ (U_le_Z a (hjr ▸ ⟨_,rfl⟩))
  have hcentral' : ⁅A,U d.radical a⁆ ⊓ Z d.radical t ≤
      centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_trans _ (hcentral.trans (centralizer_le (Ltilde_le_stabilizer a)))
    rw [commutator_comm A]
    exact inf_le_inf_right _ (commutator_mono (U_le_Z a) le_rfl)
  have hquad : ∀ x ∈ α.range, ∀ y ∈ α.range, ∀ v : Vector E.Carrier,
      x • (y • v-v)=y • v-v := by
    let rev : CriticalPath d.radical geometry z a :=
      { start_color := path.end_color
        walk := path.walk.reverse
        shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
        critical := critical_reverse d.radical geometry
          (MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
            (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d))
          a path.start_color (by rw [geometry.distance_constant a path.start_color]; exact (by omega : 0 < geometry.b d.radical))
          z path.end_color path.critical }
    exact critical_cover_actor_quadratic (M := d.overgroup) (F := E.Carrier)
      (W := s.space.toSubmodule) rev (by omega) σ p he.1 j hj hjr
      (β.comp (inclusion hAT)) (fun x w => hact (inclusion hAT x) w)
  have hbound := embedded_actor_card_le_of_central_fixed_intersection (F := E.Carrier)
    (W := s.space.toSubmodule) (G := FreeAmalgam d.radical) σ p he
    (U d.radical a) A T (centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)))
    (Z d.radical t) hT hAT j hjr β hact hker hfixed hcentral' hquad
  have hk : α.ker=(Q d.radical a).subgroupOf A := by
    ext x
    change ((e.groupEquiv (κC (inclusion hTS (inclusion hAT x)))).val=1) ↔ x.val ∈ Q d.radical a
    rw [show ∀ u : L (K := E.Carrier), (u.val=1 ↔ u=1) from fun u => ⟨fun hu => Subtype.ext hu,fun hu => congrArg Subtype.val hu⟩,
      e.groupEquiv.map_eq_one_iff]
    have heq : κC (inclusion hTS (inclusion hAT x))=1 ↔
        inclusion hTS (inclusion hAT x) ∈ κ.ker := Subtype.ext_iff
    rw [heq]
    constructor
    · intro hx
      exact hκQ ▸ mem_map_of_mem (stabilizer d.radical a).subtype hx
    · intro hx
      obtain ⟨y,hy,hyx⟩ := hκQ.symm ▸ hx
      have he : y=inclusion hTS (inclusion hAT x) := Subtype.ext hyx
      exact he ▸ hy
  have hFc : Nat.card E.Carrier=Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have hbound' : (Q d.radical a).relIndex (Z d.radical z) ≤ Nat.card F := by
    rw [←index_ker,hk,hFc] at hbound
    exact hbound
  exact hbound'

/-- A full critical commutator meeting its first edge seed only in the
vertex center has both critical images of exactly field order. -/
theorem Input.replacement_critical_indices_eq_field_of_central_edge_intersection
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (hcentral : ⁅Z d.radical a,Z d.radical z⁆ ⊓ Z d.radical t ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
    (Q d.radical z).relIndex (Z d.radical a)=Nat.card F ∧
      (Q d.radical a).relIndex (Z d.radical z)=Nat.card F := by
  have hbound' := critical_image_le_field_of_central_edge_intersection h d path hb hat hfirst hcentral
  let rev : CriticalPath d.radical geometry z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical geometry
        (MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
          (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d))
        a path.start_color (by rw [geometry.distance_constant a path.start_color]; exact (by omega : 0 < geometry.b d.radical))
        z path.end_color path.critical }
  have hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2 := by
    have hq : 1 < Nat.card F := Finite.one_lt_card
    exact hbound'.trans_lt (by nlinarith only [hq])
  obtain ⟨hz,ha⟩ := h.replacement_small_critical_indices_eq_field d rev (by omega) hsmall
  exact ⟨ha,hz⟩

/-- The actual large-mover terminal sequence now has both critical images
of order q and both full-center quotients of each R₄ of order q. The same
chosen paths, full edge fixed clauses and all overlaps are retained. -/
theorem Input.replacement_large_mover_terminal_indices
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical)
    (hJm : Nat.card F^2 < (centralizer (Subgroup.SmallMover.join (U d.radical p.first)
      (Q d.radical p.first) (Q d.radical (p.path.walk.getVert 1)) (Nat.card F^2) :
        Set (FreeAmalgam d.radical))).relIndex (U d.radical p.first)) :
    ∃ s : ℕ → CriticalSegment geometry, s 0 = p ∧
      (∀ i, BackwardLink geometry (pointPathChoice geometry (Nat.card F)) (s i) (s (i+1))) ∧
      (∀ i k j, j+2*k ≤ geometry.b d.radical →
        (s (i+k)).path.walk.getVert (j+2*k) = (s i).path.walk.getVert j) ∧
      (∀ i, let a := (s (i+2)).first
        let z := (s (i+2)).last
        let R₄ := ⁅Z d.radical a,Z d.radical z⁆
        (Q d.radical z).relIndex (Z d.radical a)=Nat.card F ∧
        (Q d.radical a).relIndex (Z d.radical z)=Nat.card F ∧
        (stabilizer d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))).relIndex R₄ =
          Nat.card F ∧
        (stabilizer d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))).relIndex R₄ =
          Nat.card F ∧
        R₄ ⊓ Z d.radical ((s (i+2)).path.walk.getVert 1) ≤
          (stabilizer d.radical (s (i+1)).first ⊓
            centralizer (stabilizer d.radical (s (i+1)).first : Set (FreeAmalgam d.radical))) ⊓
          (stabilizer d.radical (s i).first ⊓
            centralizer (stabilizer d.radical (s i).first : Set (FreeAmalgam d.radical))) ⊓
          (stabilizer d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))) := by
  obtain ⟨s,hs0,hs,hover,hcent⟩ := h.replacement_large_mover_terminal_centers d p hb hJm
  refine ⟨s,hs0,hs,hover,?_⟩
  intro i
  dsimp only
  have hat : Adjacent d.radical (s (i+2)).first ((s (i+2)).path.walk.getVert 1) := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      ((s (i+2)).path.walk.adj_getVert_succ
        (by rw [(s (i+2)).path.length_eq_b]; omega : 0 < (s (i+2)).path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  obtain ⟨hia,hiz⟩ := h.replacement_critical_indices_eq_field_of_central_edge_intersection d
    (s (i+2)).path hb.le hat rfl ((hcent i).trans (inf_le_right.trans inf_le_right))
  have hia' := h.replacement_critical_commutator_central_index d (s (i+2)).path hb.le
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  let rev := (s (i+2)).reverse hedge (by omega)
  have hiz' := h.replacement_critical_commutator_central_index d rev.path hb.le
  change (stabilizer d.radical (s (i+2)).last ⊓
    centralizer (stabilizer d.radical (s (i+2)).last : Set (FreeAmalgam d.radical))).relIndex
      ⁅Z d.radical (s (i+2)).last,Z d.radical (s (i+2)).first⁆ =
        (Q d.radical (s (i+2)).first).relIndex (Z d.radical (s (i+2)).last) at hiz'
  rw [commutator_comm] at hiz'
  exact ⟨hia,hiz,hia'.trans hia,hiz'.trans hiz,hcent i⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
