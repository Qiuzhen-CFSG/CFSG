module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.G2.MSEmbeddedKernel
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.G2.MSCriticalCoordinates

/-!
# One embedded central kernel for the two critical G₂ actions

The original central-omega cover transports to every original-color vertex
with its intrinsic offender-kernel criterion. The moving subgroup U already
has the full critical image, so the criterion applies in both directions of
a critical pair. It identifies the two central kernels as subgroups of the
original amalgam and places their common kernel in [Uα,Uα′].

The source applications construct this equality from Sylow-normalizer escape,
retain both original root-coordinate systems, and identify the two projected
images of [Uα,Uα′] pointwise through their common original elements. Thus the
later field comparison has an actual identification of the commutator images.
The comparison of scalar actions, and the resulting G₂ exclusion, remain with
qt-d-1222-natural-line-action; final 11.2.3 assembly belongs to
qt-d-1222-natural-normalizer-source.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.2), printed pp.865--866, using (1.5)(iv), p.843.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology
open scoped IsMulCommutative Pointwise commutatorElement
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS
open ChapterC ChapterC.MSCentralOrbit
open RecognitionSource.FusionReducibleNormalizer
open Stellmacher.PushingUp.AmalgamGraph BinaryMS.MS93
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction
    (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
local notation "H" => (L ⊔ (T : Subgroup G) : Subgroup G)
local notation "K" => Subgroup.subgroupOf L (L ⊔ (T : Subgroup G))
local notation "R" => Subgroup.subgroupOf (T : Subgroup G) (L ⊔ (T : Subgroup G))

include D S in
private theorem residual_eq : pResidual 2 H = K := by
  apply component_eq_residual K R S.source.maximal_faithful.1.1.1
    (T.isPGroup'.of_equiv (subgroupOfEquivOfLe le_sup_right).symm)
  intro h
  have hh : (h : G) ∈ (L : Set G) * ((T : Subgroup G) : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left L (T : Subgroup G)
      D.sylow_normalizes_component]
    exact h.property
  obtain ⟨k,hk,r,hr,he⟩ := hh
  exact ⟨⟨k,mem_sup_left hk⟩,hk,⟨r,mem_sup_right hr⟩,hr,Subtype.ext he⟩

include D S m in
private theorem image_centric :
    centralizer ((K).map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H)) = ⊥ := by
  have hF : 2 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    exact (show (2 : ℕ)^1 < 2^S.field.degree from Nat.pow_lt_pow_right (by decide) S.nonbinary)
  let : IsSimpleGroup (Atlas.G2.Model S.field.Carrier) := Atlas.G2.isSimple hF
  let : IsSimpleGroup (K ⧸ pCore 2 K) := (source_component_model D S m).some.isSimpleGroup
  apply (component_image_structure K R S.source.maximal_faithful.1.1.1
    (T.isPGroup'.of_equiv (subgroupOfEquivOfLe le_sup_right).symm) ?_).2.2.2.2
  intro h
  have hh : (h : G) ∈ (L : Set G) * ((T : Subgroup G) : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left L (T : Subgroup G)
      D.sylow_normalizes_component]
    exact h.property
  obtain ⟨k,hk,r,hr,he⟩ := hh
  exact ⟨⟨k,mem_sup_left hk⟩,hk,⟨r,mem_sup_right hr⟩,hr,Subtype.ext he⟩


/-- The intrinsic central-kernel criterion for every actual offender at a vertex. -/
def HasOffenderKernel {M J : Type*} [Group M] [Group J]
    {R₀ : Subgroup M} {a : Vertex R₀} {B : Subgroup J}
    (E : VertexAction R₀ a B) : Prop :=
  ∀ (A : Subgroup (FreeAmalgam R₀)) (hA : A ≤ stabilizer R₀ a),
    BinaryOffender.IsOffender E.action (E.quotient.comp (inclusion hA)).range →
    (U R₀ a ⊓ centralizer (Ltilde R₀ a : Set (FreeAmalgam R₀))) ≤ ⁅A,U R₀ a⁆ ∧
    ∀ x ∈ ⁅A,U R₀ a⁆, x ≠ 1 →
      (x ∈ U R₀ a ⊓ centralizer (Ltilde R₀ a : Set (FreeAmalgam R₀)) ↔
        ¬ ∃ y ∈ A, ∃ u ∈ U R₀ a, ⁅y,u⁆ = x)

private theorem vertexKernelAction_of_cover
    {M J W : Type*} [Group M] [Group J] [Finite J] [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W]
    {R₀ : Subgroup M} {a : Vertex R₀} {ρ : Representation (ZMod 2) J W}
    {B : Subgroup J} [B.Normal] (F : BinaryField) (hF : F.degree = 2)
    (s : MovedSection ρ B) (e : ActionEquiv (s.action.comp B.subtype) (binaryG2 F))
    (hp : IsCover (MovedSection.coverProjection s e))
    (j : Multiplicative s.space.toSubmodule →* FreeAmalgam R₀) (hj : Function.Injective j)
    (hjr : j.range = U R₀ a) (κ : stabilizer R₀ a →* J) (hκ : Function.Surjective κ)
    (hkQ : κ.ker.map (stabilizer R₀ a).subtype = Q R₀ a)
    (hkC : κ.ker.map (stabilizer R₀ a).subtype = C R₀ a)
    (hkL : ((Ltilde R₀ a).subgroupOf (stabilizer R₀ a)).map κ = B)
    (hf : Function.Injective (MovedSection.ambientAction s e))
    (hconj : ∀ (g : stabilizer R₀ a) (v : s.space.toSubmodule),
      j (Multiplicative.ofAdd (s.space.toRepresentation (κ g) v)) =
        (g : FreeAmalgam R₀) * j (Multiplicative.ofAdd v) * (g : FreeAmalgam R₀)⁻¹)
    (hker : ∀ v : s.space.toSubmodule, MovedSection.coverProjection s e v = 0 ↔
      j (Multiplicative.ofAdd v) ∈ centralizer (Ltilde R₀ a : Set (FreeAmalgam R₀))) :
    ∃ E : VertexAction R₀ a B, HasOffenderKernel E := by
  obtain ⟨π,hπ,hπval,hact⟩ := Representation.SymplecticFourOrthogonalCover.exists_equivariant_embedded_projection
    (U R₀ a) (stabilizer R₀ a) (U_normalized a) s.space.toRepresentation
    (MovedSection.ambientAction s e) j hj hjr (MovedSection.coverProjection s e).toLinearMap
    hp.1 (MovedSection.coverProjection_ambient s e) κ hconj
  have hπker (u : U R₀ a) : π u = 1 ↔
      u.val ∈ centralizer (Ltilde R₀ a : Set (FreeAmalgam R₀)) := by
    obtain ⟨w,hw⟩ := show u.val ∈ j.range from hjr.symm ▸ u.property
    have hu : u = ⟨j w,by rw [←hjr]; exact ⟨w,rfl⟩⟩ := Subtype.ext hw.symm
    have hv := hπval w.toAdd
    simp only [ofAdd_toAdd] at hv
    rw [hu,hv]
    exact hker w.toAdd
  have hkerImage : (MovedSection.coverProjection s e).toLinearMap.ker.toAddSubgroup.toSubgroup.map j =
      U R₀ a ⊓ centralizer (Ltilde R₀ a : Set (FreeAmalgam R₀)) := by
    ext x
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨hjr ▸ ⟨w,rfl⟩,(hker w.toAdd).mp hw⟩
    · rintro ⟨hx,hc⟩
      obtain ⟨w,rfl⟩ := show x ∈ j.range from hjr.symm ▸ hx
      exact ⟨w,(hker w.toAdd).mpr hc,rfl⟩
  have hπK : π.ker.map (U R₀ a).subtype =
      U R₀ a ⊓ centralizer (Ltilde R₀ a : Set (FreeAmalgam R₀)) := by
    ext x
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨u.property,(hπker u).mp hu⟩
    · rintro ⟨hx,hc⟩
      exact ⟨⟨x,hx⟩,(hπker ⟨x,hx⟩).mpr hc,rfl⟩
  let E : VertexAction R₀ a B := ⟨F,hF,inferInstance,e.groupEquiv,MovedSection.ambientAction s e,
    MovedSection.ambientAction_component s e,hf,κ,hκ,hkQ,hkC,hkL,π,hπ,hπK,hact⟩
  refine ⟨E,?_⟩
  intro A hA hOff
  exact embedded_offender_kernel F hF s e hp hf A (U R₀ a) _ j hj hjr
    (κ.comp (inclusion hA)) (fun x w => hconj (inclusion hA x) w) hkerImage hOff

include D S m in
/-- The original G₂ escape constructs the faithful full vertex action on its
natural moving quotient, including all literal quotient and conjugation maps. -/
theorem source_vertex_kernel_action
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    {a : Vertex R} (ha : color R a = false) :
    ∃ E : VertexAction R a ((K).map (QuotientGroup.mk' (pCore 2 H))), HasOffenderKernel E := by
  obtain ⟨hk,hn,hmodule⟩ := source_initial_module D S m hescape
  let := hn
  let q := QuotientGroup.mk' (pCore 2 H)
  let hq := QuotientGroup.mk'_surjective (pCore 2 H)
  let X := omegaCenterIn (pCore 2 H)
  let B := (K).map q
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation X q hq hk) B
  obtain ⟨hiModule,F,hF,⟨e⟩⟩ := hmodule
  have he := MovedSection.coverProjection_isCover s hiModule e
  have hp : IsPGroup 2 R :=
    T.isPGroup'.of_equiv (subgroupOfEquivOfLe le_sup_right).symm
  have hQR : pCore 2 H ≤ R :=
    pCore_isPGroup.le_sylow_of_normal (T.subtype le_sup_right)
  obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ :=
    ChapterC.RankTwo.Sp4Four.SourceComparison.vertex_coordinates_with_kernel R hp hQR ha
  rw [residual_eq D S] at hiL
  have hu : (⁅X,K⁆).map i = U R a := by
    rw [←source_initial_commutator D S m hescape]
    simpa only [ChapterC.RankTwo.Sp4Four.LocalPackage.initialLayer,residual_eq D S] using hiU
  let j := i.comp (ElementaryMovedCover.embedding X K q hq hk)
  let κ := ElementaryMovedCover.embeddedQuotient q i hi (stabilizer R a) hir
  have hkQ : κ.ker.map (stabilizer R a).subtype = Q R a := by
    rw [ElementaryMovedCover.embeddedQuotient_kernel,QuotientGroup.ker_mk']
    exact hiQ
  have hj : Function.Injective j := hi.comp (ElementaryMovedCover.embedding_injective _ _ _ _ _)
  have hjU : j.range = U R a := by
    dsimp only [j]
    rw [MonoidHom.range_comp,ElementaryMovedCover.embedding_range]
    exact hu
  have hkC : κ.ker.map (stabilizer R a).subtype = C R a :=
    hkQ.trans (MSCentralOrbit.C_eq_Q R hp hQR
      (source_omegaOrbit_centralizer D S m hescape) a ha).symm
  have hkL : ((Ltilde R a).subgroupOf (stabilizer R a)).map κ = B := by
    rw [←hiL]
    exact ElementaryMovedCover.embeddedQuotient_subgroup q i hi _ hir _
  have hfaith : Function.Injective (MovedSection.ambientAction s e) := by
    apply MovedSection.ambientAction_faithful s e _ (image_centric D S m)
    intro g h heq
    apply Atlas.G2.Natural.action_injective F.Carrier
    exact LinearMap.ext (fun v => LinearMap.congr_fun heq v)
  have hconj : ∀ (g : stabilizer R a) (v : s.space.toSubmodule),
      j (Multiplicative.ofAdd (s.space.toRepresentation (κ g) v)) =
        (g : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (g : FreeAmalgam R)⁻¹ :=
    ElementaryMovedCover.embedded_ambient_conjugate _ _ _ _ _ i hi _ hir
  obtain ⟨f,hf,hact,hker⟩ := ElementaryMovedCover.exists_conjugationActor
    X K q hq hk i hi (Ltilde R a) hiL e
  exact vertexKernelAction_of_cover F hF s e he j hj hjU κ
    (ElementaryMovedCover.embeddedQuotient_surjective q i hi _ hir hq)
    hkQ hkC hkL hfaith hconj hker

open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

/-- Restricting the critical actor to U preserves its entire image. -/
theorem critical_moving_range
    {M J₁ J₂ : Type*} [Group M] [Finite M]
    [Group J₁] [Finite J₁] [Group J₂] [Finite J₂]
    {R₀ : Subgroup M} {geometry : Geometry R₀} {a z : Vertex R₀}
    (path : CriticalPath R₀ geometry a z) (hb : 0 < geometry.b R₀)
    (hC : EdgeCentralizerCondition R₀)
    {B₁ : Subgroup J₁} {B₂ : Subgroup J₂}
    (Ea : VertexAction R₀ a B₁) (Ez : VertexAction R₀ z B₂) :
    ((criticalActor path Ez.quotient).comp (inclusion (U_le_Z a))).range =
      (criticalActor path Ez.quotient).range := by
  let δ := criticalActor path Ez.quotient
  let d := δ.comp (inclusion (U_le_Z a))
  let := finite_Z R₀ a
  let : Finite (U R₀ a) := Finite.of_injective (inclusion (U_le_Z a)) (inclusion_injective _)
  have hk : d.ker = (centralizer (Z R₀ z : Set (FreeAmalgam R₀))).subgroupOf (U R₀ a) :=
    ChapterC.RankTwo.Sp4Four.SourceComparison.restricted_kernel_of_mapped_centralizer
      _ _ _ ((U_le_Z a).trans (Z_le_stabilizer_of_dist_le a
        (geometry.exists_critical a path.start_color) path.critical.1.le))
      Ez.quotient Ez.kernel_centralizer
  have hc : Nat.card d.range = 64 := by
    rw [←index_ker,hk]
    exact critical_moving_index path hb hC Ea Ez
  let := Ez.component_normal
  have hoff := critical_actor_offenders path hb hC Ea Ez
  have hr := (ambient_offender_rank_six Ez.field Ez.degree Ez.action _
    Ez.componentEquiv Ez.component_apply Ez.faithful _ hoff).2.1
  have hc' : Nat.card δ.range = 64 := by
    rw [hoff.1.card_eq_two_pow_rank,hr]
    rfl
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,rfl⟩
    exact ⟨inclusion (U_le_Z a) x,rfl⟩
  · exact le_of_eq (hc'.trans hc.symm)

/-- The opposite moving subgroup is itself an offender in the full vertex action. -/
theorem critical_moving_offender
    {M J₁ J₂ : Type*} [Group M] [Finite M]
    [Group J₁] [Finite J₁] [Group J₂] [Finite J₂]
    {R₀ : Subgroup M} {geometry : Geometry R₀} {a z : Vertex R₀}
    (path : CriticalPath R₀ geometry a z) (hb : 0 < geometry.b R₀)
    (hC : EdgeCentralizerCondition R₀)
    {B₁ : Subgroup J₁} {B₂ : Subgroup J₂}
    (Ea : VertexAction R₀ a B₁) (Ez : VertexAction R₀ z B₂) :
    IsOffender Ez.action ((criticalActor path Ez.quotient).comp (inclusion (U_le_Z a))).range := by
  rw [critical_moving_range path hb hC Ea Ez]
  exact critical_actor_offenders path hb hC Ea Ez

/-- The two actual critical cover kernels are equal inside the original amalgam,
and this common kernel lies in the commutator of the two moving subgroups. -/
theorem critical_kernels_eq
    {M J₁ J₂ : Type*} [Group M] [Finite M]
    [Group J₁] [Finite J₁] [Group J₂] [Finite J₂]
    {R₀ : Subgroup M} {geometry : Geometry R₀} {a z : Vertex R₀}
    (path : CriticalPath R₀ geometry a z) (hb : 0 < geometry.b R₀)
    (hC : EdgeCentralizerCondition R₀)
    {B₁ : Subgroup J₁} {B₂ : Subgroup J₂}
    (Ea : VertexAction R₀ a B₁) (Ez : VertexAction R₀ z B₂)
    (ha : HasOffenderKernel Ea) (hz : HasOffenderKernel Ez) :
    U R₀ a ⊓ centralizer (Ltilde R₀ a : Set (FreeAmalgam R₀)) =
      U R₀ z ⊓ centralizer (Ltilde R₀ z : Set (FreeAmalgam R₀)) ∧
    U R₀ a ⊓ centralizer (Ltilde R₀ a : Set (FreeAmalgam R₀)) ≤ ⁅U R₀ a,U R₀ z⁆ := by
  have hba : 0 < criticalDistance R₀ a (geometry.exists_critical a path.start_color) := by
    rw [geometry.distance_constant a path.start_color]
    exact hb
  have hrev := critical_reverse R₀ geometry hC a path.start_color hba z path.end_color path.critical
  let rev : CriticalPath R₀ geometry z a := CriticalPath.ofPair path.end_color hrev
  have hUa := (U_le_Z a).trans (Z_le_stabilizer_of_dist_le a
    (geometry.exists_critical a path.start_color) path.critical.1.le)
  have hUz := (U_le_Z z).trans (Z_le_stabilizer_of_dist_le z
    (geometry.exists_critical z path.end_color) hrev.1.le)
  obtain ⟨hkz,hcz⟩ := hz (U R₀ a) hUa (critical_moving_offender path hb hC Ea Ez)
  obtain ⟨hka,hca⟩ := ha (U R₀ z) hUz (critical_moving_offender rev hb hC Ez Ea)
  exact ⟨(embedded_kernels_eq (U R₀ a) (U R₀ z) _ _ hkz hcz hka hca).symm,
    by rwa [commutator_comm] at hka⟩

include D S m in
/-- Sylow-normalizer escape identifies both central-cover kernels in the
literal critical geometry, without any additional cover or field premise. -/
theorem source_critical_kernels_eq
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R) :
    U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) =
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) ∧
    U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) ≤ ⁅U R a,U R z⁆ := by
  obtain ⟨Ea,hEa⟩ := source_vertex_kernel_action D S m hescape path.start_color
  obtain ⟨Ez,hEz⟩ := source_vertex_kernel_action D S m hescape path.end_color
  exact critical_kernels_eq path hb (source_critical_geometry D S m hescape).2 Ea Ez hEa hEz

include D S m in
/-- The original escape supplies a reversible critical pair with both marked
root actions and one common embedded central kernel in their commutator. -/
theorem source_critical_kernel_root_pair
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ g : Geometry R, 0 < g.b R ∧ Even (g.b R) ∧
      ∃ a : Vertex R, ∃ ha : color R a = false,
      ∃ hc : CriticalPair R (alpha R) a (g.exists_critical (alpha R) rfl),
      ∃ hr : CriticalPair R a (alpha R) (g.exists_critical a ha),
        ⁅Z R (alpha R),Z R a⁆ ≠ ⊥ ∧
      ∃ Ea : VertexAction R (alpha R) ((K).map (QuotientGroup.mk' (pCore 2 H))),
      ∃ Ez : VertexAction R a ((K).map (QuotientGroup.mk' (pCore 2 H))),
        Nonempty (CriticalRootCoordinates (CriticalPath.ofPair (geometry := g) rfl hc) Ez) ∧
        Nonempty (CriticalRootCoordinates (CriticalPath.ofPair (geometry := g) ha hr) Ea) ∧
        U R (alpha R) ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)) =
          U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) ∧
        U R (alpha R) ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)) ≤
          ⁅U R (alpha R),U R a⁆ := by
  obtain ⟨g,hpos,hev,a,ha,hc,hr,hn,Ea,Ez,hca,hcz⟩ := source_critical_root_pair D S m hescape
  exact ⟨g,hpos,hev,a,ha,hc,hr,hn,Ea,Ez,hca,hcz,
    source_critical_kernels_eq D S m hescape (CriticalPath.ofPair (geometry := g) rfl hc) hpos⟩

private theorem range_equiv_of_kernel_eq
    {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (g : A →* C) (h : f.ker = g.ker) :
    ∃ e : f.range ≃* g.range, ∀ x, e (f.rangeRestrict x) = g.rangeRestrict x := by
  let e := (QuotientGroup.quotientKerEquivRange f).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans (QuotientGroup.quotientKerEquivRange g))
  refine ⟨e,?_⟩
  intro x
  have hf : (QuotientGroup.quotientKerEquivRange f) (QuotientGroup.mk x) = f.rangeRestrict x := rfl
  change (QuotientGroup.quotientKerEquivRange g)
    ((QuotientGroup.quotientMulEquivOfEq h)
      ((QuotientGroup.quotientKerEquivRange f).symm (f.rangeRestrict x))) = _
  rw [←hf,MulEquiv.symm_apply_apply,QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- On a common embedded subgroup, equality of the actual central kernels
identifies the two projected images, sending each literal projected element
to its other projection. -/
theorem VertexAction.common_projection_equiv
    {M J₁ J₂ : Type*} [Group M] [Group J₁] [Group J₂]
    {R₀ : Subgroup M} {a z : Vertex R₀} {B₁ : Subgroup J₁} {B₂ : Subgroup J₂}
    (Ea : VertexAction R₀ a B₁) (Ez : VertexAction R₀ z B₂)
    (W : Subgroup (FreeAmalgam R₀)) (ha : W ≤ U R₀ a) (hz : W ≤ U R₀ z)
    (hk : U R₀ a ⊓ centralizer (Ltilde R₀ a : Set (FreeAmalgam R₀)) =
      U R₀ z ⊓ centralizer (Ltilde R₀ z : Set (FreeAmalgam R₀))) :
    ∃ e : (Ea.projection.comp (inclusion ha)).range ≃*
        (Ez.projection.comp (inclusion hz)).range,
      ∀ w, e ((Ea.projection.comp (inclusion ha)).rangeRestrict w) =
        (Ez.projection.comp (inclusion hz)).rangeRestrict w := by
  apply range_equiv_of_kernel_eq
  ext w
  have hmem (u : U R₀ a) : Ea.projection u = 1 ↔
      u.val ∈ U R₀ a ⊓ centralizer (Ltilde R₀ a : Set (FreeAmalgam R₀)) := by
    rw [←Ea.projection_kernel]
    constructor
    · intro hu
      exact ⟨u,hu,rfl⟩
    · rintro ⟨v,hv,hvu⟩
      have he : v = u := Subtype.ext hvu
      rwa [he] at hv
  have hmem' (u : U R₀ z) : Ez.projection u = 1 ↔
      u.val ∈ U R₀ z ⊓ centralizer (Ltilde R₀ z : Set (FreeAmalgam R₀)) := by
    rw [←Ez.projection_kernel]
    constructor
    · intro hu
      exact ⟨u,hu,rfl⟩
    · rintro ⟨v,hv,hvu⟩
      have he : v = u := Subtype.ext hvu
      rwa [he] at hv
  change Ea.projection (inclusion ha w) = 1 ↔ Ez.projection (inclusion hz w) = 1
  rw [hmem,hmem',hk]
  rfl

include D S m in
/-- The source comparison identifies both images of the original critical
commutator pointwise. The isomorphism is induced by the same group element,
not selected from an order equality. -/
theorem source_critical_commutator_projection_equiv
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (Ea : VertexAction R a ((K).map (QuotientGroup.mk' (pCore 2 H))))
    (Ez : VertexAction R z ((K).map (QuotientGroup.mk' (pCore 2 H)))) :
    ∃ ha : ⁅U R a,U R z⁆ ≤ U R a, ∃ hz : ⁅U R a,U R z⁆ ≤ U R z,
    ∃ e : (Ea.projection.comp (inclusion ha)).range ≃*
        (Ez.projection.comp (inclusion hz)).range,
      ∀ w, e ((Ea.projection.comp (inclusion ha)).rangeRestrict w) =
        (Ez.projection.comp (inclusion hz)).rangeRestrict w := by
  have hC := (source_critical_geometry D S m hescape).2
  have hba : 0 < criticalDistance R a (geometry.exists_critical a path.start_color) := by
    rw [geometry.distance_constant a path.start_color]
    exact hb
  have hrev := critical_reverse R geometry hC a path.start_color hba z path.end_color path.critical
  have ha : ⁅U R a,U R z⁆ ≤ U R a :=
    le_normalizer_iff_commutator_le_left.mp ((U_le_Z z).trans
      ((Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color) hrev.1.le).trans
        (U_normalized a)))
  have hz : ⁅U R a,U R z⁆ ≤ U R z :=
    le_normalizer_iff_commutator_le_right.mp ((U_le_Z a).trans
      ((Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le).trans
        (U_normalized z)))
  exact ⟨ha,hz,Ea.common_projection_equiv Ez _ ha hz
    (source_critical_kernels_eq D S m hescape path hb).1⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS
