module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.G2.MSGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.AmbientAction
public import Theory.Representation.G2NaturalFaithfulness
public import Theory.Representation.SymplecticFourOrthogonalCover.EmbeddedProjectionAction

/-!
# The actual G₂(4) action at each critical vertex

The central-omega moved cover is transported through the original vertex
embedding. Its projection onto the marked natural six-space is surjective,
with kernel exactly the centralizer of the vertex residual inside U. The
whole vertex quotient acts faithfully and retains both its original two-core
kernel and its centralizer kernel. No field compatibility between opposite
vertices is asserted here.

This constructs the actions used by MSCriticalActors. Source: MS93 (3.2),
pp.865--866, in the G₂ exclusion needed for Aschbacher--Smith 3.3.16 and 11.2.3.
The line-action owner retains the field comparison; final source assembly
remains with qt-d-1222-natural-normalizer-source.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology
open scoped IsMulCommutative Pointwise
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


/-- Natural coordinates for the literal full vertex quotient. Every map is
anchored to the original stabilizer and moving subgroup. -/
structure VertexAction {M J : Type*} [Group M] [Group J]
    (R₀ : Subgroup M) (a : Vertex R₀) (B : Subgroup J) where
  field : BinaryField
  degree : field.degree = 2
  component_normal : B.Normal
  componentEquiv : B ≃* Atlas.G2.Model field.Carrier
  action : Representation (ZMod 2) J (Atlas.G2.Natural.Space field.Carrier)
  component_apply : ∀ (b : B) v,
    action (b : J) v = Atlas.G2.Natural.action field.Carrier (componentEquiv b) v
  faithful : Function.Injective action
  quotient : stabilizer R₀ a →* J
  quotient_surjective : Function.Surjective quotient
  kernel_core : quotient.ker.map (stabilizer R₀ a).subtype = Q R₀ a
  kernel_centralizer : quotient.ker.map (stabilizer R₀ a).subtype = C R₀ a
  component_image : ((Ltilde R₀ a).subgroupOf (stabilizer R₀ a)).map quotient = B
  projection : U R₀ a →* Multiplicative (Atlas.G2.Natural.Space field.Carrier)
  projection_surjective : Function.Surjective projection
  projection_kernel : projection.ker.map (U R₀ a).subtype =
    U R₀ a ⊓ centralizer (Ltilde R₀ a : Set (FreeAmalgam R₀))
  conjugate : ∀ (g : stabilizer R₀ a) (u : U R₀ a),
    projection ⟨g.val*u.val*g.val⁻¹,
      (mem_normalizer_iff.mp (U_normalized a g.property) u.val).mp u.property⟩ =
        Multiplicative.ofAdd (action (quotient g) (projection u).toAdd)

private theorem vertexAction_of_cover
    {M J W : Type*} [Group M] [Group J] [AddCommGroup W] [Module (ZMod 2) W]
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
    Nonempty (VertexAction R₀ a B) := by
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
  refine ⟨⟨F,hF,inferInstance,e.groupEquiv,MovedSection.ambientAction s e,
    MovedSection.ambientAction_component s e,hf,κ,hκ,hkQ,hkC,hkL,π,hπ,?_,hact⟩⟩
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨u.property,(hπker u).mp hu⟩
  · rintro ⟨hx,hc⟩
    exact ⟨⟨x,hx⟩,(hπker ⟨x,hx⟩).mpr hc,rfl⟩

include D S m in
/-- The original G₂ escape constructs the faithful full vertex action on its
natural moving quotient, including all literal quotient and conjugation maps. -/
theorem source_vertex_action
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    {a : Vertex R} (ha : color R a = false) :
    Nonempty (VertexAction R a ((K).map (QuotientGroup.mk' (pCore 2 H)))) := by
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
  exact vertexAction_of_cover F hF s e he j hj hjU κ
    (ElementaryMovedCover.embeddedQuotient_surjective q i hi _ hir hq)
    hkQ hkC hkL hfaith hconj hker

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS
