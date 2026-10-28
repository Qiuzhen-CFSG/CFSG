module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear.G2Initial
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.G2.Source

/-!
# Excluding the actual G₂(4) point pair

The point-pair omega action supplies a natural cover at every original-color
vertex of its MS amalgam. The cover's kernel criterion identifies the two
embedded critical kernels. The proved reciprocal root-displacement obstruction
then forces the four-element coefficient field to be binary, a contradiction.

Every action, quotient and kernel is transported from J=LR₁. The final theorem
applies the exclusion to RadicalAssembly's literal alternative. No full-Sylow
assumption on R₁, fixed-factor centrality, or classification callback is used.
Source: Aschbacher--Smith 11.1.5, p.765; MS93 (3.2), pp.865--866.
The reused root calculations use the attributed octonion model (LICENSES/ATLAS.txt).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology
open scoped IsMulCommutative Pointwise commutatorElement
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear
open ChapterC ChapterC.MSCentralOrbit ChapterC.RankTwo.NonbinarySymplectic
open Stellmacher.PushingUp.AmalgamGraph BinaryMS.MS93
open SylowNormalizer.G2MS
open ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

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

variable {H : Type*} [Group H] [Finite H] {K R : Subgroup H}
  {F₀ : BinaryField} (h : G2Input K R F₀)
include h

/-- The point-pair action and its offender kernel live at each original vertex. -/
theorem G2Input.four_vertex_kernel_action
    (hfour : F₀.degree = 2)
    {a : Vertex R} (ha : color R a = false) :
    ∃ E : VertexAction R a ((K).map (QuotientGroup.mk' (pCore 2 H))), HasOffenderKernel E := by
  obtain ⟨hk,hn,hmodule⟩ := h.initial_module
  let := hn
  let q := QuotientGroup.mk' (pCore 2 H)
  let hq := QuotientGroup.mk'_surjective (pCore 2 H)
  let X := omegaCenterIn (pCore 2 H)
  let B := (K).map q
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation X q hq hk) B
  obtain ⟨hiModule,F,hF,⟨e⟩⟩ := hmodule
  have he := MovedSection.coverProjection_isCover s hiModule e
  have hFtwo : F.degree = 2 := hF.trans hfour
  have hp : IsPGroup 2 R :=
    h.radical.isPGroup
  have hQR : pCore 2 H ≤ R :=
    h.radical.twoCore_le
  obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ :=
    ChapterC.RankTwo.Sp4Four.SourceComparison.vertex_coordinates_with_kernel R hp hQR ha
  rw [h.residual_eq] at hiL
  have hu : (⁅X,K⁆).map i = U R a := by
    rw [←h.initial_commutator]
    simpa only [ChapterC.RankTwo.Sp4Four.LocalPackage.initialLayer,h.residual_eq] using hiU
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
      (h.omegaOrbit_centralizer) a ha).symm
  have hkL : ((Ltilde R a).subgroupOf (stabilizer R a)).map κ = B := by
    rw [←hiL]
    exact ElementaryMovedCover.embeddedQuotient_subgroup q i hi _ hir _
  have hfaith : Function.Injective (MovedSection.ambientAction s e) := by
    apply MovedSection.ambientAction_faithful s e _ ((h.image_structure).2.2.2.2)
    intro g h heq
    apply Atlas.G2.Natural.action_injective F.Carrier
    exact LinearMap.ext (fun v => LinearMap.congr_fun heq v)
  have hconj : ∀ (g : stabilizer R a) (v : s.space.toSubmodule),
      j (Multiplicative.ofAdd (s.space.toRepresentation (κ g) v)) =
        (g : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (g : FreeAmalgam R)⁻¹ :=
    ElementaryMovedCover.embedded_ambient_conjugate _ _ _ _ _ i hi _ hir
  obtain ⟨actor,hactor,hact,hker⟩ := ElementaryMovedCover.exists_conjugationActor
    X K q hq hk i hi (Ltilde R a) hiL e
  exact vertexKernelAction_of_cover F hFtwo s e he j hj hjU κ
    (ElementaryMovedCover.embeddedQuotient_surjective q i hi _ hir hq)
    hkQ hkC hkL hfaith hconj hker

/-- The genuine G₂(4) point MS row is impossible. -/
theorem G2Input.four_false (hfour : F₀.degree = 2) : False := by
  obtain ⟨⟨geometry,hpos,_⟩,hC⟩ := h.critical_geometry
  obtain ⟨a,ha⟩ := criticalPair_exists R (alpha R) (geometry.exists_critical _ rfl)
  let path := CriticalPath.ofPair (geometry := geometry) rfl ha
  obtain ⟨Ea,hEa⟩ := h.four_vertex_kernel_action hfour path.start_color
  obtain ⟨Ez,hEz⟩ := h.four_vertex_kernel_action hfour path.end_color
  have hk := (critical_kernels_eq path hpos hC Ea Ez hEa hEz).1
  exact critical_root_actions_incompatible path hpos hC Ea Ez hk

omit h

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction
    (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
  (f : InvariantFlag (.g2 m))
local notation "H" => (L ⊔ f.Ri 0 : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ f.Ri 0)
local notation "R" => Subgroup.subgroupOf (f.Ri 0) (L ⊔ f.Ri 0)


/-- The genuine G₂(4) point MS row is impossible. -/
theorem point_g2_four_false (hm : NonbinaryMSPair S.field L (f.Ri 0))
    (hfour : S.field.degree = 2) : False :=
  (point_g2_input D S m f hm).four_false hfour

/-- The original G₂(4) point radical has no normalizer escape. -/
theorem point_g2_four_normalizer_le (hfour : S.field.degree = 2) :
    normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G) := by
  by_contra he
  exact point_g2_four_false D S m f (point_msPair D S f he) hfour

/-- The actual radical alternative is unconditional in the G₂(4) branch. -/
theorem point_g2_four_radicalAlternative (hfour : S.field.degree = 2) :
    Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree := by
  exact Or.inl (point_g2_four_normalizer_le D S m f hfour)

/-- Both original 11.2.3 clauses in the field-four exceptional row, now with
its radical-alternative input proved on the actual point flag. -/
theorem point_g2_four_source_11_2_3 (hfour : S.field.degree = 2)
    {X : Subgroup G} (hX : IsCartan T L X) :
    (V ⊓ centralizer (L : Set G) = ⊥ →
      normalizer (f.Vi 0 : Set G) = centralizer (f.Vi 0 : Set G) ⊔
        (normalizer (L : Set G) ⊓ normalizer (f.Vi 0 : Set G))) ∧
    (centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G) →
      normalizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G)) :=
  chosen_g2_source_11_2_3 D S m f hX (point_g2_four_radicalAlternative D S m f hfour)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear
