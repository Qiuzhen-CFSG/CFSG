module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.Replacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.AmbientLayer
public import Theory.Frattini.Intersection

/-!
# The literal natural cover on the characteristic replacement

The original input supplies the natural quotient of the replacement omega
layer. Transport it to the actual holomorph graph, retaining the fixed kernel,
the full semilinear action and the original field degree. No odd-index witness
for the replacement radical is needed.

Source: MS93 (3.2)--(3.3), pp.863--867, and the replacement in Section 7,
pp.932--933. These are inputs to the distance-two argument, not its whole-core
or field-four conclusions.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open SymplecticConjugatePair.Ambient
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Positive even geometry is also available in the replacement overgroup. -/
theorem replacement_positive_even_geometry :
    ∃ g : Geometry d.radical, 0 < g.b d.radical ∧ Even (g.b d.radical) :=
  exists_positive_even_geometry d.radical (replacement_isPGroup h d)
    (replacement_ne_bot h d) (replacement_characteristic h d)
    (replacement_core_le h d) (replacement_selfCentralizing h d)
    (replacement_omegaOrbit_centralizer h d)

/-- The original omega orbit and full central omega layer have the same
literal commutator with (K.subgroupOf d.overgroup); no fully moved or field-four premise is needed. -/
theorem replacement_initialCore_eq :
    ⁅omegaOrbit d.radical,(K.subgroupOf d.overgroup)⁆ = ⁅omegaCenterIn (pCore 2 d.overgroup),(K.subgroupOf d.overgroup)⁆ := by
  let C := (K.subgroupOf d.overgroup).map (QuotientGroup.mk' (pCore 2 d.overgroup))
  obtain ⟨_,hC,hs,hq,_⟩ := (replacement_component_image_structure h d)
  let := hC
  let := hs
  let := hq
  let : IsElementaryAbelian 2 (omegaOrbit d.radical) :=
    omegaOrbit_elementary d.radical (replacement_core_le h d) (replacement_selfCentralizing h d)
  have hne : C ≠ ⊥ := by
    intro hz
    have hc := (replacement_component_image_card h d)
    have hlo := card_symplectic_ge F h.field_card h.nonbinary
    change Nat.card C = _ at hc
    rw [hz,card_bot] at hc
    omega
  exact NormalElementaryQuotient.commutator_eq_of_irrPlus (omegaOrbit d.radical)
    (omegaCenterIn (pCore 2 d.overgroup))
    (omegaOrbit_le_centralOmega d.radical (replacement_core_le h d) (replacement_selfCentralizing h d))
    (QuotientGroup.mk' (pCore 2 d.overgroup)) (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (replacement_omegaOrbit_centralizer h d).symm)
    ((QuotientGroup.ker_mk' _).trans (replacement_centralOmega_centralizer h d).symm)
    (K.subgroupOf d.overgroup) C rfl hne (replacement_centralOmega_moved_natural h d).1

/-- The actual replacement component in its two-core quotient. -/
@[expose] noncomputable def replacementComponent :
    Subgroup (d.overgroup ⧸ pCore 2 d.overgroup) :=
  (K.subgroupOf d.overgroup).map (QuotientGroup.mk' (pCore 2 d.overgroup))

theorem replacementComponent_normal : (replacementComponent d).Normal :=
  (replacement_component_image_structure h d).2.1

/-- The literal replacement omega-layer representation with its exact kernel. -/
@[expose] noncomputable def replacementRepresentation :=
  NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) (QuotientGroup.mk' (pCore 2 d.overgroup))
    (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (replacement_centralOmega_centralizer h d).symm)

/-- The shared moved/fixed section used by all replacement graph transports. -/
@[expose] noncomputable def replacementMovedSection :=
  letI := replacementComponent_normal h d
  MovedSection.ofNormal (replacementRepresentation h d) (replacementComponent d)

/-- The original moved/fixed projection is a cover for the actual natural
symplectic derived action, retaining the field degree of the input marking. -/
theorem replacement_centralOmega_initial_cover :
    let C := replacementComponent d
    let s := replacementMovedSection h d
    ∃ E : BinaryField, E.degree = n ∧
      ∃ e : ActionEquiv (s.action.comp C.subtype) (binaryNatural (K := E.Carrier)),
        IsCover (MovedSection.coverProjection s e) := by
  have hnat : IsIrrPlus (replacementRepresentation h d) (replacementComponent d)
      (subspaceCommutator (replacementRepresentation h d) ⊤ (replacementComponent d)) ∧
      ∃ E : BinaryField, E.degree = n ∧ Nonempty
        (ActionEquiv ((replacementMovedSection h d).action.comp (replacementComponent d).subtype)
          (binarySymplectic E)) := replacement_centralOmega_moved_natural h d
  obtain ⟨hi,E,hdegree,⟨e⟩⟩ := hnat
  let C := (K.subgroupOf d.overgroup).map (QuotientGroup.mk' (pCore 2 d.overgroup))
  let : C.Normal := (replacement_component_image_structure h d).2.1
  let s := replacementMovedSection h d
  have hlarge : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hdegree]
    exact lt_of_lt_of_le (by decide : 2 < 2^2)
      (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let e' : ActionEquiv (s.action.comp C.subtype) (binaryNatural (K := E.Carrier)) :=
    Sp4Four.derivedNaturalActionEquiv hlarge (s.action.comp C.subtype) e
  exact ⟨E,hdegree,e',MovedSection.coverProjection_isCover s hi e'⟩

section Covers
variable {M J W : Type*} [Group M] [Group J] [AddCommGroup W] [Module (ZMod 2) W]
variable {ρ : Representation (ZMod 2) J W} {C : Subgroup J}

/-- A literal cover transported to one original-color replacement vertex. -/
structure VertexCover (T : Subgroup M) (s : MovedSection ρ C) (n : ℕ) (a : Vertex T) where
  field : BinaryField
  degree : field.degree = n
  equiv : ActionEquiv (s.action.comp C.subtype)
    (binaryNatural (K := field.Carrier))
  cover : IsCover (MovedSection.coverProjection s equiv)
  embedding : Multiplicative s.space.toSubmodule →* FreeAmalgam T
  injective : Function.Injective embedding
  range_eq : embedding.range = U T a
  actor : Ltilde T a →* commutator (Matrix.symplecticGroup (Fin 2) field.Carrier)
  onto : Function.Surjective actor
  conjugation : ∀ (k : Ltilde T a) (v : s.space.toSubmodule),
    embedding (Multiplicative.ofAdd
      (MovedSection.coverAction s equiv (actor k) v)) =
      (k : FreeAmalgam T) * embedding (Multiplicative.ofAdd v) *
        (k : FreeAmalgam T)⁻¹
  kernel : ∀ v : s.space.toSubmodule,
    MovedSection.coverProjection s equiv v = 0 ↔
      embedding (Multiplicative.ofAdd v) ∈ centralizer (Ltilde T a : Set (FreeAmalgam T))

/-- The full quotient action on the same natural cover at a vertex. -/
structure AmbientVertexCover (T : Subgroup M) (s : MovedSection ρ C) (n : ℕ) (a : Vertex T) where
  field : BinaryField
  degree : field.degree = n
  equiv : ActionEquiv (s.action.comp C.subtype)
    (binaryNatural (K := field.Carrier))
  cover : IsCover (MovedSection.coverProjection s equiv)
  embedding : Multiplicative s.space.toSubmodule →* FreeAmalgam T
  injective : Function.Injective embedding
  range_eq : embedding.range = U T a
  quotient : stabilizer T a →* (J)
  onto : Function.Surjective quotient
  kernel_Q : quotient.ker.map (stabilizer T a).subtype = Q T a
  kernel_C : quotient.ker.map (stabilizer T a).subtype = BinaryMS.MS93.C T a
  component : ((Ltilde T a).subgroupOf (stabilizer T a)).map quotient =
    C
  faithful : Function.Injective (MovedSection.ambientAction s equiv)
  semilinear : ∀ g : J, ∃ σ : field.Carrier ≃+* field.Carrier,
    ∀ c v, MovedSection.ambientAction s equiv g (c • v) =
      σ c • MovedSection.ambientAction s equiv g v
  conjugation : ∀ (g : stabilizer T a) (v : s.space.toSubmodule),
    embedding (Multiplicative.ofAdd (s.space.toRepresentation (quotient g) v)) =
      (g : FreeAmalgam T) * embedding (Multiplicative.ofAdd v) *
        (g : FreeAmalgam T)⁻¹
  projection : ∀ (g : stabilizer T a) (v : s.space.toSubmodule),
    MovedSection.coverProjection s equiv
        (s.space.toRepresentation (quotient g) v) =
      MovedSection.ambientAction s equiv (quotient g)
        (MovedSection.coverProjection s equiv v)
  kernel : ∀ v : s.space.toSubmodule,
    MovedSection.coverProjection s equiv v = 0 ↔
      embedding (Multiplicative.ofAdd v) ∈ centralizer (Ltilde T a : Set (FreeAmalgam T))

end Covers

/-- Construct the actual cover and its residual conjugation action. -/
theorem replacement_initial_cover_at_vertex
    {a : Vertex d.radical} (ha : color d.radical a = false) : Nonempty (VertexCover d.radical (replacementMovedSection h d) n a) := by
  let C := (K.subgroupOf d.overgroup).map (QuotientGroup.mk' (pCore 2 d.overgroup))
  let : C.Normal := (replacement_component_image_structure h d).2.1
  let : (replacementComponent d).Normal := replacementComponent_normal h d
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let hq := QuotientGroup.mk'_surjective (pCore 2 d.overgroup)
  let hk := (QuotientGroup.ker_mk' _).trans (replacement_centralOmega_centralizer h d).symm
  let s := replacementMovedSection h d
  obtain ⟨E,hE,e,he⟩ := (replacement_centralOmega_initial_cover h d)
  obtain ⟨i,hi,_,hiL,hiU⟩ := Sp4Four.LocalPackage.vertex_coordinates d.radical ha
  rw [(replacement_residual h d)] at hiL
  have hU : (⁅omegaOrbit d.radical,(K.subgroupOf d.overgroup)⁆).map i = U d.radical a := by
    simpa only [Sp4Four.LocalPackage.initialLayer,(replacement_residual h d)] using hiU
  let j := i.comp (ElementaryMovedCover.embedding (omegaCenterIn (pCore 2 d.overgroup)) (K.subgroupOf d.overgroup) q hq hk)
  have hjU : j.range = U d.radical a := by
    dsimp only [j]
    rw [MonoidHom.range_comp,ElementaryMovedCover.embedding_range,←(replacement_initialCore_eq h d)]
    exact hU
  obtain ⟨f,hf,hact,hker⟩ := ElementaryMovedCover.exists_conjugationActor
    (omegaCenterIn (pCore 2 d.overgroup)) (K.subgroupOf d.overgroup) q hq hk i hi
    (Ltilde d.radical a) hiL e
  refine ⟨⟨E,hE,e,he,j,hi.comp (ElementaryMovedCover.embedding_injective _ _ _ _ _),hjU,
    f,hf,hact,hker⟩⟩

/-- Construct the whole vertex quotient action, retaining its two-core kernel. -/
theorem replacement_ambient_initial_cover_at_vertex
    {a : Vertex d.radical} (ha : color d.radical a = false) : Nonempty (AmbientVertexCover d.radical (replacementMovedSection h d) n a) := by
  let C := (K.subgroupOf d.overgroup).map (QuotientGroup.mk' (pCore 2 d.overgroup))
  let : C.Normal := (replacement_component_image_structure h d).2.1
  let : (replacementComponent d).Normal := replacementComponent_normal h d
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let hq := QuotientGroup.mk'_surjective (pCore 2 d.overgroup)
  let hk := (QuotientGroup.ker_mk' _).trans (replacement_centralOmega_centralizer h d).symm
  let s := replacementMovedSection h d
  obtain ⟨E,hE,e,he⟩ := (replacement_centralOmega_initial_cover h d)
  obtain ⟨i,hi,hir,hiK,hiU,hiQ⟩ :=
    Sp4Four.SourceComparison.vertex_coordinates_with_kernel d.radical
      (replacement_isPGroup h d) (replacement_core_le h d) ha
  rw [(replacement_residual h d)] at hiK
  have hU : (⁅omegaOrbit d.radical,(K.subgroupOf d.overgroup)⁆).map i = U d.radical a := by
    simpa only [Sp4Four.LocalPackage.initialLayer,(replacement_residual h d)] using hiU
  let j := i.comp (ElementaryMovedCover.embedding (omegaCenterIn (pCore 2 d.overgroup)) (K.subgroupOf d.overgroup) q hq hk)
  have hjU : j.range = U d.radical a := by
    dsimp only [j]
    rw [MonoidHom.range_comp,ElementaryMovedCover.embedding_range,←(replacement_initialCore_eq h d)]
    exact hU
  let κ := ElementaryMovedCover.embeddedQuotient q i hi (stabilizer d.radical a) hir
  have hkQ : κ.ker.map (stabilizer d.radical a).subtype = Q d.radical a := by
    rw [ElementaryMovedCover.embeddedQuotient_kernel,QuotientGroup.ker_mk']
    exact hiQ
  refine ⟨⟨E,hE,e,he,j,hi.comp (ElementaryMovedCover.embedding_injective _ _ _ _ _),hjU,
    κ,ElementaryMovedCover.embeddedQuotient_surjective q i hi _ hir hq,hkQ,?_,?_,
    MovedSection.ambientAction_faithful s e binaryNatural_injective
      (replacement_component_image_structure h d).2.2.2.2,?_,?_,?_,?_⟩⟩
  · exact hkQ.trans (MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) a ha).symm
  · rw [←hiK]
    exact ElementaryMovedCover.embeddedQuotient_subgroup q i hi _ hir (K.subgroupOf d.overgroup)
  · have hcard : 2 < Nat.card E.Carrier := by
      rw [E.card_eq,hE]
      exact lt_of_lt_of_le (by decide : 2 < 2^2)
        (Nat.pow_le_pow_right (by decide) h.nonbinary)
    let d : commutator (Matrix.symplecticGroup (Fin 2) E.Carrier) ≃*
        Matrix.symplecticGroup (Fin 2) E.Carrier :=
      (MulEquiv.subgroupCongr
        (Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hcard)).trans
        Subgroup.topEquiv
    intro g
    exact SymplecticNaturalNormalizer.exists_field_twist
      ⟨linearAction (MovedSection.ambientAction s e) g,
        SymplecticNaturalNormalizer.operator_mem_naturalNormalizer C hcard
          (e.groupEquiv.trans d) (MovedSection.ambientAction s e)
          (fun b v => MovedSection.ambientAction_component s e b v) g⟩
  · exact ElementaryMovedCover.embedded_ambient_conjugate (omegaCenterIn (pCore 2 d.overgroup)) (K.subgroupOf d.overgroup) q hq hk i hi _ hir
  · intro g v
    exact MovedSection.coverProjection_ambient s e (κ g) v
  · obtain ⟨f,hf,hact,hker⟩ := ElementaryMovedCover.exists_conjugationActor
      (omegaCenterIn (pCore 2 d.overgroup)) (K.subgroupOf d.overgroup) q hq hk i hi (Ltilde d.radical a) hiK e
    exact hker

/-- The literal moving subgroup is elementary; this is derived from the
positive critical geometry of the input rather than supplied to its cover. -/
theorem replacement_vertex_moving_elementary {a : Vertex d.radical} (ha : color d.radical a = false) :
    IsElementaryAbelian 2 (U d.radical a) := by
  obtain ⟨g,hpos,_⟩ := (replacement_positive_even_geometry h d)
  let : IsElementaryAbelian 2 (X d.radical a) := omegaCenter_elementary (Q d.radical a)
  let : IsElementaryAbelian 2 (Z d.radical a) := IsElementaryAbelian.of_le
    (g.omega_bound a ha (by rwa [g.distance_constant a ha]))
  exact IsElementaryAbelian.of_le (DistanceEight.U_le_Z d.radical a)

/-- The initial cover realized on the literal moving subgroup, with its
actual residual actor and fixed kernel, for every nonbinary degree. -/
theorem replacement_initial_subgroup_cover_at_vertex
    {a : Vertex d.radical} (ha : color d.radical a = false) :
    letI := (replacement_vertex_moving_elementary h d) ha
    ∃ E : BinaryField, E.degree = n ∧
      ∃ σ : Representation (ZMod 2)
          (commutator (Matrix.symplecticGroup (Fin 2) E.Carrier)) (Additive (U d.radical a)),
      ∃ p : σ.IntertwiningMap (binaryNatural (K := E.Carrier)), IsCover p ∧
      ∃ f : Ltilde d.radical a →* commutator (Matrix.symplecticGroup (Fin 2) E.Carrier),
        Function.Surjective f ∧
        (∀ (k : Ltilde d.radical a) (u : U d.radical a),
          ((σ (f k) (Additive.ofMul u)).toMul : FreeAmalgam d.radical) =
            (k : FreeAmalgam d.radical) * u * (k : FreeAmalgam d.radical)⁻¹) ∧
        p.toLinearMap.ker.toAddSubgroup.toSubgroup'.map (U d.radical a).subtype =
          U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) := by
  let := (replacement_vertex_moving_elementary h d) ha
  obtain ⟨⟨E,hE,e,he,j,hj,hjU,f,hf,hact,hker⟩⟩ := (replacement_initial_cover_at_vertex h d) ha
  obtain ⟨σ,p,hp,hact',hker'⟩ := exists_subgroup_cover _ _ _ he
    (U d.radical a) (Ltilde d.radical a) j hj hjU f hact hker
  exact ⟨E,hE,σ,p,hp,f,hf,hact',hker'⟩

omit [Finite F] [CharP F 2] in
/-- The graph Frattini bound is exactly the bound needed on the intrinsic
replacement core, through its original injective vertex map. -/
theorem replacement_frattini_small_of_graph
    (hsmall : core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map (Q d.radical (alpha d.radical)).subtype ⊔
        X d.radical (alpha d.radical)) :
    ⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆ ≤
      (frattini (pCore 2 d.overgroup)).map (pCore 2 d.overgroup).subtype ⊔
        omegaCenterIn (pCore 2 d.overgroup) := by
  rw [core_alpha d.radical (replacement_isPGroup h d) (replacement_core_le h d)
      (replacement_residual h d), X,
    Q_alpha d.radical (replacement_isPGroup h d) (replacement_core_le h d),
    omegaCenter_map _ _ (embedM_injective d.radical),
    frattini_image_map _ _ (embedM_injective d.radical),←Subgroup.map_sup] at hsmall
  exact (map_le_map_iff_of_injective (embedM_injective d.radical)).mp hsmall

/-- Apply a whole graph-core bound to the actual original component, keeping
its natural model at the original degree. -/
theorem short_and_natural_of_replacement_graph_frattini_small
    (hsmall : core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map (Q d.radical (alpha d.radical)).subtype ⊔
        X d.radical (alpha d.radical)) :
    IsShort K ∧ ∃ E : BinaryField, E.degree = n ∧
      IsLinearBlockModel K (binarySymplectic E) :=
  short_and_natural_of_replacement_frattini_small h d
    (replacement_frattini_small_of_graph h d hsmall)

/-- The degree-two whole-graph-core branch gives the original block. The
field restriction and graph bound remain the substantive distance-two goals. -/
theorem block_of_degree_two_replacement_graph_frattini_small (hn : n = 2)
    (hsmall : core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map (Q d.radical (alpha d.radical)).subtype ⊔
        X d.radical (alpha d.radical)) : IsSp4FourBlock K :=
  block_of_degree_two_replacement_frattini_small h d hn
    (replacement_frattini_small_of_graph h d hsmall)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
