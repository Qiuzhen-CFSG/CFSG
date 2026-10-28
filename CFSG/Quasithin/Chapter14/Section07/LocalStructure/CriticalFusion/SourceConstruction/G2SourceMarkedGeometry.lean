module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceGeometry
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.SubgroupPartitionCounting

/-!
# Marking the original G₂ geometry from source recognition

Natural/Weyl recognition supplies the full equivariant module identification.
The original flag gives the quotient orders, Sylow normalization, central
point, and the local commutator identity. These inputs construct the marked
point and line and all eight clauses of 14.7.55. No module identification,
marked point, line family or recognition datum is assumed by the assembled
`source_marked_geometry` theorem.

Normality is relative to the original H. The canonical comparison between
the internal H-quotient and the ambient U/V₁ quotient preserves every subgroup
image and its literal quotient map. In particular the marked point and line
are the original V₂/V₁ and V/V₁ on the same natural/Weyl geometry.

The earlier faithful action, generalized-Fitting identity, critical choice,
and F.9.18 implications remain explicit as in G2SourceRecognition. The four
precise numerical/offender inputs from B.4.6 remain with qt-b-04-g2; their
final discharge belongs to qt-d-14775-source. The critical-pair argument
14.7.60–62 and the exclusion remain separate obligations of this source branch.

Source: Aschbacher–Smith, 14.7.54–55, printed pp.1065–1066. The actual
natural and Weyl models retain the ATLAS attribution in LICENSES/ATLAS.txt.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
open G2Exclusion G2Exclusion.MarkedGeometry
open G2Exclusion.MarkedGeometry.LocalParabolics.ThreeOffenderOrbit
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) (HStar F.H) W}
  (c : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))

variable [IsMulCommutative V]

local instance internalSpanNormal : (F.U.subgroupOf F.H).Normal :=
  (normal_subgroupOf_iff_le_normalizer F.U_le_H).mpr
    (le_normalizer_conjugateSpanBy V F.H)

local instance internalPointNormal :
    ((F.Vi 1).subgroupOf F.H |>.subgroupOf (F.U.subgroupOf F.H)).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer
    (subgroupOf_mono F.H ((F.le_seed 1).trans (le_conjugateSpanBy V F.H)))).mpr
  intro a _
  apply mem_normalizer_iff.mpr
  intro b
  exact mem_normalizer_iff.mp a.property (b : G)

/-- The canonical internal-to-ambient quotient comparison. -/
def internalQuotientEquiv :
    let := c.kernel_normal
    ((F.U.subgroupOf F.H) ⧸ ((F.Vi 1).subgroupOf F.H).subgroupOf (F.U.subgroupOf F.H)) ≃*
      (F.U ⧸ (F.Vi 1).subgroupOf F.U) := by
  let := c.kernel_normal
  apply QuotientGroup.congr _ _ (subgroupOfEquivOfLe F.U_le_H)
  ext u
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact hv
  · intro hu
    exact ⟨(subgroupOfEquivOfLe F.U_le_H).symm u,hu,
      (subgroupOfEquivOfLe F.U_le_H).apply_symm_apply u⟩

/-- The same coordinates on the internal literal quotient in H. -/
def internalModuleEquiv (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W) :
    Multiplicative m.Space ≃*
      ((F.U.subgroupOf F.H) ⧸ ((F.Vi 1).subgroupOf F.H).subgroupOf (F.U.subgroupOf F.H)) := by
  let := c.kernel_normal
  exact (literalModuleEquiv c m E).trans (internalQuotientEquiv c).symm

omit [Finite G] in
private theorem internal_coordinates (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (u : F.U.subgroupOf F.H) :
    E (((internalModuleEquiv c m E).symm
      (QuotientGroup.mk' (((F.Vi 1).subgroupOf F.H).subgroupOf (F.U.subgroupOf F.H)) u)).toAdd) =
        (c.coordinates ((subgroupOfEquivOfLe F.U_le_H) u)).toAdd := by
  let := c.kernel_normal
  change E (((literalModuleEquiv c m E).symm (QuotientGroup.mk' _
    ((subgroupOfEquivOfLe F.U_le_H) u))).toAdd) = _
  exact literalModuleEquiv_coordinates c m E _

omit [Finite G] in
/-- The internal quotient marking preserves the actual conjugation in H. -/
theorem internalModuleEquiv_conjugation
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2))
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (he : ∀ a v, E (m.action (i a) v) = σ a (E v))
    (a : F.H) (u : F.U.subgroupOf F.H) :
    m.action (i (starMap F a))
      (((internalModuleEquiv c m E).symm (QuotientGroup.mk' _ u)).toAdd) =
      ((internalModuleEquiv c m E).symm (QuotientGroup.mk' _
        ⟨a * (u : F.H) * a⁻¹, (internalSpanNormal (F := F)).conj_mem u u.property a⟩)).toAdd := by
  apply E.injective
  rw [he,internal_coordinates,internal_coordinates]
  exact (c.equivariant a ((subgroupOfEquivOfLe F.U_le_H) u)).symm

omit [Finite G] in
/-- The order of an internal quotient image is the original relative index. -/
theorem internal_image_card (B : Subgroup G) (hB : B ≤ F.U) :
    Nat.card (((B.subgroupOf F.H).subgroupOf (F.U.subgroupOf F.H)).map
      (QuotientGroup.mk' (((F.Vi 1).subgroupOf F.H).subgroupOf (F.U.subgroupOf F.H)))) =
        (F.Vi 1).relIndex B := by
  rw [← relIndex_ker,QuotientGroup.ker_mk']
  change (((F.Vi 1).subgroupOf F.H).comap (F.U.subgroupOf F.H).subtype).relIndex _ = _
  rw [relIndex_comap,map_subgroupOf_eq_of_le (subgroupOf_mono F.H hB)]
  change ((F.Vi 1).comap F.H.subtype).relIndex _ = _
  rw [relIndex_comap,map_subgroupOf_eq_of_le (hB.trans F.U_le_H)]

/-- The internal commutator identity used to mark the Weyl line. -/
theorem internal_seed_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) :
    ⁅V.subgroupOf F.H,(F.Li L 1).subgroupOf F.H⁆ ⊔ (F.Vi 1).subgroupOf F.H =
      V.subgroupOf F.H := by
  have hV : V ≤ F.H := (le_conjugateSpanBy V F.H).trans F.U_le_H
  have hL : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  apply map_injective (f := F.H.subtype) F.H.subtype_injective
  rw [Subgroup.map_sup,map_commutator,map_subgroupOf_eq_of_le hV,
    map_subgroupOf_eq_of_le hL,map_subgroupOf_eq_of_le ((F.le_seed 1).trans hV),
    ← seed_commutator h F,sup_eq_left.mpr (F.le_seed 1)]

/-- The marked action is the pullback of the actual full model action. -/
@[instance_reducible] def internalModuleAction (i : HStar F.H →* Atlas.G2.Model (ZMod 2))
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W) :
    MulDistribMulAction (HStar F.H)
      ((F.U.subgroupOf F.H) ⧸ ((F.Vi 1).subgroupOf F.H).subgroupOf (F.U.subgroupOf F.H)) := by
  let := MarkedPencil.Assembly.modelQuotientAction m.action (internalModuleEquiv c m E)
  exact MulDistribMulAction.compHom _ i

/-- All eight marked-geometry clauses follow from recognition and the original
flag; the source line and point are constructed rather than postulated. -/
theorem marked_geometry_of_recognition
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2)) (hi : Function.Injective i)
    (hJ : commutator (Atlas.G2.Model (ZMod 2)) ≤ i.range)
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (he : ∀ a v, E (m.action (i a) v) = σ a (E v))
    (hRank : ∀ A : Subgroup (Atlas.G2.Model (ZMod 2)),
      A ≤ commutator (Atlas.G2.Model (ZMod 2)) → IsElementaryTwo A → rank A ≤ 2)
    (hOne : ∀ A : Subgroup (Atlas.G2.Model (ZMod 2)), IsElementaryTwo A →
      rank A = 1 → 2 ≤ fixedCodim m.action A)
    (hTwo : ∀ A : Subgroup (Atlas.G2.Model (ZMod 2)),
      A ≤ commutator (Atlas.G2.Model (ZMod 2)) → IsElementaryTwo A →
      rank A = 2 → 3 ≤ fixedCodim m.action A)
    (hB46 : ∀ B : Subgroup (Atlas.G2.Model (ZMod 2)), IsBestOffender m.action B ↔
      ∃ g : Atlas.G2.Model (ZMod 2), Atlas.G2.BinaryCore.elementary.map
        (MulAut.conj g).toMonoidHom = B) :
    letI := internalModuleAction c i m E
    ∃ p : Atlas.G2.SingularPoints (ZMod 2),
      MarkedPencil.Assembly.SourceConclusions (F.U.subgroupOf F.H)
        ((F.Vi 1).subgroupOf F.H) ((F.Vi 2).subgroupOf F.H) (V.subgroupOf F.H)
        m.action m.singularMap (internalModuleEquiv c m E) (starMap F) i
        (T.subtype (F.invariant 1)) p ∧
      Assembly.HexagonConclusions (transportGeometry m.singularMap.geometry
        (internalModuleEquiv c m E)) := by
  let := internalModuleAction c i m E
  let := h.chosen.elementary
  let : IsElementaryAbelian 2 (F.Vi 1) :=
    IsElementaryAbelian.of_injective (inclusion (F.le_seed 1)) (inclusion_injective _)
  have hVH : V ≤ F.H := (le_conjugateSpanBy V F.H).trans F.U_le_H
  let := IsElementaryAbelian.subgroupOf (p := 2) ((F.le_seed 1).trans hVH)
  have hk : IsPGroup 2 (i.comp (starMap F)).ker := by
    have hh : (i.comp (starMap F)).ker = pCore 2 F.H := by
      ext a
      change i (starMap F a) = 1 ↔ a ∈ pCore 2 F.H
      rw [← i.map_one,hi.eq_iff]
      exact QuotientGroup.eq_one_iff a
    rw [hh]
    exact pCore_isPGroup
  have hcentral : (⊤ : Subgroup F.H) ≤ centralizer (((F.Vi 1).subgroupOf F.H) : Set F.H) := by
    intro a _ b hb
    exact Subtype.ext ((normalizer_le_centralizer_of_card_two _
      (by simpa using F.card 1 (by decide)) a.property) b hb)
  have hcardV : Nat.card (((V.subgroupOf F.H).subgroupOf (F.U.subgroupOf F.H)).map
      (QuotientGroup.mk' (((F.Vi 1).subgroupOf F.H).subgroupOf (F.U.subgroupOf F.H)))) = 4 := by
    rw [internal_image_card V (le_conjugateSpanBy V F.H)]
    have hc := relIndex_mul_card_of_le (F.le_seed 1)
    have hv : Nat.card V = 8 := by
      calc Nat.card V = Nat.card (F.Vi 3) := congrArg (fun B : Subgroup G => Nat.card B) F.last.symm
           _ = 8 := F.card 3 (by decide)
    rw [F.card 1 (by decide),hv] at hc
    omega
  have hcardV₂ : Nat.card ((((F.Vi 2).subgroupOf F.H).subgroupOf (F.U.subgroupOf F.H)).map
      (QuotientGroup.mk' (((F.Vi 1).subgroupOf F.H).subgroupOf (F.U.subgroupOf F.H)))) = 2 := by
    rw [internal_image_card (F.Vi 2) ((F.le_seed 2).trans (le_conjugateSpanBy V F.H))]
    have hc := relIndex_mul_card_of_le (F.monotone (by decide : 1 ≤ 2))
    rw [F.card 1 (by decide),F.card 2 (by decide)] at hc
    omega
  have hn (B : Subgroup G) (hB : (T : Subgroup G) ≤ normalizer (B : Set G)) :
      ((T.subtype (show (T : Subgroup G) ≤ F.H from F.invariant 1)) : Subgroup F.H) ≤
        normalizer (B.subgroupOf F.H : Set F.H) := by
    intro a ha
    apply mem_normalizer_iff.mpr
    intro b
    exact mem_normalizer_iff.mp (hB ha) (b : G)
  apply Assembly.source_marked_geometry m (F.U.subgroupOf F.H) ((F.Vi 1).subgroupOf F.H)
    ((F.Vi 2).subgroupOf F.H) (V.subgroupOf F.H) ((F.Li L 1).subgroupOf F.H)
    (subgroupOf_mono F.H (F.monotone (by decide : 1 ≤ 2)))
    (subgroupOf_mono F.H (F.le_seed 2))
    (subgroupOf_mono F.H (le_conjugateSpanBy V F.H))
    (internal_seed_commutator h) hcentral (starMap F) (QuotientGroup.mk'_surjective _)
    i hi hJ hk (internalModuleEquiv c m E)
    (fun a w => ?_) (internalModuleEquiv_conjugation c i m E he)
    hcardV hcardV₂ (T.subtype (F.invariant 1))
    (hn V (F.last ▸ F.invariant 3)) (hn (F.Vi 2) (F.invariant 2)) hRank hOne hTwo hB46
  change (internalModuleEquiv c m E) (Multiplicative.ofAdd
    (m.action (i a) (((internalModuleEquiv c m E).symm
      ((internalModuleEquiv c m E) (Multiplicative.ofAdd w))).toAdd))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

omit [Finite G] in
/-- Every marked subgroup uses the original quotient map after comparison. -/
theorem internalQuotientEquiv_image (B : Subgroup G) :
    letI := c.kernel_normal
    ((((B.subgroupOf F.H).subgroupOf (F.U.subgroupOf F.H)).map
      (QuotientGroup.mk' (((F.Vi 1).subgroupOf F.H).subgroupOf (F.U.subgroupOf F.H)))).map
      (internalQuotientEquiv c).toMonoidHom) =
    (B.subgroupOf F.U).map (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.U)) := by
  let := c.kernel_normal
  let e := subgroupOfEquivOfLe F.U_le_H
  ext q
  constructor
  · rintro ⟨_,⟨u,hu,rfl⟩,rfl⟩
    exact ⟨e u,hu,rfl⟩
  · rintro ⟨u,hu,rfl⟩
    refine ⟨QuotientGroup.mk' _ (e.symm u),⟨e.symm u,hu,rfl⟩,?_⟩
    change QuotientGroup.mk' _ (e (e.symm u)) = _
    rw [e.apply_symm_apply]

omit [Finite G] in
private theorem internal_model_image (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (B : Subgroup (Multiplicative m.Space)) :
    letI := c.kernel_normal
    (B.map (internalModuleEquiv c m E).toMonoidHom).map (internalQuotientEquiv c).toMonoidHom =
      B.map (literalModuleEquiv c m E).toMonoidHom := by
  let := c.kernel_normal
  rw [map_map]
  congr 1

omit [Finite G] in
/-- The internally constructed point and line are exactly the original
ambient quotient images of V₂ and V. -/
theorem original_marked_points
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (p : Atlas.G2.SingularPoints (ZMod 2))
    (hp : (transportGeometry m.singularMap.geometry (internalModuleEquiv c m E)).point p =
      (((F.Vi 2).subgroupOf F.H).subgroupOf (F.U.subgroupOf F.H)).map
        (QuotientGroup.mk' (((F.Vi 1).subgroupOf F.H).subgroupOf (F.U.subgroupOf F.H))))
    (hl : ∃ l : Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.ZeroProductLine (ZMod 2),
      ((V.subgroupOf F.H).subgroupOf (F.U.subgroupOf F.H)).map
        (QuotientGroup.mk' (((F.Vi 1).subgroupOf F.H).subgroupOf (F.U.subgroupOf F.H))) =
        (transportGeometry m.singularMap.geometry (internalModuleEquiv c m E)).line l ∧
      Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.pointOnLine p l) :
    letI := c.kernel_normal
    (transportGeometry m.singularMap.geometry (literalModuleEquiv c m E)).point p =
      ((F.Vi 2).subgroupOf F.U).map (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.U)) ∧
    ∃ l : Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.ZeroProductLine (ZMod 2),
      (V.subgroupOf F.U).map (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.U)) =
        (transportGeometry m.singularMap.geometry (literalModuleEquiv c m E)).line l ∧
      Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.pointOnLine p l := by
  let := c.kernel_normal
  have hpoint := internal_model_image c m E (m.singularMap.geometry.point p)
  change ((transportGeometry m.singularMap.geometry (internalModuleEquiv c m E)).point p).map
    (internalQuotientEquiv c).toMonoidHom = _ at hpoint
  rw [hp,internalQuotientEquiv_image c (F.Vi 2)] at hpoint
  obtain ⟨l,hl,hpl⟩ := hl
  refine ⟨hpoint.symm,l,?_,hpl⟩
  have hline := internal_model_image c m E (m.singularMap.geometry.line l)
  change ((transportGeometry m.singularMap.geometry (internalModuleEquiv c m E)).line l).map
    (internalQuotientEquiv c).toMonoidHom = _ at hline
  rw [← hl,internalQuotientEquiv_image c V] at hline
  exact hline

omit [IsMulCommutative V] in
/-- The original source marked geometry: recognition supplies the entire
module identification and the original flag supplies its point and line. -/
theorem source_marked_geometry
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hf : Function.Injective σ)
    (P : Sylow 2 (HStar F.H)) (hP : star F (K F) ⊔ (P : Subgroup (HStar F.H)) = ⊤)
    (orbit : letI : (star F (K F)).Normal := hfit ▸ inferInstance
      letI : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
        (Multiplicative.toAdd.surjective.comp c.onto)
      OrbitInputs σ (star F (K F)) P hP)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection)
    (hquad : IsQuadratic σ (star F path.Uα))
    (hbound : fixedCodim σ (star F path.Uα) ≤ 2 * rank (star F path.Uα))
    (hRank : ∀ A : Subgroup (Atlas.G2.Model (ZMod 2)),
      A ≤ commutator (Atlas.G2.Model (ZMod 2)) → IsElementaryTwo A → rank A ≤ 2)
    (hOne : ∀ (m : BinaryG2Module) (A : Subgroup (Atlas.G2.Model (ZMod 2))),
      IsElementaryTwo A → rank A = 1 → 2 ≤ fixedCodim m.action A)
    (hTwo : ∀ (m : BinaryG2Module) (A : Subgroup (Atlas.G2.Model (ZMod 2))),
      A ≤ commutator (Atlas.G2.Model (ZMod 2)) → IsElementaryTwo A →
      rank A = 2 → 3 ≤ fixedCodim m.action A)
    (hB46 : ∀ (m : BinaryG2Module) (B : Subgroup (Atlas.G2.Model (ZMod 2))),
      IsBestOffender m.action B ↔ ∃ g : Atlas.G2.Model (ZMod 2),
        Atlas.G2.BinaryCore.elementary.map (MulAut.conj g).toMonoidHom = B) :
    letI : IsMulCommutative V := h.chosen.elementary.toIsMulCommutative
    ∃ i : HStar F.H →* Atlas.G2.Model (ZMod 2), Function.Injective i ∧
      commutator (Atlas.G2.Model (ZMod 2)) ≤ i.range ∧
    ∃ m : BinaryG2Module, ∃ E : m.Space ≃ₗ[ZMod 2] W,
      (∀ a v, E (m.action (i a) v) = σ a (E v)) ∧
      (letI := internalModuleAction c i m E
      ∃ p : Atlas.G2.SingularPoints (ZMod 2),
        MarkedPencil.Assembly.SourceConclusions (F.U.subgroupOf F.H)
          ((F.Vi 1).subgroupOf F.H) ((F.Vi 2).subgroupOf F.H) (V.subgroupOf F.H)
          m.action m.singularMap (internalModuleEquiv c m E) (starMap F) i
          (T.subtype (F.invariant 1)) p ∧
        Assembly.HexagonConclusions (transportGeometry m.singularMap.geometry
          (internalModuleEquiv c m E)) ∧
        (letI := c.kernel_normal
        (transportGeometry m.singularMap.geometry (literalModuleEquiv c m E)).point p =
          ((F.Vi 2).subgroupOf F.U).map (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.U)) ∧
        ∃ l : Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.ZeroProductLine (ZMod 2),
          (V.subgroupOf F.U).map (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.U)) =
            (transportGeometry m.singularMap.geometry (literalModuleEquiv c m E)).line l ∧
          Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.pointOnLine p l)) := by
  let : IsMulCommutative V := h.chosen.elementary.toIsMulCommutative
  obtain ⟨i,hi,hJ,he⟩ := source_natural_or_weyl c h hab hcomponent hfit eK hf
    P hP orbit path hplace selection hquad hbound
  have hm : ∃ m : BinaryG2Module, ∃ E : m.Space ≃ₗ[ZMod 2] W,
      ∀ a v, E (m.action (i a) v) = σ a (E v) := by
    rcases he with ⟨E,he⟩ | ⟨E,he⟩
    · exact ⟨.natural,E,he⟩
    · exact ⟨.weyl,E,he⟩
  obtain ⟨m,E,he⟩ := hm
  let := internalModuleAction c i m E
  obtain ⟨p,hp,hhex⟩ := marked_geometry_of_recognition c h i hi hJ m E he
    hRank (hOne m) (hTwo m) (hB46 m)
  exact ⟨i,hi,hJ,m,E,he,p,hp,hhex,original_marked_points c m E p hp.point hp.line⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
