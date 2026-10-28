module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Actions
public import CFSG.Quasithin.ChapterB.InternalThompsonAction
public import Theory.GroupTheory.SylowNormalJoinIntersection
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# The original natural-module action and its quotient kernel

The actor is the literal LT/C_LT(V). Its marked L-image is identified
with L/O2(L) using the actual conjugation kernel. The original map from V
to its chosen central quotient intertwines this marking. A seed-centralizing
normalizer element centralizes L/O2(L); the final lift uses the intersections
of the specified Sylow subgroup with two normal factors.

These transports supply the original-group conclusion in the natural-module
Thompson argument of Aschbacher--Smith 11.4.2, printed p.777. Normality is
relative to LT throughout, and the quotient centralizer retains N_G(L).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.NaturalThompson
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (S : D.NonbinaryNaturalInput)

include S in
/-- The kernel identity uses faithfulness of the supplied central action,
including the full SL3 center. -/
theorem component_action_kernel :
    (centralizer (V : Set G)).subgroupOf L = pCore 2 L := by
  apply le_antisymm
  · intro l hl
    apply (QuotientGroup.eq_one_iff l).mp
    apply S.faithful
    exact (D.actionCentralizer_le_centralAction_ker hl).trans
      (map_one D.centralQuotientAction).symm
  · exact D.chosenAction_core.trans D.chosenAction_ker.le

def originalGroup (_D : Chapter12.Section02.ChosenModule T L V) : Subgroup G := L ⊔ T

def originalModule (_S : D.NonbinaryNaturalInput) : Subgroup (originalGroup D) :=
  V.subgroupOf (originalGroup D)

instance originalModule_normal : (originalModule S).Normal :=
  normal_subgroupOf_of_le_normalizer (sup_le D.normalizes S.sylow_normalizes)

instance originalModule_elementary : IsElementaryAbelian 2 (originalModule S) := by
  let := D.elementary
  exact IsElementaryAbelian.subgroupOf (D.le_sylow.trans le_sup_right)

abbrev OriginalQuotient := ChapterB.InternalThompsonAction.ActionQuotient (originalModule S)
abbrev originalProjection : originalGroup D →* OriginalQuotient S :=
  ChapterB.InternalThompsonAction.actionMk (originalModule S)
def originalAction : Representation (ZMod 2) (OriginalQuotient S) (Additive (originalModule S)) :=
  ChapterB.InternalThompsonAction.action (originalModule S)
def originalLayer : Subgroup (OriginalQuotient S) :=
  (L.subgroupOf (originalGroup D)).map (originalProjection S)

instance originalLayer_normal : (originalLayer S).Normal := by
  let : (L.subgroupOf (originalGroup D)).Normal :=
    normal_subgroupOf_of_le_normalizer
      (sup_le L.le_normalizer D.sylow_normalizes_component)
  exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

def layerProjection : L →* originalLayer S :=
  ((originalProjection S).subgroupMap (L.subgroupOf (originalGroup D))).comp
    (subgroupOfEquivOfLe (show L ≤ originalGroup D from le_sup_left)).symm.toMonoidHom

theorem layerProjection_surjective : Function.Surjective (layerProjection S) :=
  ((originalProjection S).subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe _).symm.surjective

theorem layerProjection_ker : (layerProjection S).ker = pCore 2 L := by
  rw [← component_action_kernel S]
  ext l
  change layerProjection S l = 1 ↔ (l : G) ∈ centralizer (V : Set G)
  have he : layerProjection S l = 1 ↔
      (⟨l, (le_sup_left : L ≤ originalGroup D) l.property⟩ : originalGroup D) ∈
        centralizer (originalModule S : Set (originalGroup D)) := by
    rw [← Subtype.coe_inj]
    exact QuotientGroup.eq_one_iff _
  rw [he]
  constructor
  · intro h v hv
    exact congrArg Subtype.val (h ⟨v, (le_sup_right : (T : Subgroup G) ≤ originalGroup D) (D.le_sylow hv)⟩ hv)
  · intro h v hv
    exact Subtype.ext (h v hv)

def layerEquiv : (L ⧸ pCore 2 L) ≃* originalLayer S :=
  (QuotientGroup.quotientMulEquivOfEq (layerProjection_ker S).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (layerProjection S) (layerProjection_surjective S))

theorem layerEquiv_mk (l : L) :
    layerEquiv S (QuotientGroup.mk' (pCore 2 L) l) = layerProjection S l := rfl

/-- The original quotient map, before choosing any natural coordinates. -/
def moduleProjection : Additive (originalModule S) →ₗ[ZMod 2] D.chosenCentralQuotient :=
  ((D.toCentralQuotient.comp (subgroupOfEquivOfLe
    (D.le_sylow.trans (le_sup_right : (T : Subgroup G) ≤ originalGroup D))).toMonoidHom).toAdditive).toZModLinearMap 2

theorem moduleProjection_surjective : Function.Surjective (moduleProjection S) :=
  D.toCentralQuotient_surjective.comp (subgroupOfEquivOfLe _).surjective

theorem moduleProjection_component (l : L) (v : Additive (originalModule S)) :
    moduleProjection S (originalAction S (layerProjection S l) v) =
      D.chosenCentralAction l (moduleProjection S v) := by
  let e := subgroupOfEquivOfLe
    (D.le_sylow.trans (le_sup_right : (T : Subgroup G) ≤ originalGroup D))
  have he : e (originalAction S (layerProjection S l) v).toMul =
      V.normalizerMonoidHom (inclusion D.normalizes l) (e v.toMul) := by
    apply Subtype.ext
    change (((originalAction S (layerProjection S l) v).toMul : originalGroup D) : G) =
      (l : G) * ((v.toMul : originalGroup D) : G) * (l : G)⁻¹
    exact congrArg (fun x : originalGroup D => (x : G)) (ChapterB.InternalThompsonAction.action_apply
      (originalModule S) ⟨l, (le_sup_left : L ≤ originalGroup D) l.property⟩ v)
  change (D.toCentralQuotient (e (originalAction S (layerProjection S l) v).toMul)).toAdd = _
  rw [he]
  let c := LocalGeometry.coordinates D S
  apply c.linearEquiv.injective
  change (c.projection (V.normalizerMonoidHom (inclusion D.normalizes l) (e v.toMul))).toAdd = _
  rw [c.projection_component_conjugation]
  exact (c.intertwines (QuotientGroup.mk' (pCore 2 L) l) (moduleProjection S v)).symm

include S in
/-- An element centralizing the actual seed centralizes the component's
actual two-core quotient. The normalizer convention is retained. -/
theorem seedCentralizer_le_quotientCentralizer :
    normalizer (L : Set G) ⊓ centralizer (V : Set G) ≤
      Closure.coreQuotientCentralizer L := by
  rintro g ⟨hgL,hgV⟩
  refine ⟨⟨g,hgL⟩, ?_, rfl⟩
  apply MulEquiv.ext
  intro q
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  rw [Closure.coreQuotientAction_apply_mk]
  change QuotientGroup.mk' (pCore 2 L) (L.normalizerMonoidHom ⟨g,hgL⟩ l) =
    QuotientGroup.mk' (pCore 2 L) l
  apply QuotientGroup.eq_iff_div_mem.mpr
  rw [← component_action_kernel S]
  have hn : L ≤ normalizer (centralizer (V : Set G) : Set G) :=
    D.normalizes.trans (normalizer_le_normalizer_centralizer V)
  change g * (l : G) * g⁻¹ / (l : G) ∈ centralizer (V : Set G)
  simpa only [div_eq_mul_inv, commutatorElement_def] using
    le_normalizer_iff_commutator_le_left.mp hn (commutator_mem_commutator hgV l.property)

/-- Internal centralization is exactly ambient centralization under inclusion. -/
theorem originalCentralizer_map :
    (centralizer (originalModule S : Set (originalGroup D))).map (originalGroup D).subtype =
      originalGroup D ⊓ centralizer (V : Set G) := by
  ext g
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨x.property, ?_⟩
    intro v hv
    exact congrArg (fun x : originalGroup D => (x : G))
      (hx ⟨v,(le_sup_right : (T : Subgroup G) ≤ originalGroup D) (D.le_sylow hv)⟩ hv)
  · rintro ⟨hg,hc⟩
    refine ⟨⟨g,hg⟩, ?_, rfl⟩
    intro v hv
    exact Subtype.ext (hc v hv)

/-- Lift containment in the faithful original L-image and use the specified
Sylow intersection, rather than an arbitrary lift of the quotient kernel. -/
theorem thompson_le_sylow_join_of_image_le
    (himage : (elementaryAbelianMaxJ
      ((T.subtype (show (T : Subgroup G) ≤ originalGroup D from le_sup_right)) :
        Subgroup (originalGroup D))).map (originalProjection S) ≤ originalLayer S) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤
      ((T : Subgroup G) ⊓ L) ⊔ ((T : Subgroup G) ⊓ Closure.coreQuotientCentralizer L) := by
  let P := T.subtype (show (T : Subgroup G) ≤ originalGroup D from le_sup_right)
  let K := L.subgroupOf (originalGroup D)
  let C := centralizer (originalModule S : Set (originalGroup D))
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hpre : elementaryAbelianMaxJ (P : Subgroup (originalGroup D)) ≤ K ⊔ C := by
    have hh := map_le_iff_le_comap.mp himage
    change _ ≤ ((K.map (originalProjection S)).comap (originalProjection S)) at hh
    rwa [comap_map_eq, QuotientGroup.ker_mk'] at hh
  have hJT : elementaryAbelianMaxJ (P : Subgroup (originalGroup D)) ≤ P :=
    sSup_le fun _ hA => hA.1
  have hh := (le_inf hJT hpre).trans_eq (P.inf_sup_eq_sup_inf_normal K C)
  have hm := map_mono hh (f := (originalGroup D).subtype)
  have hP : (P : Subgroup (originalGroup D)).map (originalGroup D).subtype = T :=
    map_subgroupOf_eq_of_le le_sup_right
  rw [← elementaryAbelianMaxJ_map_injective _ (originalGroup D).subtype_injective, hP, Subgroup.map_sup,
    Subgroup.map_inf _ _ _ (originalGroup D).subtype_injective,
    Subgroup.map_inf _ _ _ (originalGroup D).subtype_injective,
    hP, map_subgroupOf_eq_of_le (show L ≤ originalGroup D from le_sup_left),
    originalCentralizer_map] at hm
  apply hm.trans
  apply sup_le_sup le_rfl
  intro g hg
  exact ⟨hg.1, seedCentralizer_le_quotientCentralizer S
    ⟨D.sylow_normalizes_component hg.1, hg.2.2⟩⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.NaturalThompson
