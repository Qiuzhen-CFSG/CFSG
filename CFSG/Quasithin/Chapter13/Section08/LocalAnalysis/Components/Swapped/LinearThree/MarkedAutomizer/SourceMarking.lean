module
public import Theory.GroupTheory.SylowNormalIntersection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.CoverTransport
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.SourceMarking.ModelCommutator
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.Notation
/-!
# Source marking of the covered point residual

For the compatible binary cover action, the nonidentity element of the
source line gives an actual binary point. The residual of its normalizer
in LT equals the residual of its normalizer in L: monotonicity and
idempotence of finite two-residuals remove the normalizing two-group T.
The quotient action then maps this residual onto the literal cover model.

The actual L₀ = O²(O₂,Z(L)) maps onto the order-three center of the cover.
Its containment in L₁ and its scalar image under `sectionEquiv` are proved.
The actual L₁,+ = O²([L₁,T∩L]) maps to the corresponding model commutator
residual, with T∩L transported to a genuine Sylow subgroup of the cover.
The intrinsic central-extension calculation identifies this image with
`derivedLine`. Thus `exists_marked_section_with_marks` constructs one point
and one section equivalence identifying both source marks, including their
containments in the source residual.
No residual image, cubic coordinates, inverter or automizer is assumed.

Source: Aschbacher–Smith, Notation 13.2.1 and Lemma 13.2.2, printed
pp.877–878; the standing setup on pp.946–947 and the covered branch of
13.8.16(1), printed p.952 (PDF p.969).
-/

@[expose] public section
open Subgroup Theory.SpecificGroups.SymmetricSix
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer
namespace SourceMarking
variable {G : Type*} [Group G]

/-- Removing the normalizing two-group does not change the marked residual. -/
theorem residual_eq_left [Finite G] (L T V₁ : Subgroup G)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (L : Set G)) :
    markedResidual L T V₁ =
      (pResidual 2 (L ⊓ normalizer (V₁ : Set G) : Subgroup G)).map
        (L ⊓ normalizer (V₁ : Set G)).subtype := by
  apply le_antisymm
  · have h := embedded_pResidual_mono 2
      (le_inf (markedResidual_le_left L T V₁ hT hn)
        (markedResidual_le_normalizer L T V₁))
    have hp : IsPPerfect 2 (markedResidual L T V₁) :=
      isPPerfect_embedded_pResidual 2 _
    rwa [(pResidual_eq_top_iff 2 _).mpr hp,
      ← MonoidHom.range_eq_map, range_subtype] at h
  · exact embedded_pResidual_mono 2 (inf_le_inf le_sup_left le_rfl)

private theorem normalizes_two_iff (U : Subgroup G) (hc : Nat.card U = 2)
    (z : U) (hz : z ≠ 1) (g : G) :
    g ∈ normalizer (U : Set G) ↔ g * z.val * g⁻¹ = z.val := by
  have hu := (Nat.card_eq_two_iff' (1 : U)).mp hc
  constructor
  · intro hg
    have hne := (U.normalizerMonoidHom ⟨g, hg⟩).map_ne_one_iff.mpr hz
    exact congrArg Subtype.val (hu.unique hne hz)
  · intro hg
    apply centralizer_le_normalizer _
    intro u hu'
    by_cases he : (⟨u, hu'⟩ : U) = 1
    · have : u = 1 := congrArg Subtype.val he
      simp [this]
    · have : u = z.val := congrArg Subtype.val (hu.unique he hz)
      rw [this]
      exact (mul_inv_eq_iff_eq_mul.mp hg).symm
end SourceMarking

namespace CoverPointModel
variable {G : Type*} [Group G] {L V : Subgroup G} {hLV : L ≤ normalizer (V : Set G)}

/-- The literal quotient map, followed by the supplied cover equivalence. -/
noncomputable def coverMap (d : CoverPointModel L V hLV) : L →* Model.Cover :=
  d.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

theorem coverMap_surjective (d : CoverPointModel L V hLV) :
    Function.Surjective d.coverMap :=
  d.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)

/-- The binary point corresponding to a chosen nonidentity source vector. -/
noncomputable def markedPoint (d : CoverPointModel L V hLV) (V₁ : Subgroup G)
    (hV₁V : V₁ ≤ V) (z : V₁) (hz : z ≠ 1) : BinaryPoint :=
  ⟨Multiplicative.toAdd (d.moduleEquiv (inclusion hV₁V z)),
    d.moduleEquiv.map_ne_one_iff.mpr (fun he => hz (Subtype.ext (congrArg (fun v : V => (v : G)) he)))⟩

/-- Compatibility identifies the source line normalizer with the model stabilizer. -/
theorem coverMap_mem_parabolic_iff (d : CoverPointModel L V hLV)
    (V₁ : Subgroup G) (hV₁V : V₁ ≤ V) (hc : Nat.card V₁ = 2)
    (z : V₁) (hz : z ≠ 1) (l : L) :
    d.coverMap l ∈ Model.parabolic (d.markedPoint V₁ hV₁V z hz) ↔
      l.val ∈ normalizer (V₁ : Set G) := by
  rw [SourceMarking.normalizes_two_iff V₁ hc z hz]
  change (Atlas.Codes.hexEvenCoordinate (d.coverMap l)).val •
    d.markedPoint V₁ hV₁V z hz = d.markedPoint V₁ hV₁V z hz ↔ _
  rw [Subtype.ext_iff]
  change (polarPointPerm (Atlas.Codes.hexEvenCoordinate (d.coverMap l)).val
    (d.markedPoint V₁ hV₁V z hz)).val = _ ↔ _
  rw [← polarAction_point]
  change polarAction (Atlas.Codes.hexEvenCoordinate
    (d.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l))).val
      (Multiplicative.toAdd (d.moduleEquiv (inclusion hV₁V z))) = _ ↔ _
  rw [← d.equivariant]
  change d.moduleEquiv (V.normalizerMonoidHom (inclusion hLV l) (inclusion hV₁V z)) =
    d.moduleEquiv (inclusion hV₁V z) ↔ _
  rw [d.moduleEquiv.injective.eq_iff, Subtype.ext_iff]
  rfl

theorem parabolic_image (d : CoverPointModel L V hLV)
    (V₁ : Subgroup G) (hV₁V : V₁ ≤ V) (hc : Nat.card V₁ = 2)
    (z : V₁) (hz : z ≠ 1) :
    ((normalizer (V₁ : Set G)).subgroupOf L).map d.coverMap =
      Model.parabolic (d.markedPoint V₁ hV₁V z hz) := by
  ext g
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact (d.coverMap_mem_parabolic_iff V₁ hV₁V hc z hz l).mpr hl
  · intro hg
    obtain ⟨l, rfl⟩ := d.coverMap_surjective g
    exact ⟨l, (d.coverMap_mem_parabolic_iff V₁ hV₁V hc z hz l).mp hg, rfl⟩

/-- The source residual has exactly the model residual as image; no image premise. -/
theorem markedResidual_image [Finite G] (d : CoverPointModel L V hLV)
    (T V₁ : Subgroup G) (hT : IsPGroup 2 T)
    (hn : T ≤ normalizer (L : Set G))
    (hV₁V : V₁ ≤ V) (hc : Nat.card V₁ = 2) (z : V₁) (hz : z ≠ 1) :
    (d.subgroupMap (markedResidual L T V₁)
      (markedResidual_le_left L T V₁ hT hn)).range =
        Model.residual (d.markedPoint V₁ hV₁V z hz) := by
  have he : (markedResidual L T V₁).subgroupOf L =
      (pResidual 2 ((normalizer (V₁ : Set G)).subgroupOf L)).map
        ((normalizer (V₁ : Set G)).subgroupOf L).subtype := by
    apply (map_injective L.subtype_injective)
    rw [map_subgroupOf_eq_of_le (markedResidual_le_left L T V₁ hT hn),
      map_embedded_pResidual, subgroupOf_map_subtype, inf_comm,
      SourceMarking.residual_eq_left L T V₁ hT hn]
  have hr : (d.subgroupMap (markedResidual L T V₁)
      (markedResidual_le_left L T V₁ hT hn)).range =
        ((markedResidual L T V₁).subgroupOf L).map d.coverMap := by
    ext g
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨inclusion (markedResidual_le_left L T V₁ hT hn) r, r.property, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨l.val, hl⟩, rfl⟩
  rw [hr, he, map_embedded_pResidual, d.parabolic_image V₁ hV₁V hc z hz]
  rfl

open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
  (centralPreimage zero plus)

/-- Express a restricted homomorphism's range using intrinsic subgroup images. -/
theorem subgroupMap_range (d : CoverPointModel L V hLV) (A : Subgroup G) (hAL : A ≤ L) :
    (d.subgroupMap A hAL).range = (A.subgroupOf L).map d.coverMap := by
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨inclusion hAL a, a.property, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l.val, hl⟩, rfl⟩

private theorem residual_subgroupOf [Finite G] (A : Subgroup G) (hAL : A ≤ L) :
    (((pResidual 2 A).map A.subtype).subgroupOf L) =
      (pResidual 2 (A.subgroupOf L)).map (A.subgroupOf L).subtype := by
  apply (map_injective L.subtype_injective)
  rw [map_subgroupOf_eq_of_le ((map_subtype_le _).trans hAL),
    map_embedded_pResidual, map_subgroupOf_eq_of_le hAL]

/-- Residual images retain their literal ambient inclusion. -/
theorem residual_image [Finite G] (d : CoverPointModel L V hLV)
    (A : Subgroup G) (hAL : A ≤ L) :
    (((pResidual 2 A).map A.subtype).subgroupOf L).map d.coverMap =
      (pResidual 2 ((A.subgroupOf L).map d.coverMap)).map
        ((A.subgroupOf L).map d.coverMap).subtype := by
  rw [residual_subgroupOf A hAL, map_embedded_pResidual]

/-- The actual central preimage maps onto the center of the cover. -/
theorem centralPreimage_image (d : CoverPointModel L V hLV) :
    ((centralPreimage L).subgroupOf L).map d.coverMap = center Model.Cover := by
  have hc : (centralPreimage L).subgroupOf L =
      (center (L ⧸ pCore 2 L)).comap (QuotientGroup.mk' (pCore 2 L)) := by
    apply (map_injective L.subtype_injective)
    rw [map_subgroupOf_eq_of_le (show centralPreimage L ≤ L from map_subtype_le _)]
    rfl
  rw [hc]
  ext g
  constructor
  · rintro ⟨l, hl, rfl⟩
    apply mem_center_iff.mpr
    intro y
    obtain ⟨q, rfl⟩ := d.quotientEquiv.surjective y
    exact (map_mul d.quotientEquiv _ _).symm.trans
      ((congrArg d.quotientEquiv (mem_center_iff.mp hl q)).trans (map_mul d.quotientEquiv _ _))
  · intro hg
    obtain ⟨l, rfl⟩ := d.coverMap_surjective g
    refine ⟨l, ?_, rfl⟩
    change QuotientGroup.mk' (pCore 2 L) l ∈ center (L ⧸ pCore 2 L)
    apply mem_center_iff.mpr
    intro q
    apply d.quotientEquiv.injective
    simp only [map_mul]
    exact mem_center_iff.mp hg (d.quotientEquiv q)

/-- The order-three center is its own two-residual. -/
theorem center_residual :
    (pResidual 2 (center Model.Cover)).map (center Model.Cover).subtype =
      center Model.Cover := by
  have he : pResidual 2 (center Model.Cover) = ⊤ := by
    apply top_unique
    intro z _
    apply mem_pResidual_of_orderOf_coprime
    apply Nat.Coprime.of_dvd_right (orderOf_dvd_natCard z)
    rw [Representation.Hexacode.even_center_card]
    decide
  rw [he, ← MonoidHom.range_eq_map, range_subtype]

/-- L₀ maps onto the intrinsic scalar subgroup, before taking either two-core quotient. -/
theorem zero_image [Finite G] (d : CoverPointModel L V hLV) :
    ((zero L).subgroupOf L).map d.coverMap = center Model.Cover := by
  change (((pResidual 2 (centralPreimage L)).map (centralPreimage L).subtype).subgroupOf L).map
    d.coverMap = _
  rw [d.residual_image (centralPreimage L) (map_subtype_le _),
    d.centralPreimage_image, center_residual]

/-- Central cover elements fix every point of the binary module. -/
theorem center_le_parabolic (x : BinaryPoint) : center Model.Cover ≤ Model.parabolic x := by
  intro g hg
  rw [← Representation.Hexacode.even_kernel_eq_center] at hg
  change Atlas.Codes.hexEvenCoordinate g ∈ MulAction.stabilizer A6 x
  rw [show Atlas.Codes.hexEvenCoordinate g = 1 from hg]
  exact one_mem _

/-- The source zero mark lies in the actual residual, not merely its quotient. -/
theorem zero_le_markedResidual [Finite G] (d : CoverPointModel L V hLV)
    (T V₁ : Subgroup G) (hT : IsPGroup 2 T) (hn : T ≤ normalizer (L : Set G))
    (hV₁V : V₁ ≤ V) (hc : Nat.card V₁ = 2) (z : V₁) (hz : z ≠ 1) :
    zero L ≤ markedResidual L T V₁ := by
  rw [SourceMarking.residual_eq_left L T V₁ hT hn]
  apply embedded_pResidual_mono 2
  apply le_inf (map_subtype_le _)
  intro g hg
  have hl : g ∈ L := map_subtype_le _ hg
  apply (d.coverMap_mem_parabolic_iff V₁ hV₁V hc z hz ⟨g, hl⟩).mp
  apply center_le_parabolic
  rw [← d.centralPreimage_image]
  exact ⟨⟨g, hl⟩, hg, rfl⟩

/-- The scalar subgroup itself is contained in the model residual. -/
theorem center_le_residual (x : BinaryPoint) : center Model.Cover ≤ Model.residual x := by
  rw [← center_residual]
  exact embedded_pResidual_mono 2 (center_le_parabolic x)

/-- Restricting the actual cover map commutes with taking a subgroup image. -/
theorem toModelResidual_image (d : CoverPointModel L V hLV)
    (R A : Subgroup G) (hRL : R ≤ L) (hAR : A ≤ R)
    (x : BinaryPoint) (hr : (d.subgroupMap R hRL).range = Model.residual x) :
    (A.subgroupOf R).map (d.toModelResidual R hRL x hr) =
      ((A.subgroupOf L).map d.coverMap).subgroupOf (Model.residual x) := by
  apply (map_injective (Model.residual x).subtype_injective)
  rw [subgroupOf_map_subtype]
  have hle : (A.subgroupOf L).map d.coverMap ≤ Model.residual x := by
    rw [← hr, d.subgroupMap_range]
    exact map_mono (comap_mono hAR)
  rw [inf_eq_left.mpr hle]
  ext g
  constructor
  · rintro ⟨r, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨inclusion hRL a, ha, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    refine ⟨d.toModelResidual R hRL x hr ⟨l.val, hAR hl⟩, ?_, rfl⟩
    exact ⟨⟨l.val, hAR hl⟩, hl, rfl⟩

/-- Transport the image of any source subgroup through the actual section equivalence. -/
theorem sectionEquiv_subgroup_image [Finite G] (d : CoverPointModel L V hLV)
    (R A : Subgroup G) (hRL : R ≤ L) (hAR : A ≤ R)
    (x : BinaryPoint) (hr : (d.subgroupMap R hRL).range = Model.residual x) :
    ((A.subgroupOf R).map (QuotientGroup.mk' (pCore 2 R))).map
      (d.sectionEquiv R hRL x hr).toMonoidHom =
      (((A.subgroupOf L).map d.coverMap).subgroupOf (Model.residual x)).map
        (QuotientGroup.mk' (pCore 2 (Model.residual x))) := by
  rw [map_map, ← d.toModelResidual_image R A hRL hAR x hr, map_map]
  rfl

/-- The literal source L₀ gives the intrinsic scalar mark in R/O₂(R). -/
theorem sectionEquiv_zero_image [Finite G] (d : CoverPointModel L V hLV)
    (T V₁ : Subgroup G) (hT : IsPGroup 2 T) (hn : T ≤ normalizer (L : Set G))
    (hV₁V : V₁ ≤ V) (hc : Nat.card V₁ = 2) (z : V₁) (hz : z ≠ 1) :
    (((zero L).subgroupOf (markedResidual L T V₁)).map
      (QuotientGroup.mk' (pCore 2 (markedResidual L T V₁)))).map
        (d.sectionEquiv _ (markedResidual_le_left L T V₁ hT hn) _
          (d.markedResidual_image T V₁ hT hn hV₁V hc z hz)).toMonoidHom =
      Model.scalarLine (d.markedPoint V₁ hV₁V z hz) := by
  rw [d.sectionEquiv_subgroup_image _ _ _
    (d.zero_le_markedResidual T V₁ hT hn hV₁V hc z hz), d.zero_image]
  rfl


private theorem commutator_subgroupOf_eq (A B : Subgroup G) (hAL : A ≤ L) (hBL : B ≤ L) :
    ⁅A, B⁆.subgroupOf L = ⁅A.subgroupOf L, B.subgroupOf L⁆ := by
  apply (map_injective L.subtype_injective)
  rw [map_subgroupOf_eq_of_le ((commutator_le_sup A B).trans (sup_le hAL hBL)),
    map_commutator, map_subgroupOf_eq_of_le hAL, map_subgroupOf_eq_of_le hBL]

/-- The actual plus residual maps to the residual of the commutator with the
 actual image of T∩L. There is no prescribed model mark in this identity. -/
theorem plus_image [Finite G] (d : CoverPointModel L V hLV)
    (T V₁ : Subgroup G) (hT : IsPGroup 2 T) (hn : T ≤ normalizer (L : Set G))
    (hV₁V : V₁ ≤ V) (hc : Nat.card V₁ = 2) (z : V₁) (hz : z ≠ 1) :
    ((plus L T V₁).subgroupOf L).map d.coverMap =
      (pResidual 2 (⁅Model.residual (d.markedPoint V₁ hV₁V z hz),
        (T.subgroupOf L).map d.coverMap⁆ : Subgroup Model.Cover)).map
          ⁅Model.residual (d.markedPoint V₁ hV₁V z hz),
            (T.subgroupOf L).map d.coverMap⁆.subtype := by
  have hRL := markedResidual_le_left L T V₁ hT hn
  change (((pResidual 2 (⁅markedResidual L T V₁, T ⊓ L⁆ : Subgroup G)).map
    ⁅markedResidual L T V₁, T ⊓ L⁆.subtype).subgroupOf L).map d.coverMap = _
  rw [d.residual_image _ ((commutator_le_sup _ _).trans (sup_le hRL inf_le_right)),
    commutator_subgroupOf_eq _ _ hRL inf_le_right, map_commutator,
    ← d.subgroupMap_range _ hRL, d.markedResidual_image T V₁ hT hn hV₁V hc z hz]
  have he : (T ⊓ L).subgroupOf L = T.subgroupOf L := by
    ext l
    exact and_iff_left l.property
  rw [he]

/-- The source Sylow arrangement implies the two-group input used above. -/
theorem source_isPGroup (T : Subgroup G) (S : Sylow 2 (L ⊔ T : Subgroup G))
    (hS : (S : Subgroup (L ⊔ T : Subgroup G)) = T.subgroupOf (L ⊔ T)) :
    IsPGroup 2 T := by
  have hp := S.isPGroup'
  rw [hS] at hp
  exact hp.of_equiv (subgroupOfEquivOfLe (show T ≤ L ⊔ T from le_sup_right))

/-- T∩L maps to a genuine Sylow subgroup of the cover. -/
theorem exists_coverSylow [Finite G] (d : CoverPointModel L V hLV)
    (T : Subgroup G) (hn : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (L ⊔ T : Subgroup G))
    (hS : (S : Subgroup (L ⊔ T : Subgroup G)) = T.subgroupOf (L ⊔ T)) :
    ∃ U : Sylow 2 Model.Cover, (U : Subgroup Model.Cover) =
      (T.subgroupOf L).map d.coverMap := by
  let N := L.subgroupOf (L ⊔ T)
  let _ : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hn)
  obtain ⟨J, hJ⟩ := S.exists_subgroupOf_eq_of_normal N
  let e : N ≃* L := subgroupOfEquivOfLe le_sup_left
  let K := J.mapSurjective (f := e.toMonoidHom) e.surjective
  have hK : (K : Subgroup L) = T.subgroupOf L := by
    change (J : Subgroup N).map e.toMonoidHom = _
    rw [hJ, hS]
    ext l
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact hn
    · intro hl
      exact ⟨e.symm l, hl, e.apply_symm_apply l⟩
  refine ⟨K.mapSurjective d.coverMap_surjective, ?_⟩
  rw [Sylow.coe_mapSurjective, hK]

/-- Source stability puts the same Sylow image inside the model parabolic. -/
theorem sourceSylow_image_le_parabolic (d : CoverPointModel L V hLV)
    (T V₁ : Subgroup G) (hTV : T ≤ normalizer (V₁ : Set G))
    (hV₁V : V₁ ≤ V) (hc : Nat.card V₁ = 2) (z : V₁) (hz : z ≠ 1) :
    (T.subgroupOf L).map d.coverMap ≤ Model.parabolic (d.markedPoint V₁ hV₁V z hz) := by
  rintro g ⟨l, hl, rfl⟩
  exact (d.coverMap_mem_parabolic_iff V₁ hV₁V hc z hz l).mpr (hTV hl)

/-- Transport an intrinsic model calculation to the source plus mark.
 Its hypothesis concerns every Sylow subgroup of the concrete parabolic,
 independently of G and all source maps. -/
theorem sectionEquiv_plus_image_of_model [Finite G] (d : CoverPointModel L V hLV)
    (T V₁ : Subgroup G) (hn : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (L ⊔ T : Subgroup G))
    (hS : (S : Subgroup (L ⊔ T : Subgroup G)) = T.subgroupOf (L ⊔ T))
    (hTV : T ≤ normalizer (V₁ : Set G))
    (hV₁V : V₁ ≤ V) (hc : Nat.card V₁ = 2) (z : V₁) (hz : z ≠ 1)
    (hmodel : ∀ (x : BinaryPoint) (U : Sylow 2 Model.Cover),
      (U : Subgroup Model.Cover) ≤ Model.parabolic x →
      (((pResidual 2 (⁅Model.residual x, (U : Subgroup Model.Cover)⁆ : Subgroup Model.Cover)).map
        ⁅Model.residual x, (U : Subgroup Model.Cover)⁆.subtype).subgroupOf
          (Model.residual x)).map (QuotientGroup.mk' (pCore 2 (Model.residual x))) =
        Model.derivedLine x) :
    (((plus L T V₁).subgroupOf (markedResidual L T V₁)).map
      (QuotientGroup.mk' (pCore 2 (markedResidual L T V₁)))).map
        (d.sectionEquiv _ (markedResidual_le_left L T V₁ (source_isPGroup T S hS) hn) _
          (d.markedResidual_image T V₁ (source_isPGroup T S hS) hn hV₁V hc z hz)).toMonoidHom =
      Model.derivedLine (d.markedPoint V₁ hV₁V z hz) := by
  have hT := source_isPGroup T S hS
  have hplus : plus L T V₁ ≤ markedResidual L T V₁ :=
    CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.plus_le_one L T V₁ hTV
  rw [d.sectionEquiv_subgroup_image _ _ _ hplus,
    d.plus_image T V₁ hT hn hV₁V hc z hz]
  obtain ⟨U, hU⟩ := d.exists_coverSylow T hn S hS
  rw [← hU]
  have hle : (U : Subgroup Model.Cover) ≤ Model.parabolic (d.markedPoint V₁ hV₁V z hz) := by
    rw [hU]
    exact d.sourceSylow_image_le_parabolic T V₁ hTV hV₁V hc z hz
  exact hmodel _ U hle

/-- The literal source L₁,+ gives the intrinsic derived mark in R/O₂(R),
with the model commutator identity discharged. -/
theorem sectionEquiv_plus_image [Finite G] (d : CoverPointModel L V hLV)
    (T V₁ : Subgroup G) (hn : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (L ⊔ T : Subgroup G))
    (hS : (S : Subgroup (L ⊔ T : Subgroup G)) = T.subgroupOf (L ⊔ T))
    (hTV : T ≤ normalizer (V₁ : Set G))
    (hV₁V : V₁ ≤ V) (hc : Nat.card V₁ = 2) (z : V₁) (hz : z ≠ 1) :
    (((plus L T V₁).subgroupOf (markedResidual L T V₁)).map
      (QuotientGroup.mk' (pCore 2 (markedResidual L T V₁)))).map
        (d.sectionEquiv _ (markedResidual_le_left L T V₁ (source_isPGroup T S hS) hn) _
          (d.markedResidual_image T V₁ (source_isPGroup T S hS) hn hV₁V hc z hz)).toMonoidHom =
      Model.derivedLine (d.markedPoint V₁ hV₁V z hz) :=
  d.sectionEquiv_plus_image_of_model T V₁ hn S hS hTV hV₁V hc z hz
    Model.commutator_residual_image_eq_derivedLine


/-- Source input constructs a compatible marked point and quotient map,
 and identifies the zero mark without any geometric image assumption. -/
theorem exists_marked_section [Finite G] (d : CoverPointModel L V hLV)
    (T V₁ : Subgroup G) (hn : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (L ⊔ T : Subgroup G))
    (hS : (S : Subgroup (L ⊔ T : Subgroup G)) = T.subgroupOf (L ⊔ T))
    (hV₁V : V₁ ≤ V) (hc : Nat.card V₁ = 2) :
    ∃ (x : BinaryPoint)
      (hr : (d.subgroupMap (markedResidual L T V₁)
        (markedResidual_le_left L T V₁ (source_isPGroup T S hS) hn)).range = Model.residual x),
      zero L ≤ markedResidual L T V₁ ∧
      (((zero L).subgroupOf (markedResidual L T V₁)).map
        (QuotientGroup.mk' (pCore 2 (markedResidual L T V₁)))).map
          (d.sectionEquiv _ (markedResidual_le_left L T V₁ (source_isPGroup T S hS) hn)
            x hr).toMonoidHom = Model.scalarLine x := by
  obtain ⟨z, hz, _⟩ := (Nat.card_eq_two_iff' (1 : V₁)).mp hc
  refine ⟨d.markedPoint V₁ hV₁V z hz,
    d.markedResidual_image T V₁ (source_isPGroup T S hS) hn hV₁V hc z hz,
    d.zero_le_markedResidual T V₁ (source_isPGroup T S hS) hn hV₁V hc z hz, ?_⟩
  exact d.sectionEquiv_zero_image T V₁ (source_isPGroup T S hS) hn hV₁V hc z hz

/-- The source Sylow arrangement and stable line construct a compatible
point and section equivalence carrying both actual source marks to the
intrinsic model lines. No residual-image or marking identity is assumed. -/
theorem exists_marked_section_with_marks [Finite G] (d : CoverPointModel L V hLV)
    (T V₁ : Subgroup G) (hn : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (L ⊔ T : Subgroup G))
    (hS : (S : Subgroup (L ⊔ T : Subgroup G)) = T.subgroupOf (L ⊔ T))
    (hTV : T ≤ normalizer (V₁ : Set G))
    (hV₁V : V₁ ≤ V) (hc : Nat.card V₁ = 2) :
    ∃ (x : BinaryPoint)
      (hr : (d.subgroupMap (markedResidual L T V₁)
        (markedResidual_le_left L T V₁ (source_isPGroup T S hS) hn)).range = Model.residual x),
      zero L ≤ markedResidual L T V₁ ∧
      plus L T V₁ ≤ markedResidual L T V₁ ∧
      (((zero L).subgroupOf (markedResidual L T V₁)).map
        (QuotientGroup.mk' (pCore 2 (markedResidual L T V₁)))).map
          (d.sectionEquiv _ (markedResidual_le_left L T V₁ (source_isPGroup T S hS) hn)
            x hr).toMonoidHom = Model.scalarLine x ∧
      (((plus L T V₁).subgroupOf (markedResidual L T V₁)).map
        (QuotientGroup.mk' (pCore 2 (markedResidual L T V₁)))).map
          (d.sectionEquiv _ (markedResidual_le_left L T V₁ (source_isPGroup T S hS) hn)
            x hr).toMonoidHom = Model.derivedLine x := by
  obtain ⟨z, hz, _⟩ := (Nat.card_eq_two_iff' (1 : V₁)).mp hc
  refine ⟨d.markedPoint V₁ hV₁V z hz,
    d.markedResidual_image T V₁ (source_isPGroup T S hS) hn hV₁V hc z hz,
    d.zero_le_markedResidual T V₁ (source_isPGroup T S hS) hn hV₁V hc z hz, ?_,
    d.sectionEquiv_zero_image T V₁ (source_isPGroup T S hS) hn hV₁V hc z hz,
    d.sectionEquiv_plus_image T V₁ hn S hS hTV hV₁V hc z hz⟩
  exact CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.plus_le_one L T V₁ hTV

end CoverPointModel
end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer

end
