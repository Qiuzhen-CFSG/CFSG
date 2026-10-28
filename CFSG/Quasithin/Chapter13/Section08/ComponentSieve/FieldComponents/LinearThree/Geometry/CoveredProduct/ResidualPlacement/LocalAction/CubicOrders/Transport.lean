module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.NaturalSetup
public import Theory.Representation.HexacodeAction.CubicLocalModel
public import Theory.GroupTheory.SylowNormalIntersection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.CubicOrders.SourceContainment

/-!
# Transport of the covered cubic residual to the concrete model

The source factorization places L₁ in L. Functoriality and idempotence of
finite two-residuals identify its image with the actual point-stabilizer
residual in the hexacode cover. Restricting the supplied Sylow subgroup to
L, which is normal relative to LT, gives the corresponding Sylow marking.
The image of X is then the literal commutator residual of these two images.

The restricted cover map has two-group kernel, so it preserves intrinsic
two-core quotients even when the source subgroup is not normal in L. This
reduces the second cubic order to a finite calculation in the fixed carrier;
that numerical calculation is not assumed or asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1 and Lemma 13.2.2(3), printed pp.876–877;
application 13.8.21(1), printed p.957.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.CubicOrders
open Representation.Hexacode
variable {G : Type*} [Group G] [Finite G]
variable {L T V V₁ V₃ : Subgroup G} (d : NaturalSetup L T V V₁ V₃)

/-- The quotient marking supplied by the earlier covered local setup. -/
def coverProjection : L →* CubicLocalModel.H :=
  d.cover.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

omit [Finite G] in
theorem coverProjection_surjective : Function.Surjective (coverProjection d) :=
  d.cover.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem coverProjection_kernel : (coverProjection d).ker = pCore 2 L := by
  ext x
  change d.cover (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ x ∈ pCore 2 L
  rw [map_eq_one_iff _ d.cover.injective]
  exact QuotientGroup.eq_one_iff _

/-- Image of a source subgroup under its actual two-core quotient marking. -/
def coverImage (X : Subgroup G) : Subgroup CubicLocalModel.H :=
  (X.subgroupOf L).map (coverProjection d)

private theorem residual_idempotent (A : Subgroup G) : residual (residual A) = residual A := by
  change (pResidual 2 (residual A)).map (residual A).subtype = residual A
  rw [(pResidual_eq_top_iff 2 _).mpr (residual_isPPerfect A), ← MonoidHom.range_eq_map, range_subtype]

private theorem residual_subgroupOf (A B : Subgroup G) (h : residual A ≤ B) :
    (residual A).subgroupOf B = residual (A.subgroupOf B) := by
  apply map_injective B.subtype_injective
  rw [map_subgroupOf_eq_of_le h]
  change residual A = ((pResidual 2 (A.subgroupOf B)).map (A.subgroupOf B).subtype).map B.subtype
  rw [map_embedded_pResidual, subgroupOf_map_subtype]
  apply le_antisymm
  · rw [← residual_idempotent A]
    exact embedded_pResidual_mono 2 (le_inf (residual_le A) h)
  · exact embedded_pResidual_mono 2 inf_le_left

include d in
omit [Finite G] in
private theorem one_le_L
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L) : one L T V₁ ≤ L := by
  have hn : one L T V₁ ≤ normalizer (L : Set G) :=
    (one_le L T V₁).trans (inf_le_left.trans (sup_le L.le_normalizer d.normalizes_L))
  have hc : ⁅one L T V₁, T ⊓ L⁆ ≤ L := by
    apply (commutator_mono le_rfl inf_le_right).trans
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp hn
  rw [hfactor]
  exact sup_le ((residual_le _).trans hc) (zero_le L)

omit [Finite G] in
private theorem flag_normalizer_iff (g : (L ⊔ T : Subgroup G)) :
    g.val ∈ normalizer (V₁ : Set G) ↔
      ∀ w : Natural, BinaryPermutation.naturalRepresentation (Fin 6) (d.permutation g) w
        ∈ d.point ↔ w ∈ d.point := by
  constructor
  · intro hg w
    obtain ⟨v, hv⟩ := d.naturalMap_surjective (Multiplicative.ofAdd w)
    have he : (d.naturalMap v).toAdd = w := congrArg Multiplicative.toAdd hv
    rw [← he, ← d.conjugation g v]
    rw [← mem_flagPreimage_iff, ← mem_flagPreimage_iff, ← d.line_eq]
    exact (mem_normalizer_iff.mp hg v.val).symm
  · intro hg
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxV : x ∈ V := by rw [d.line_eq] at hx; exact flagPreimage_le _ _ hx
      let v : V := ⟨x, hxV⟩
      rw [d.line_eq] at hx ⊢
      change (V.normalizerMonoidHom ⟨g.val, d.normalizes_V g.property⟩ v).val ∈ flagPreimage d.naturalMap d.point
      rw [mem_flagPreimage_iff, d.conjugation, hg]
      exact (mem_flagPreimage_iff d.naturalMap d.point v).mp hx
    · intro hx
      have hcV : g.val * x * g.val⁻¹ ∈ V := by rw [d.line_eq] at hx; exact flagPreimage_le _ _ hx
      have hxV : x ∈ V := (mem_normalizer_iff.mp (d.normalizes_V g.property) x).mpr hcV
      let v : V := ⟨x, hxV⟩
      rw [d.line_eq] at hx ⊢
      apply (mem_flagPreimage_iff d.naturalMap d.point v).mpr
      rw [← hg, ← d.conjugation g v, ← mem_flagPreimage_iff]
      exact hx

omit [Finite G] in
/-- Conjugation and the actual flag preimage identify the stabilizer image. -/
theorem coverImage_parabolic : coverImage d (parabolic L T V₁) = CubicLocalModel.stabilizer d.point := by
  ext a
  constructor
  · rintro ⟨l, hl, rfl⟩
    have hg := (flag_normalizer_iff d (inclusion le_sup_left l)).mp hl.2
    change ∀ w : Natural, BinaryPermutation.naturalRepresentation (Fin 6)
      (Atlas.Codes.hexEvenCoordinate (d.cover (QuotientGroup.mk' (pCore 2 L) l))).val w ∈ d.point ↔ w ∈ d.point
    simpa only [d.cover_compatible] using hg
  · intro ha
    obtain ⟨l, rfl⟩ := coverProjection_surjective d a
    refine ⟨l, ⟨(le_sup_left : L ≤ L ⊔ T) l.property, ?_⟩, rfl⟩
    apply (flag_normalizer_iff d (inclusion le_sup_left l)).mpr
    change ∀ w : Natural, BinaryPermutation.naturalRepresentation (Fin 6)
      (Atlas.Codes.hexEvenCoordinate (d.cover (QuotientGroup.mk' (pCore 2 L) l))).val w ∈ d.point ↔ w ∈ d.point at ha
    simpa only [d.cover_compatible] using ha

/-- The image of L₁ is the residual of the full model stabilizer. -/
theorem coverImage_one_source
    :
    coverImage d (one L T V₁) = CubicLocalModel.pointResidual d.point := by
  unfold coverImage one
  rw [residual_subgroupOf _ _ (d.one_le_local)]
  change ((pResidual 2 _).map _).map (coverProjection d) = _
  rw [map_embedded_pResidual]
  change CubicLocalModel.residual (coverImage d (parabolic L T V₁)) = CubicLocalModel.pointResidual d.point
  rw [coverImage_parabolic]
  rfl

theorem coverImage_one
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L) :
    coverImage d (one L T V₁) = CubicLocalModel.pointResidual d.point := by
  unfold coverImage one
  rw [residual_subgroupOf _ _ (one_le_L d hfactor)]
  change ((pResidual 2 _).map _).map (coverProjection d) = _
  rw [map_embedded_pResidual]
  change CubicLocalModel.residual (coverImage d (parabolic L T V₁)) = CubicLocalModel.pointResidual d.point
  rw [coverImage_parabolic]
  rfl

include d in
private theorem exists_sourceSylow :
    ∃ P : Sylow 2 L, (P : Subgroup L) = T.subgroupOf L := by
  have hn : L ⊔ T ≤ normalizer (L : Set G) := sup_le L.le_normalizer d.normalizes_L
  let : (L.subgroupOf (L ⊔ T)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hn
  obtain ⟨P, hP⟩ := d.sylow.exists_subgroupOf_eq_of_normal (L.subgroupOf (L ⊔ T))
  let e : L.subgroupOf (L ⊔ T) ≃* L := subgroupOfEquivOfLe le_sup_left
  have he : Function.Surjective e.toMonoidHom := e.surjective
  refine ⟨P.mapSurjective he, ?_⟩
  change (P : Subgroup _).map e.toMonoidHom = T.subgroupOf L
  rw [hP, d.sylow_eq]
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    have he' : y.val.val = x.val := congrArg Subtype.val he
    change y.val.val ∈ T at hy
    change x.val ∈ T
    exact he' ▸ hy
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    exact hx

/-- The actual image of T∩L, as a Sylow subgroup of the concrete cover. -/
noncomputable def coverSylow : Sylow 2 CubicLocalModel.H :=
  (exists_sourceSylow d).choose.mapSurjective (coverProjection_surjective d)

theorem coverSylow_eq : (coverSylow d : Subgroup CubicLocalModel.H) = coverImage d (T ⊓ L) := by
  rw [coverSylow, Sylow.coe_mapSurjective, (exists_sourceSylow d).choose_spec]
  apply congrArg (map (coverProjection d))
  ext x
  exact ⟨fun h => ⟨h, x.property⟩, fun h => h.1⟩

theorem coverSylow_le_stabilizer :
    (coverSylow d : Subgroup CubicLocalModel.H) ≤ CubicLocalModel.stabilizer d.point := by
  rw [coverSylow_eq, ← coverImage_parabolic d]
  apply map_mono
  intro x hx
  exact ⟨(le_sup_right : T ≤ L ⊔ T) hx.1, d.line_stable hx.1⟩

/-- The image of X is the commutator residual with the actual Sylow image. -/
theorem coverImage_plus_source
    :
    coverImage d (plus L T V₁) = CubicLocalModel.commutatorResidual d.point (coverSylow d) := by
  have h1 := d.one_le_local
  have hc : ⁅one L T V₁, T ⊓ L⁆ ≤ L :=
    (commutator_mono h1 inf_le_right).trans (commutator_le_sup L L |>.trans (sup_idem L).le)
  have hres : plus L T V₁ ≤ L := (residual_le _).trans hc
  have he : ⁅one L T V₁, T ⊓ L⁆.subgroupOf L =
      ⁅(one L T V₁).subgroupOf L, (T ⊓ L).subgroupOf L⁆ := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le hc, map_commutator,
      map_subgroupOf_eq_of_le h1, map_subgroupOf_eq_of_le inf_le_right]
  unfold coverImage plus
  rw [residual_subgroupOf _ _ hres, he]
  change ((pResidual 2 _).map _).map (coverProjection d) = _
  rw [map_embedded_pResidual, map_commutator]
  change CubicLocalModel.residual
    ⁅coverImage d (one L T V₁), coverImage d (T ⊓ L)⁆ = _
  rw [coverImage_one_source d, ← coverSylow_eq]
  rfl


theorem coverImage_plus
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L) :
    coverImage d (plus L T V₁) = CubicLocalModel.commutatorResidual d.point (coverSylow d) := by
  have h1 := one_le_L d hfactor
  have hc : ⁅one L T V₁, T ⊓ L⁆ ≤ L :=
    (commutator_mono h1 inf_le_right).trans (commutator_le_sup L L |>.trans (sup_idem L).le)
  have hres : plus L T V₁ ≤ L := (residual_le _).trans hc
  have he : ⁅one L T V₁, T ⊓ L⁆.subgroupOf L =
      ⁅(one L T V₁).subgroupOf L, (T ⊓ L).subgroupOf L⁆ := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le hc, map_commutator,
      map_subgroupOf_eq_of_le h1, map_subgroupOf_eq_of_le inf_le_right]
  unfold coverImage plus
  rw [residual_subgroupOf _ _ hres, he]
  change ((pResidual 2 _).map _).map (coverProjection d) = _
  rw [map_embedded_pResidual, map_commutator]
  change CubicLocalModel.residual
    ⁅coverImage d (one L T V₁), coverImage d (T ⊓ L)⁆ = _
  rw [coverImage_one d hfactor, ← coverSylow_eq]
  rfl

/-- The cover map restricted to a source subgroup and its actual image. -/
def coverMap (X : Subgroup G) (hXL : X ≤ L) : X →* coverImage d X :=
  ((coverProjection d).comp (inclusion hXL)).codRestrict _
    (fun x => ⟨inclusion hXL x, x.property, rfl⟩)

omit [Finite G] in
theorem coverMap_surjective (X : Subgroup G) (hXL : X ≤ L) :
    Function.Surjective (coverMap d X hXL) := by
  rintro ⟨_, l, hl, rfl⟩
  exact ⟨⟨l.val, hl⟩, Subtype.ext rfl⟩

omit [Finite G] in
theorem coverMap_kernel (X : Subgroup G) (hXL : X ≤ L) :
    (coverMap d X hXL).ker = (pCore 2 L).comap (inclusion hXL) := by
  ext x
  rw [MonoidHom.mem_ker, ← Subtype.coe_inj]
  change coverProjection d (inclusion hXL x) = 1 ↔ inclusion hXL x ∈ pCore 2 L
  rw [← coverProjection_kernel d]
  rfl

/-- The cover projection preserves the intrinsic two-core quotient of every
source subgroup contained in L, without an ambient normality assumption. -/
noncomputable def coverCoreEquiv (X : Subgroup G) (hXL : X ≤ L) :
    (X ⧸ pCore 2 X) ≃* (coverImage d X ⧸ pCore 2 (coverImage d X)) := by
  let g := coverMap d X hXL
  have hg : Function.Surjective g := coverMap_surjective d X hXL
  have hker : IsPGroup 2 g.ker := by
    rw [coverMap_kernel]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hXL)
  let f := (QuotientGroup.mk' (pCore 2 (coverImage d X))).comp g
  have hs : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp hg
  have hk : f.ker = pCore 2 X := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact g.comap_pCore_of_ker_isPGroup hg hker
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hs)

/-- The remaining cubic-order assertion is exactly the intrinsic quotient
calculation in the concrete cover, at its actual point and Sylow marking. -/
theorem plus_core_card_eq_model_source
    :
    Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) =
      Nat.card (CubicLocalModel.commutatorResidual d.point (coverSylow d) ⧸
        pCore 2 (CubicLocalModel.commutatorResidual d.point (coverSylow d))) := by
  have hXL : plus L T V₁ ≤ L :=
    (plus_le_one L T V₁ d.line_stable).trans (d.one_le_local)
  have h := Nat.card_congr (coverCoreEquiv d (plus L T V₁) hXL).toEquiv
  rwa [coverImage_plus_source d] at h

theorem plus_core_card_eq_model
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L) :
    Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) =
      Nat.card (CubicLocalModel.commutatorResidual d.point (coverSylow d) ⧸
        pCore 2 (CubicLocalModel.commutatorResidual d.point (coverSylow d))) := by
  have hXL : plus L T V₁ ≤ L :=
    (plus_le_one L T V₁ d.line_stable).trans (one_le_L d hfactor)
  have h := Nat.card_congr (coverCoreEquiv d (plus L T V₁) hXL).toEquiv
  rwa [coverImage_plus d hfactor] at h

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.CubicOrders
