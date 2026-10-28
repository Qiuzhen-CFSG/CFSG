module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalModels.Factorization.Model
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.NaturalSetup
public import Theory.GroupTheory.SylowNormalIntersection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.A6Exclusion
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.QuotientMarks
public import Theory.GroupTheory.PResidual.PrimeSection


/-!
# The source factorization L₁ = L₁,+ L₀

The actual Sylow supplement first puts the two-residual L₁ inside L,
independently of the desired factorization. The original cover projection
then maps L₁, L₁,+ and L₀ to the marked point residual, its Sylow-commutator
residual, and the cubic center. The model factorization identifies these
images. Relative normality and two-perfectness lift it through the
original two-group kernel. A central fixed kernel in the natural section
is allowed throughout.

This proves the i=1 clause of Aschbacher–Smith 13.2.2(3), printed p.877,
with the literal definitions consumed by 13.8.5 and 13.8.21.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CoverFactorization
open Representation.Hexacode
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
variable {G : Type*} [Group G] [Finite G]
variable {L T V V₁ V₃ : Subgroup G} (d : NaturalSetup L T V V₁ V₃)

/-- The quotient marking supplied by the earlier covered local setup. -/
@[expose] def sourceProjection : L →* CubicLocalModel.H :=
  d.cover.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

omit [Finite G] in
theorem sourceProjection_surjective : Function.Surjective (sourceProjection d) :=
  d.cover.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem sourceProjection_kernel : (sourceProjection d).ker = pCore 2 L := by
  ext x
  change d.cover (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ x ∈ pCore 2 L
  rw [map_eq_one_iff _ d.cover.injective]
  exact QuotientGroup.eq_one_iff _

/-- Image of a source subgroup under its actual two-core quotient marking. -/
@[expose] def sourceImage (X : Subgroup G) : Subgroup CubicLocalModel.H :=
  (X.subgroupOf L).map (sourceProjection d)

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
theorem sourceImage_parabolic : sourceImage d (parabolic L T V₁) = CubicLocalModel.stabilizer d.point := by
  ext a
  constructor
  · rintro ⟨l, hl, rfl⟩
    have hg := (flag_normalizer_iff d (inclusion le_sup_left l)).mp hl.2
    change ∀ w : Natural, BinaryPermutation.naturalRepresentation (Fin 6)
      (Atlas.Codes.hexEvenCoordinate (d.cover (QuotientGroup.mk' (pCore 2 L) l))).val w ∈ d.point ↔ w ∈ d.point
    simpa only [d.cover_compatible] using hg
  · intro ha
    obtain ⟨l, rfl⟩ := sourceProjection_surjective d a
    refine ⟨l, ⟨(le_sup_left : L ≤ L ⊔ T) l.property, ?_⟩, rfl⟩
    apply (flag_normalizer_iff d (inclusion le_sup_left l)).mpr
    change ∀ w : Natural, BinaryPermutation.naturalRepresentation (Fin 6)
      (Atlas.Codes.hexEvenCoordinate (d.cover (QuotientGroup.mk' (pCore 2 L) l))).val w ∈ d.point ↔ w ∈ d.point at ha
    simpa only [d.cover_compatible] using ha

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
noncomputable def sourceSylow : Sylow 2 CubicLocalModel.H :=
  (exists_sourceSylow d).choose.mapSurjective (sourceProjection_surjective d)

theorem sourceSylow_eq : (sourceSylow d : Subgroup CubicLocalModel.H) = sourceImage d (T ⊓ L) := by
  rw [sourceSylow, Sylow.coe_mapSurjective, (exists_sourceSylow d).choose_spec]
  apply congrArg (map (sourceProjection d))
  ext x
  exact ⟨fun h => ⟨h, x.property⟩, fun h => h.1⟩

theorem sourceSylow_le_stabilizer :
    (sourceSylow d : Subgroup CubicLocalModel.H) ≤ CubicLocalModel.stabilizer d.point := by
  rw [sourceSylow_eq, ← sourceImage_parabolic d]
  apply map_mono
  intro x hx
  exact ⟨(le_sup_right : T ≤ L ⊔ T) hx.1, d.line_stable hx.1⟩


include d in
omit [Finite G] in
theorem source_one_le : one L T V₁ ≤ L := by
  have hp := d.sylow.isPGroup'
  rw [d.sylow_eq] at hp
  exact Components.Swapped.LinearThree.MarkedAutomizer.markedResidual_le_left L T V₁
    (hp.of_equiv (subgroupOfEquivOfLe (show T ≤ L ⊔ T from le_sup_right))) d.normalizes_L

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

theorem source_one_image :
    sourceImage d (one L T V₁) = CubicLocalModel.pointResidual d.point := by
  unfold sourceImage ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.one
  rw [residual_subgroupOf _ _ (source_one_le d)]
  change ((pResidual 2 _).map _).map (sourceProjection d) = _
  rw [map_embedded_pResidual]
  change CubicLocalModel.residual (sourceImage d (parabolic L T V₁)) = CubicLocalModel.pointResidual d.point
  rw [sourceImage_parabolic]
  rfl

theorem source_plus_image :
    sourceImage d (plus L T V₁) = CubicLocalModel.commutatorResidual d.point (sourceSylow d) := by
  have h1 := source_one_le d
  have hc : ⁅one L T V₁, T ⊓ L⁆ ≤ L :=
    (commutator_mono h1 inf_le_right).trans (commutator_le_sup L L |>.trans (sup_idem L).le)
  have hres : plus L T V₁ ≤ L := (residual_le _).trans hc
  have he : ⁅one L T V₁, T ⊓ L⁆.subgroupOf L =
      ⁅(one L T V₁).subgroupOf L, (T ⊓ L).subgroupOf L⁆ := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le hc, map_commutator,
      map_subgroupOf_eq_of_le h1, map_subgroupOf_eq_of_le inf_le_right]
  unfold sourceImage plus
  rw [residual_subgroupOf _ _ hres, he]
  change ((pResidual 2 _).map _).map (sourceProjection d) = _
  rw [map_embedded_pResidual, map_commutator]
  change CubicLocalModel.residual
    ⁅sourceImage d (one L T V₁), sourceImage d (T ⊓ L)⁆ = _
  rw [source_one_image d, ← sourceSylow_eq]
  rfl



include d in
omit [Finite G] in
theorem source_zero_le : zero L ≤ one L T V₁ := by
  apply embedded_pResidual_mono 2
  apply le_inf ((map_subtype_le _).trans le_sup_left)
  apply d.centralPreimage_centralizes.trans
  apply (centralizer_le ?_).trans (centralizer_le_normalizer _)
  rw [d.line_eq]
  exact flagPreimage_le _ _

omit [Finite G] in
private theorem central_image : sourceImage d (centralPreimage L) = center Atlas.Codes.HexEvenAutomorphisms := by
  have hc : (centralPreimage L).subgroupOf L =
      (center (L ⧸ pCore 2 L)).comap (QuotientGroup.mk' (pCore 2 L)) := by
    apply (map_injective L.subtype_injective)
    rw [map_subgroupOf_eq_of_le (show centralPreimage L ≤ L from map_subtype_le _)]
    rfl
  unfold sourceImage
  rw [hc]
  ext g
  constructor
  · rintro ⟨l, hl, rfl⟩
    apply mem_center_iff.mpr
    intro y
    obtain ⟨q, rfl⟩ := d.cover.surjective y
    exact (map_mul d.cover _ _).symm.trans
      ((congrArg d.cover (mem_center_iff.mp hl q)).trans (map_mul d.cover _ _))
  · intro hg
    obtain ⟨l, rfl⟩ := sourceProjection_surjective d g
    refine ⟨l, ?_, rfl⟩
    change QuotientGroup.mk' (pCore 2 L) l ∈ center (L ⧸ pCore 2 L)
    apply mem_center_iff.mpr
    intro q
    apply d.cover.injective
    simp only [map_mul]
    exact mem_center_iff.mp hg (d.cover q)

theorem source_zero_image : sourceImage d (zero L) = center Atlas.Codes.HexEvenAutomorphisms := by
  unfold sourceImage zero
  rw [residual_subgroupOf _ _ (zero_le L)]
  change ((pResidual 2 _).map _).map (sourceProjection d) = _
  rw [map_embedded_pResidual]
  change residual (sourceImage d (centralPreimage L)) = _
  rw [central_image d]
  have he : pResidual 2 (center Atlas.Codes.HexEvenAutomorphisms) = ⊤ := by
    apply top_unique
    intro z _
    apply mem_pResidual_of_orderOf_coprime
    apply Nat.Coprime.of_dvd_right (orderOf_dvd_natCard z)
    rw [even_center_card]
    decide
  change (pResidual 2 (center Atlas.Codes.HexEvenAutomorphisms)).map _ = _
  rw [he, ← MonoidHom.range_eq_map, range_subtype]

include d in
theorem source_factorization : one L T V₁ = plus L T V₁ ⊔ zero L := by
  let R := one L T V₁
  let B := plus L T V₁ ⊔ zero L
  have hRL : R ≤ L := source_one_le d
  have hBR : B ≤ R := sup_le (plus_le_one L T V₁ d.line_stable) (source_zero_le d)
  have hBL : B ≤ L := hBR.trans hRL
  have hn : R ≤ normalizer (B:Set G) :=
    (le_inf (one_normalizes_plus L T V₁)
      (one_normalizes_zero L T V₁ d.normalizes_L)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  let N := B.subgroupOf R
  let : N.Normal := normal_subgroupOf_of_le_normalizer hn
  let f : R →* Atlas.Codes.HexEvenAutomorphisms :=
    (sourceProjection d).comp (inclusion hRL)
  have hk : f.ker = (pCore 2 L).comap (inclusion hRL) := by
    rw [← MonoidHom.comap_ker,sourceProjection_kernel]
  have hp : IsPGroup 2 f.ker := by
    rw [hk]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hRL)
  have himage : sourceImage d R = sourceImage d B := by
    change sourceImage d (one L T V₁) = sourceImage d (plus L T V₁ ⊔ zero L)
    simp only [sourceImage]
    rw [subgroupOf_sup (plus_le_L L T V₁ d.normalizes_L) (zero_le L),Subgroup.map_sup]
    change sourceImage d (one L T V₁) = sourceImage d (plus L T V₁) ⊔ sourceImage d (zero L)
    rw [source_one_image d,source_plus_image d,source_zero_image d]
    exact model_factorization d.point d.point_dim (sourceSylow d) (sourceSylow_le_stabilizer d)
  have him : (⊤:Subgroup R).map f = N.map f := by
    have hi : (⊤:Subgroup R).map (inclusion hRL) = R.subgroupOf L := by
      ext x
      constructor
      · rintro ⟨r,_,rfl⟩
        exact r.property
      · intro hx
        exact ⟨⟨x.val,hx⟩,mem_top _,rfl⟩
    have hj : N.map (inclusion hRL) = B.subgroupOf L := by
      ext x
      constructor
      · rintro ⟨r,hr,rfl⟩
        exact hr
      · intro hx
        exact ⟨⟨x.val,hBR hx⟩,hx,rfl⟩
    rw [show f = (sourceProjection d).comp (inclusion hRL) from rfl,←map_map,←map_map,hi,hj]
    exact himage
  have hs : N ⊔ f.ker = ⊤ := by
    have he := congrArg (Subgroup.comap f) him
    rw [comap_map_eq,top_sup_eq,comap_map_eq] at he
    exact he.symm
  have hr : IsPPerfect 2 (⊤:Subgroup R) :=
    (residual_isPPerfect (parabolic L T V₁)).of_surjective
      (Subgroup.topEquiv : (⊤:Subgroup R) ≃* R).symm.toMonoidHom
      Subgroup.topEquiv.symm.surjective
  have he := le_normal_of_isPPerfect_of_le_sup_pGroup ⊤ N f.ker hr hp hs.ge
  apply le_antisymm _ hBR
  intro x hx
  exact he (mem_top (⟨x,hx⟩:R))

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CoverFactorization

end
