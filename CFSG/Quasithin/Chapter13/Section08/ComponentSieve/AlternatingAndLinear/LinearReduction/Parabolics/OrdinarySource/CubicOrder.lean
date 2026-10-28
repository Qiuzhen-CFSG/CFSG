module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource.NaturalSetup
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalCubicOrder
import Mathlib.Tactic

/-!
# The ordinary source line residual has cubic quotient

For the genuine natural-section data, the six-letter permutation image
contains A₆ and has a two-group kernel. Relative normality of L and the
Sylow supplement show that the kernel is an extension of a subgroup of
O₂(L) by a subgroup of LT/L. Equivariance and surjectivity of the natural
section map identify N_LT(V₁)'s image with the natural-line stabilizer in
that permutation image.

The intrinsic six-letter calculation gives the line stabilizer's residual
quotient order three. Surjectivity transports the two-residual, and the
restricted two-group kernel transports the intrinsic two-core. Finally,
the subgroup embedding realizes the literal source definition of L₁.
No residual order or flag position is assumed. The extra centralizer-kernel
and T-stability data in `NaturalSetup` are compatible source hypotheses;
the calculation applies to every natural line.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, §13.2 and
Notation 13.2.1, printed pp.876–877; the ordinary case used in 13.8.25,
printed p.959 (PDF p.976). This is the local order calculation only.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
open BinaryPermutation Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {L T V V₁ : Subgroup G}

omit [Finite G] in
/-- The supplied marking fills the alternating subgroup in the permutation image. -/
theorem NaturalSetup.alternating_le_range (d : NaturalSetup L T V V₁) :
    alternatingGroup (Fin 6) ≤ d.permutation.range := by
  intro a ha
  obtain ⟨q, hq⟩ := d.model.surjective ⟨a, ha⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  exact ⟨inclusion le_sup_left l, (d.model_compatible l).trans (congrArg Subtype.val hq)⟩

omit [Finite G] in
/-- The permutation kernel is a two-group, using relative normality and the
actual Sylow supplement. -/
theorem NaturalSetup.permutation_kernel_isPGroup (d : NaturalSetup L T V V₁) :
    IsPGroup 2 d.permutation.ker := by
  let M := L ⊔ T
  let N := L.subgroupOf M
  let _ : N.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le L.le_normalizer d.normalizes_L)
  have hT : IsPGroup 2 (T.subgroupOf M) := by
    rw [← d.sylow_eq]
    exact d.sylow.isPGroup'
  have hgen : N ⊔ T.subgroupOf M = ⊤ := by
    apply map_injective M.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]
  have hquot : IsPGroup 2 (M ⧸ N) := isPGroup_quotient_of_sup_eq_top N _ hT hgen
  let q := (QuotientGroup.mk' N).comp d.permutation.ker.subtype
  have hqker : IsPGroup 2 q.ker := by
    let r : q.ker →* L :=
      (M.subtype.comp (d.permutation.ker.subtype.comp q.ker.subtype)).codRestrict L (by
        intro x
        change x.val.val ∈ N
        exact (QuotientGroup.eq_one_iff (N := N) x.val.val).mp x.property)
    have hr : ∀ x : q.ker, r x ∈ pCore 2 L := by
      intro x
      have hm : d.model (QuotientGroup.mk' (pCore 2 L) (r x)) = 1 :=
        Subtype.ext ((d.model_compatible (r x)).symm.trans x.val.property)
      exact (QuotientGroup.eq_one_iff (N := pCore 2 L) (r x)).mp
        (d.model.injective (hm.trans d.model.map_one.symm))
    let r' : q.ker →* pCore 2 L := r.codRestrict _ hr
    apply pCore_isPGroup.of_injective r'
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : pCore 2 L => (x.val : G)) hab
  have ht := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup q hqker
  rw [comap_top] at ht
  exact ht.of_equiv topEquiv

omit [Finite G] in
private theorem source_mem_line (d : NaturalSetup L T V V₁) (v : V) :
    v.val ∈ V₁ ↔ (d.naturalMap v).toAdd ∈ d.point := by
  conv_lhs => rw [d.line_eq]
  rw [sourceLinePreimage, mem_map]
  constructor
  · rintro ⟨w, hw, he⟩
    have h : w = v := Subtype.ext he
    subst w
    exact hw
  · intro hv
    exact ⟨v, hv, rfl⟩

/-- The source line normalizer is exactly the preimage of its natural-space stabilizer. -/
theorem NaturalSetup.mem_line_normalizer (d : NaturalSetup L T V V₁)
    (g : (L ⊔ T : Subgroup G)) :
    g.val ∈ normalizer (V₁ : Set G) ↔
      d.permutation g ∈ subspaceStabilizer (naturalRepresentation (Fin 6)) d.point := by
  constructor
  · intro hg v
    obtain ⟨w, hw⟩ := d.naturalMap_surjective (Multiplicative.ofAdd v)
    have hw' : (d.naturalMap w).toAdd = v := congrArg Multiplicative.toAdd hw
    rw [← hw', ← d.conjugation g w, ← source_mem_line d, ← source_mem_line d]
    exact ((mem_normalizer_iff.mp hg) w).symm
  · intro hg
    apply mem_normalizer_fintype
    intro x hx
    have hxV : x ∈ V := by
      rw [d.line_eq] at hx
      obtain ⟨v, _, rfl⟩ := hx
      exact v.property
    let v : V := ⟨x, hxV⟩
    have hv := (source_mem_line d v).mp hx
    have hgv := (hg (d.naturalMap v).toAdd).mpr hv
    rw [← d.conjugation g v, ← source_mem_line d] at hgv
    exact hgv


/-- The local permutation image is the actual line stabilizer inside the
whole permutation image. -/
theorem NaturalSetup.line_normalizer_image (d : NaturalSetup L T V V₁) :
    (d.permutation.comp (inclusion (show
      (L ⊔ T) ⊓ normalizer (V₁ : Set G) ≤ L ⊔ T from inf_le_left))).range =
        d.permutation.range ⊓ subspaceStabilizer (naturalRepresentation (Fin 6)) d.point := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨inclusion inf_le_left x, rfl⟩,
      (d.mem_line_normalizer (inclusion inf_le_left x)).mp x.property.2⟩
  · rintro ⟨⟨g, rfl⟩, hg⟩
    exact ⟨⟨g.val, g.property, (d.mem_line_normalizer g).mpr hg⟩, rfl⟩


/-- The ordinary A₆ natural-line residual of Notation 13.2.1 has cubic
quotient by its intrinsic two-core. No local order is assumed. -/
theorem source_residual_quotient_card (d : NaturalSetup L T V V₁)
    (L₁ : Subgroup G)
    (hdef : L₁ = (pResidual 2 ((L ⊔ T) ⊓ normalizer (V₁ : Set G) : Subgroup G)).map
      ((L ⊔ T) ⊓ normalizer (V₁ : Set G)).subtype) :
    Nat.card (L₁ ⧸ pCore 2 L₁) = 3 := by
  let M := (L ⊔ T) ⊓ normalizer (V₁ : Set G)
  let f : M →* Equiv.Perm (Fin 6) := d.permutation.comp (inclusion inf_le_left)
  have hfker : IsPGroup 2 f.ker := by
    rw [← MonoidHom.comap_ker]
    exact d.permutation_kernel_isPGroup.comap_of_injective _
      (inclusion_injective inf_le_left)
  let R := pResidual 2 M
  have hmap : R.map f = (pResidual 2 f.range).map f.range.subtype := by
    calc
      _ = (R.map f.rangeRestrict).map f.range.subtype := by rw [map_map]; rfl
      _ = _ := by rw [map_pResidual_of_surjective 2 f.rangeRestrict f.rangeRestrict_surjective]
  have hmodel : Nat.card (R.map f ⧸ pCore 2 (R.map f)) = 3 := by
    rw [hmap, d.line_normalizer_image]
    exact Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalCubicOrder.point_residual_quotient_card
      d.permutation.range d.alternating_le_range d.point d.point_dim
  let r := f.subgroupMap R
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap]
    exact hfker.comap_subtype
  have hR : Nat.card (R ⧸ pCore 2 R) = 3 :=
    (Nat.card_congr
      (Theory.GroupTheory.ComponentLocalCoreSection.quotientCoreEquiv 2 r
        (f.subgroupMap_surjective R) hr).toEquiv).trans hmodel
  subst L₁
  let e := R.equivMapOfInjective M.subtype M.subtype_injective
  exact (Nat.card_congr
    (Theory.GroupTheory.ComponentLocalCoreSection.quotientCoreEquiv 2 e.symm.toMonoidHom
      e.symm.surjective (IsPGroup.ker_isPGroup_of_injective e.symm.injective)).toEquiv).trans hR

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
