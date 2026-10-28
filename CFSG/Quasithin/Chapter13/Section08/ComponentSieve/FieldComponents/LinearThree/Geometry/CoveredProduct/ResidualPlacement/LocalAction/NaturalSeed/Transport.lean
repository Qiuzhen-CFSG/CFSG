module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.NaturalSetup
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.Algebra.Module.ZMod

/-!
# Transport from the actual natural section to the covered seed

The hexacode coordinate map makes the image of L exactly A₆. Surjectivity
and equivariance of the natural section map identify the image of N_LT(V₁)
with the point stabilizer in the permutation image of LT. Finite residual
transport then identifies the image of L₁ with its two-residual, without
confusing this residual with the larger stabilizer.

Linear action differences are images of actual subgroup commutators.
Generation modulo the point lifts to generation modulo V₁ because V₁ is
the whole inverse image of the point and thus contains the section kernel.
The image of the supplied Sylow subgroup is Sylow in the actual permutation
image, and it preserves both flag subspaces. The concrete residual action
on that flag remains a separate model calculation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1, printed p.877; the seed action used in 13.8.16 and
13.8.21(1), printed pp.952–953 and 957.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.NaturalSetup
noncomputable section
variable {G : Type*} [Group G] {L T V V₁ V₃ : Subgroup G}
  (d : NaturalSetup L T V V₁ V₃)

/-- The literal natural six-letter representation, with its original quotient model. -/
abbrev naturalAction := BinaryPermutation.naturalRepresentation (Fin 6)

/-- Permutation image after restricting an ambient subgroup to LT. -/
def permutationImage (A : Subgroup G) : Subgroup (Equiv.Perm (Fin 6)) :=
  (A.subgroupOf (L ⊔ T)).map d.permutation

/-- The cover compatibility and coordinate surjectivity identify the full A₆ image. -/
theorem permutationImage_L : d.permutationImage L = alternatingGroup (Fin 6) := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    let l : L := ⟨g.val, hg⟩
    have he := d.cover_compatible l
    change d.permutation g = _ at he
    rw [he]
    exact (Atlas.Codes.hexEvenCoordinate _).property
  · intro a ha
    obtain ⟨h, hh⟩ := Atlas.Codes.hexEvenCoordinate_surjective ⟨a, ha⟩
    obtain ⟨q, hq⟩ := d.cover.surjective h
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
    refine ⟨inclusion le_sup_left l, l.property, ?_⟩
    rw [d.cover_compatible, hl, hq, hh]

/-- The actual permutation image contains A₆. -/
theorem alternating_le_range : alternatingGroup (Fin 6) ≤ d.permutation.range := by
  rw [← d.permutationImage_L]
  rintro _ ⟨g, _, rfl⟩
  exact ⟨g, rfl⟩

/-- An element normalizes a flag preimage exactly when its permutation preserves the subspace. -/
theorem flag_normalizer_iff (P : Submodule (ZMod 2) Natural)
    (g : (L ⊔ T : Subgroup G)) :
    g.val ∈ normalizer (flagPreimage d.naturalMap P : Set G) ↔
      d.permutation g ∈ subspaceStabilizer naturalAction P := by
  constructor
  · intro hg w
    obtain ⟨v, hv⟩ := d.naturalMap_surjective (Multiplicative.ofAdd w)
    have hv' : (d.naturalMap v).toAdd = w := congrArg Multiplicative.toAdd hv
    rw [← hv', ← d.conjugation]
    rw [← mem_flagPreimage_iff, ← mem_flagPreimage_iff]
    exact ((mem_normalizer_iff.mp hg) v.val).symm
  · intro hg
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      let v : V := ⟨x, flagPreimage_le _ _ hx⟩
      have hp : (d.naturalMap v).toAdd ∈ P := (mem_flagPreimage_iff _ _ v).mp hx
      have hc := (hg (d.naturalMap v).toAdd).mpr hp
      rw [← d.conjugation] at hc
      exact (mem_flagPreimage_iff _ _ _).mpr hc
    · intro hx
      have hv : x ∈ V :=
        (mem_normalizer_iff.mp (d.normalizes_V g.property) x).mpr
          (flagPreimage_le _ _ hx)
      let v : V := ⟨x, hv⟩
      have hc : (d.naturalMap (V.normalizerMonoidHom
          ⟨g.val, d.normalizes_V g.property⟩ v)).toAdd ∈ P :=
        (mem_flagPreimage_iff _ _ _).mp hx
      rw [d.conjugation] at hc
      exact (mem_flagPreimage_iff _ _ v).mpr ((hg _).mp hc)

/-- The relative normalizer maps onto the actual point stabilizer in the image of LT. -/
theorem parabolic_image : d.permutationImage (parabolic L T V₁) =
    d.permutation.range ⊓ subspaceStabilizer naturalAction d.point := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    refine ⟨MonoidHom.mem_range.mpr ⟨g, rfl⟩, ?_⟩
    apply (d.flag_normalizer_iff d.point g).mp
    rw [← d.line_eq]
    exact hg.2
  · rintro a ⟨ha, hp⟩
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp ha
    refine ⟨g, ⟨g.property, ?_⟩, rfl⟩
    rw [d.line_eq]
    exact (d.flag_normalizer_iff d.point g).mpr hp

/-- The given Sylow subgroup preserves the two actual quotient subspaces. -/
theorem sylow_flag_stable :
    d.permutationImage T ≤ subspaceStabilizer naturalAction d.point ∧
      d.permutationImage T ≤ subspaceStabilizer naturalAction d.hyperplane := by
  constructor
  · rintro _ ⟨g, hg, rfl⟩
    apply (d.flag_normalizer_iff d.point g).mp
    rw [← d.line_eq]
    exact d.line_stable hg
  · rintro _ ⟨g, hg, rfl⟩
    apply (d.flag_normalizer_iff d.hyperplane g).mp
    rw [← d.seed_eq]
    exact d.seed_stable hg

/-- The image of an ambient subgroup on the genuine natural section. -/
def naturalImage (B : Subgroup G) : Submodule (ZMod 2) Natural :=
  AddSubgroup.toZModSubmodule 2
    (AddSubgroup.toSubgroup.symm ((B.subgroupOf V).map d.naturalMap))

theorem mem_naturalImage (B : Subgroup G) (w : Natural) :
    w ∈ d.naturalImage B ↔ ∃ v : V, v.val ∈ B ∧ (d.naturalMap v).toAdd = w := by
  rfl

theorem point_le_naturalImage_line : d.point ≤ d.naturalImage V₁ := by
  intro w hw
  obtain ⟨v, hv⟩ := d.naturalMap_surjective (Multiplicative.ofAdd w)
  have he : (d.naturalMap v).toAdd = w := congrArg Multiplicative.toAdd hv
  refine (d.mem_naturalImage V₁ w).mpr ⟨v, ?_, he⟩
  rw [d.line_eq]
  exact (mem_flagPreimage_iff _ _ v).mpr (he.symm ▸ hw)

theorem displacement_le_naturalImage_commutator (A : Subgroup G) :
    subspaceCommutator naturalAction d.hyperplane (d.permutationImage A) ≤
      d.naturalImage ⁅A, V₃⁆ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ⟨g, hg, rfl⟩, w, hw, rfl⟩
  obtain ⟨v, hv⟩ := d.naturalMap_surjective (Multiplicative.ofAdd w)
  have he : (d.naturalMap v).toAdd = w := congrArg Multiplicative.toAdd hv
  have hv3 : v.val ∈ V₃ := by
    rw [d.seed_eq]
    exact (mem_flagPreimage_iff _ _ v).mpr (he.symm ▸ hw)
  let c : V := V.normalizerMonoidHom ⟨g.val, d.normalizes_V g.property⟩ v * v⁻¹
  refine (d.mem_naturalImage _ _).mpr ⟨c, ?_, ?_⟩
  · exact commutator_mem_commutator hg hv3
  · change (d.naturalMap
      (V.normalizerMonoidHom ⟨g.val, d.normalizes_V g.property⟩ v * v⁻¹)).toAdd = _
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
    change (d.naturalMap (V.normalizerMonoidHom
      ⟨g.val, d.normalizes_V g.property⟩ v)).toAdd - (d.naturalMap v).toAdd = _
    rw [d.conjugation, he]

theorem naturalImage_mono {A B : Subgroup G} (h : A ≤ B) :
    d.naturalImage A ≤ d.naturalImage B := by
  intro w hw
  obtain ⟨v, hv, he⟩ := (d.mem_naturalImage A w).mp hw
  exact (d.mem_naturalImage B w).mpr ⟨v, h hv, he⟩

/-- Lift section generation using that the whole kernel lies in the line preimage. -/
theorem seed_le_of_naturalImage (B : Subgroup G) (hline : V₁ ≤ B)
    (hseed : d.hyperplane ≤ d.naturalImage B) : V₃ ≤ B := by
  intro v hv
  let x : V := ⟨v, d.seed_le hv⟩
  have hx : (d.naturalMap x).toAdd ∈ d.hyperplane := by
    apply (mem_flagPreimage_iff _ _ x).mp
    rwa [← d.seed_eq]
  obtain ⟨y, hy, he⟩ := (d.mem_naturalImage B _).mp (hseed hx)
  have hk : d.naturalMap (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, show d.naturalMap x = d.naturalMap y from he.symm]
    exact mul_inv_cancel _
  have hxy : ((x * y⁻¹ : V) : G) ∈ V₁ := by
    rw [d.line_eq]
    apply (mem_flagPreimage_iff _ _ (x * y⁻¹)).mpr
    rw [hk]
    exact d.point.zero_mem
  have hm := B.mul_mem (hline hxy) hy
  simpa only [coe_mul, coe_inv, inv_mul_cancel_right] using hm

/-- Linear generation by the actual action lifts to an ambient subgroup commutator. -/
theorem seed_le_commutator_sup_of_displacement (A : Subgroup G)
    (hgen : d.hyperplane ≤
      subspaceCommutator naturalAction d.hyperplane (d.permutationImage A) ⊔ d.point) :
    V₃ ≤ ⁅A, V₃⁆ ⊔ V₁ := by
  apply d.seed_le_of_naturalImage _ le_sup_right
  exact hgen.trans (sup_le
    ((d.displacement_le_naturalImage_commutator A).trans
      (d.naturalImage_mono le_sup_left))
    (d.point_le_naturalImage_line.trans (d.naturalImage_mono le_sup_right)))

/-- Stabilization of the section lifts through its actual inverse image. -/
theorem normalizes_seed_of_image (A : Subgroup G) (hA : A ≤ L ⊔ T)
    (hstable : d.permutationImage A ≤ subspaceStabilizer naturalAction d.hyperplane) :
    A ≤ normalizer (V₃ : Set G) := by
  intro a ha
  rw [d.seed_eq]
  apply (d.flag_normalizer_iff d.hyperplane ⟨a, hA ha⟩).mpr
  exact hstable ⟨⟨a, hA ha⟩, ha, rfl⟩

variable [Finite G]

/-- No kernel restriction is needed to send the supplied Sylow subgroup to a Sylow image. -/
theorem image_sylow : ∃ Q : Sylow 2 d.permutation.range,
    (Q : Subgroup d.permutation.range).map d.permutation.range.subtype =
      d.permutationImage T := by
  refine ⟨d.sylow.mapSurjective d.permutation.rangeRestrict_surjective, ?_⟩
  rw [Sylow.coe_mapSurjective, map_map, d.sylow_eq]
  rfl

/-- Finite residuals commute with the permutation image of every subgroup of LT. -/
theorem permutationImage_residual (A : Subgroup G) (hA : A ≤ L ⊔ T) :
    d.permutationImage (residual A) = residual (d.permutationImage A) := by
  have he : (residual A).subgroupOf (L ⊔ T) = residual (A.subgroupOf (L ⊔ T)) := by
    apply map_injective (L ⊔ T).subtype_injective
    rw [map_subgroupOf_eq_of_le ((residual_le A).trans hA)]
    change residual A = ((pResidual 2 (A.subgroupOf (L ⊔ T))).map
      (A.subgroupOf (L ⊔ T)).subtype).map (L ⊔ T).subtype
    rw [map_embedded_pResidual, map_subgroupOf_eq_of_le hA]
    rfl
  unfold permutationImage
  rw [he]
  exact map_embedded_pResidual 2 _ _

/-- L₁ maps to the residual of the point stabilizer, rather than to the whole stabilizer. -/
theorem one_image : d.permutationImage (one L T V₁) =
    residual (d.permutation.range ⊓ subspaceStabilizer naturalAction d.point) := by
  rw [one, d.permutationImage_residual _ (show parabolic L T V₁ ≤ L ⊔ T from inf_le_left), d.parabolic_image]

end
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.NaturalSetup
