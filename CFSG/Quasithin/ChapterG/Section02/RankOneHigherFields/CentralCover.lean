module

public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Reduction
public import Theory.GroupTheory.PResidual.FaithfulSylowCover

/-!
# Eliminating the central kernel in higher-field G.2.3

For the original marked conjugator, form P=WWᵍ and the literal quotient I/P.
The star projection factors through this quotient with central two-kernel S/P.
Its restriction to U+ is faithful. Thus the preceding starred commutator
identity lifts to U+=[U+,L₁+]≤L+. The supplement I=LU gives I+=L+, so the
source hypothesis L=O²(L) makes I+ two-perfect. The faithful U+ complements
the kernel in a Sylow preimage; transfer forces that kernel to be trivial.

The final subgroup and ordered-product identities retain only U≤T, I*=L*,
the actual Sylow witness for U* inside L*, and [U*,L₁*]=U*. These earlier
source outputs remain with the starred branch and final assembly owner.
No global complement, central-kernel vanishing, or Gaschütz theorem is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.3(3), printed pp.333–334, PDF pp.344–345.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields
open Setup
variable {G : Type*} [Group G] [Finite G]
variable {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g : G}

/-- The literal image of an ambient subgroup in I/P. -/
def productImage (D : Setup G) (g : G)
    [((WProduct D g).subgroupOf (D.I g)).Normal] (A : Subgroup G) :
    Subgroup (D.I g ⧸ (WProduct D g).subgroupOf (D.I g)) :=
  (A.subgroupOf (D.I g)).map (QuotientGroup.mk' ((WProduct D g).subgroupOf (D.I g)))

namespace Hypothesis
variable (d : Hypothesis D F n g) (hUT : D.U ≤ D.T)
  (hstar : D.star (D.I g) = D.star D.L)
include d

omit d [Finite G] [Field F] [Finite F] in
private theorem S_subgroupOf : (D.S g).subgroupOf (D.I g) = pCore 2 (D.I g) :=
  comap_map_eq_self_of_injective (D.I g).subtype_injective _

/-- The normal product lies in the original star kernel. -/
theorem product_le_star_ker :
    (WProduct D g).subgroupOf (D.I g) ≤ (d.IStarProjection hUT hstar).ker := by
  rw [d.IStarProjection_ker hUT hstar, ← S_subgroupOf]
  exact comap_mono (d.WProduct_le_S hUT hstar.ge)

variable [((WProduct D g).subgroupOf (D.I g)).Normal]

/-- The literal star map factors through I/P. -/
def productStarProjection :
    (D.I g ⧸ (WProduct D g).subgroupOf (D.I g)) →* D.star D.L :=
  QuotientGroup.lift _ (d.IStarProjection hUT hstar) (d.product_le_star_ker hUT hstar)

theorem productStarProjection_mk (i : D.I g) :
    d.productStarProjection hUT hstar
      (QuotientGroup.mk' ((WProduct D g).subgroupOf (D.I g)) i) =
        d.IStarProjection hUT hstar i := rfl

/-- Every original starred element has a representative in I/P. -/
theorem productStarProjection_surjective :
    Function.Surjective (d.productStarProjection hUT hstar) := by
  intro x
  obtain ⟨i, hi⟩ := d.IStarProjection_surjective hUT hstar x
  exact ⟨QuotientGroup.mk' _ i, hi⟩

/-- The central-cover kernel is precisely S/P. -/
theorem productStarProjection_ker :
    (d.productStarProjection hUT hstar).ker = productImage D g (D.S g) := by
  rw [productStarProjection, QuotientGroup.ker_lift, d.IStarProjection_ker hUT hstar]
  rw [productImage, S_subgroupOf]

theorem productStarProjection_central :
    (d.productStarProjection hUT hstar).ker ≤
      center (D.I g ⧸ (WProduct D g).subgroupOf (D.I g)) := by
  rw [d.productStarProjection_ker hUT hstar]
  exact d.image_S_le_center_productQuotient hUT hstar.ge

theorem productStarProjection_kernel_isPGroup :
    IsPGroup 2 (d.productStarProjection hUT hstar).ker := by
  rw [d.productStarProjection_ker hUT hstar, productImage, S_subgroupOf]
  exact pCore_isPGroup.map _

/-- The factored map has exactly the original ambient starred images. -/
theorem productStarProjection_map (A : Subgroup G) (hA : A ≤ D.I g) :
    ((productImage D g A).map (d.productStarProjection hUT hstar)).map
      (D.star D.L).subtype = D.star A := by
  rw [productImage, map_map, map_map]
  change (A.subgroupOf (D.I g)).map (D.binaryStarRestriction (D.I g) (d.I_le_LT hUT)) = _
  exact binaryStarRestriction_map _ _ _ hA

/-- U/(P∩U) is faithful on the starred image, since U∩S=W≤P. -/
theorem productImage_U_faithful :
    Disjoint (productImage D g D.U) (d.productStarProjection hUT hstar).ker := by
  apply disjoint_def.mpr
  rintro x ⟨u, hu, rfl⟩ hk
  have huks : u ∈ (d.IStarProjection hUT hstar).ker := hk
  rw [d.IStarProjection_ker hUT hstar, ← S_subgroupOf] at huks
  apply (QuotientGroup.eq_one_iff u).mpr
  exact (show D.W g ≤ WProduct D g from le_sup_left) ⟨hu, huks⟩

omit d [Finite G] [Field F] [Finite F] in
private theorem local_le_L : D.L₁ ≤ D.L :=
  (map_subtype_le _).trans inf_le_left

/-- The original local residual still normalizes U in the product quotient. -/
theorem productImage_local_normalizes_U :
    productImage D g D.L₁ ≤ normalizer (productImage D g D.U : Set _) := by
  have hn : D.L₁ ≤ normalizer (D.U : Set G) :=
    (le_sup_left.trans d.setup.local_le).trans (le_normalizer_conjugateSpanBy D.V D.H)
  have hn' : D.L₁.subgroupOf (D.I g) ≤ normalizer (D.U.subgroupOf (D.I g) : Set _) :=
    (comap_mono hn).trans (le_normalizer_comap _)
  exact (map_mono hn').trans ((D.U.subgroupOf (D.I g)).le_normalizer_map _)

include hUT hstar

/-- Starred commutator generation lifts through the faithful U-image. -/
theorem productImage_U_commutator
    (hc : ⁅D.star D.U, D.star D.L₁⁆ = D.star D.U) :
    ⁅productImage D g D.U, productImage D g D.L₁⁆ = productImage D g D.U := by
  apply eq_commutator_of_faithful_image (d.productStarProjection hUT hstar) _ _
    d.productImage_local_normalizes_U (d.productImage_U_faithful hUT hstar)
  apply map_injective (D.star D.L).subtype_injective
  rw [map_commutator, d.productStarProjection_map hUT hstar D.U le_sup_left,
    d.productStarProjection_map hUT hstar D.L₁
      (local_le_L.trans (d.L_le_I_of_star hUT hstar.ge))]
  exact hc

/-- L remains normal after passing to the literal product quotient. -/
theorem productImage_L_normal : (productImage D g D.L).Normal := by
  have hn : (D.L.subgroupOf (D.I g)).Normal :=
    (normal_subgroupOf_iff_le_normalizer (d.L_le_I_of_star hUT hstar.ge)).mpr (by
      rw [d.I_eq_LU_of_star hUT hstar.ge]
      exact sup_le D.L.le_normalizer (hUT.trans d.setup.T_normalizes_L))
  exact hn.map _ (QuotientGroup.mk'_surjective _)

/-- The lifted commutator places U+ inside L+. -/
theorem productImage_U_le_L
    (hc : ⁅D.star D.U, D.star D.L₁⁆ = D.star D.U) :
    productImage D g D.U ≤ productImage D g D.L := by
  let := d.productImage_L_normal hUT hstar
  rw [← d.productImage_U_commutator hUT hstar hc]
  exact (commutator_mono le_rfl (map_mono (comap_mono local_le_L))).trans
    (commutator_le_right (productImage D g D.U) (productImage D g D.L))

/-- The source supplement I=LU now gives I+=L+. -/
theorem productImage_L_eq_top
    (hc : ⁅D.star D.U, D.star D.L₁⁆ = D.star D.U) :
    productImage D g D.L = ⊤ := by
  have he : productImage D g D.L ⊔ productImage D g D.U = ⊤ := by
    unfold productImage
    rw [← Subgroup.map_sup, ← subgroupOf_sup (d.L_le_I_of_star hUT hstar.ge)
      (show D.U ≤ D.I g from le_sup_left), ← d.I_eq_LU_of_star hUT hstar.ge,
      subgroupOf_self, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  rwa [sup_eq_left.mpr (d.productImage_U_le_L hUT hstar hc)] at he

/-- The product quotient inherits the source two-perfectness of L. -/
theorem productQuotient_isPPerfect
    (hc : ⁅D.star D.U, D.star D.L₁⁆ = D.star D.U) :
    IsPPerfect 2 (D.I g ⧸ (WProduct D g).subgroupOf (D.I g)) := by
  let f := (QuotientGroup.mk' ((WProduct D g).subgroupOf (D.I g))).comp
    (inclusion (d.L_le_I_of_star hUT hstar.ge))
  apply ((pResidual_eq_top_iff 2 D.L).mp d.setup.residual).of_surjective f
  intro x
  have hx : x ∈ productImage D g D.L := by
    rw [d.productImage_L_eq_top hUT hstar hc]
    trivial
  obtain ⟨i, hi, he⟩ := hx
  exact ⟨⟨i, hi⟩, he⟩

/-- U+ is a faithful complement to S+ in the Sylow preimage. -/
theorem productQuotient_sylow_supplement (T : Sylow 2 (D.star D.L))
    (hT : (T : Subgroup (D.star D.L)).map (D.star D.L).subtype = D.star D.U) :
    ∃ R : Sylow 2 (D.I g ⧸ (WProduct D g).subgroupOf (D.I g)),
      (R : Subgroup _) = productImage D g D.U ⊔ productImage D g (D.S g) ∧
        Disjoint (productImage D g D.U) (productImage D g (D.S g)) := by
  have hmap : (productImage D g D.U).map (d.productStarProjection hUT hstar) = T := by
    apply map_injective (D.star D.L).subtype_injective
    rw [d.productStarProjection_map hUT hstar D.U le_sup_left, hT]
  obtain ⟨R, hR⟩ := exists_sylow_eq_sup_ker_of_sylow_image
    (d.productStarProjection hUT hstar) (d.productStarProjection_kernel_isPGroup hUT hstar)
    (productImage D g D.U) T hmap
  exact ⟨R, (d.productStarProjection_ker hUT hstar) ▸ hR,
    (d.productStarProjection_ker hUT hstar) ▸ d.productImage_U_faithful hUT hstar⟩

/-- The supplement is a genuine internal complement in the Sylow group. -/
theorem productQuotient_sylow_complement (T : Sylow 2 (D.star D.L))
    (hT : (T : Subgroup (D.star D.L)).map (D.star D.L).subtype = D.star D.U) :
    ∃ R : Sylow 2 (D.I g ⧸ (WProduct D g).subgroupOf (D.I g)),
      productImage D g D.U ≤ R ∧
      ((productImage D g D.U).subgroupOf (R : Subgroup _)).IsComplement'
        ((productImage D g (D.S g)).subgroupOf (R : Subgroup _)) := by
  have hmap : (productImage D g D.U).map (d.productStarProjection hUT hstar) = T := by
    apply map_injective (D.star D.L).subtype_injective
    rw [d.productStarProjection_map hUT hstar D.U le_sup_left, hT]
  obtain ⟨R, hR, hc⟩ := exists_sylow_complement_of_faithful_image
    (d.productStarProjection hUT hstar) (d.productStarProjection_kernel_isPGroup hUT hstar)
    (productImage D g D.U) (d.productImage_U_faithful hUT hstar) T hmap
  exact ⟨R, hR, (d.productStarProjection_ker hUT hstar) ▸ hc⟩

/-- Transfer kills S/P, using the faithful Sylow lift and L=O²(L). -/
theorem productStarProjection_ker_eq_bot (T : Sylow 2 (D.star D.L))
    (hT : (T : Subgroup (D.star D.L)).map (D.star D.L).subtype = D.star D.U)
    (hc : ⁅D.star D.U, D.star D.L₁⁆ = D.star D.U) :
    (d.productStarProjection hUT hstar).ker = ⊥ := by
  apply ker_eq_bot_of_faithful_sylow_image (d.productQuotient_isPPerfect hUT hstar hc)
    (d.productStarProjection hUT hstar) (d.productStarProjection_central hUT hstar)
    (d.productStarProjection_kernel_isPGroup hUT hstar)
    (productImage D g D.U) (d.productImage_U_faithful hUT hstar) T
  apply map_injective (D.star D.L).subtype_injective
  rw [d.productStarProjection_map hUT hstar D.U le_sup_left, hT]

omit [((WProduct D g).subgroupOf (D.I g)).Normal] in
/-- G.2.3(3), conditional only on the preceding starred generation, Sylow
and commutator outputs. The original conjugator g is unchanged. -/
theorem S_eq_WProduct (T : Sylow 2 (D.star D.L))
    (hT : (T : Subgroup (D.star D.L)).map (D.star D.L).subtype = D.star D.U)
    (hc : ⁅D.star D.U, D.star D.L₁⁆ = D.star D.U) :
    D.S g = WProduct D g := by
  let := d.WProduct_normal hUT hstar.ge
  have hz : productImage D g (D.S g) = ⊥ :=
    (d.productStarProjection_ker hUT hstar).symm.trans
      (d.productStarProjection_ker_eq_bot hUT hstar T hT hc)
  have hle : (D.S g).subgroupOf (D.I g) ≤ (WProduct D g).subgroupOf (D.I g) := by
    have he := (Subgroup.map_eq_bot_iff _).mp hz
    simpa only [QuotientGroup.ker_mk'] using he
  apply le_antisymm ?_ (d.WProduct_le_S hUT hstar.ge)
  intro x hx
  exact hle (show (⟨x, pCoreIn_le 2 (D.I g) hx⟩ : D.I g) ∈
    (D.S g).subgroupOf (D.I g) from hx)

omit [((WProduct D g).subgroupOf (D.I g)).Normal] in
/-- The literal ordered product identity in the source, with the original g. -/
theorem S_eq_ordered_product (T : Sylow 2 (D.star D.L))
    (hT : (T : Subgroup (D.star D.L)).map (D.star D.L).subtype = D.star D.U)
    (hc : ⁅D.star D.U, D.star D.L₁⁆ = D.star D.U) :
    (D.S g : Set G) = (D.W g : Set G) * (conjugate (D.W g) g : Set G) := by
  rw [d.S_eq_WProduct hUT hstar T hT hc]
  exact d.WProduct_eq_product hUT hstar.ge

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields
