module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Structure.Reduction

/-!
# The literal central extension in G.2.4

The quotient is I/P for P = WWᵍ, with the original marked conjugator.
The star map descends to a surjection onto the actual L*. Its kernel is
the image of S, a central two-group. The image of U meets that kernel
trivially, because U∩P = U∩S = W. These definitions let the local root
construction and the residual argument use exactly the same quotient.

Source: Aschbacher–Smith G.2.4(3), printed pp.334–335, referring to
G.2.3, printed pp.333–334. No vanishing of S/P is asserted here.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive.CentralKernel
open Setup
variable {G : Type*} [Group G]

abbrev Quotient (D : Setup G) (g : G)
    [((WProduct D g).subgroupOf (D.I g)).Normal] :=
  D.I g ⧸ (WProduct D g).subgroupOf (D.I g)

def projection (D : Setup G) (g : G)
    [((WProduct D g).subgroupOf (D.I g)).Normal] :
    D.I g →* Quotient D g :=
  QuotientGroup.mk' ((WProduct D g).subgroupOf (D.I g))

/-- Images always use restriction to the original I before quotienting. -/
def image (D : Setup G) (g : G)
    [((WProduct D g).subgroupOf (D.I g)).Normal] (A : Subgroup G) :
    Subgroup (Quotient D g) :=
  (A.subgroupOf (D.I g)).map (projection D g)

variable [Finite G] {D : Setup G} {g : G} (d : Hypothesis D g)

omit [Finite G] in
private theorem core_subgroupOf :
    (D.S g).subgroupOf (D.I g) = pCore 2 (D.I g) := by
  change ((pCore 2 (D.I g)).map (D.I g).subtype).comap (D.I g).subtype = _
  rw [comap_map_eq, (D.I g).ker_subtype, sup_bot_eq]

/-- The product denominator is killed by the original star map. -/
theorem product_le_star_ker (hstar : D.star (D.I g) = D.star D.L) :
    (WProduct D g).subgroupOf (D.I g) ≤ (d.IStarProjection hstar).ker := by
  rw [d.IStarProjection_ker hstar, ← core_subgroupOf]
  exact comap_mono (d.WProduct_le_S hstar.ge)

variable [((WProduct D g).subgroupOf (D.I g)).Normal]

/-- Descent of the original star map, with its original target L*. -/
def starMap (hstar : D.star (D.I g) = D.star D.L) :
    Quotient D g →* D.star D.L :=
  QuotientGroup.lift _ (d.IStarProjection hstar) (product_le_star_ker d hstar)

theorem starMap_projection (hstar : D.star (D.I g) = D.star D.L) (i : D.I g) :
    starMap d hstar (projection D g i) = d.IStarProjection hstar i := rfl

theorem starMap_surjective (hstar : D.star (D.I g) = D.star D.L) :
    Function.Surjective (starMap d hstar) :=
  QuotientGroup.lift_surjective_of_surjective _ _
    (d.IStarProjection_surjective hstar) _

theorem starMap_ker (hstar : D.star (D.I g) = D.star D.L) :
    (starMap d hstar).ker = image D g (D.S g) := by
  rw [starMap, QuotientGroup.ker_lift, d.IStarProjection_ker hstar,
    ← core_subgroupOf]
  rfl

theorem starMap_ker_le_center (hstar : D.star (D.I g) = D.star D.L) :
    (starMap d hstar).ker ≤ center (Quotient D g) := by
  rw [starMap_ker]
  exact d.image_S_le_center_productQuotient hstar.ge

theorem starMap_ker_isPGroup (hstar : D.star (D.I g) = D.star D.L) :
    IsPGroup 2 (starMap d hstar).ker := by
  rw [starMap_ker]
  exact (isPGroup_pCoreIn 2 (D.I g)).comap_subtype.map (projection D g)

/-- Mapping an actual quotient image back to Star recovers its original star. -/
theorem map_image_starMap (hstar : D.star (D.I g) = D.star D.L)
    (A : Subgroup G) (hAI : A ≤ D.I g) :
    (image D g A).map ((D.star D.L).subtype.comp (starMap d hstar)) =
      D.star A := by
  ext x
  constructor
  · rintro ⟨y, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨inclusion (d.I_le_LT) i, hi, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    let i : D.I g := ⟨a, hAI ha⟩
    exact ⟨projection D g i, ⟨i, ha, rfl⟩, rfl⟩

include d

/-- The image of the original Sylow normalizes the marked radical lift. -/
theorem image_T_normalizes_U :
    image D g D.T ≤ normalizer (image D g D.U : Set (Quotient D g)) := by
  have hn : D.T.subgroupOf (D.I g) ≤
      normalizer (D.U.subgroupOf (D.I g) : Set (D.I g)) :=
    (comap_mono d.setup.toBaseHypothesis.binary_T_normalizes_U).trans (D.U.le_normalizer_comap (D.I g).subtype)
  exact (map_mono hn).trans ((D.U.subgroupOf (D.I g)).le_normalizer_map _)

/-- The genuine two-residual of the point stabilizer acts on the U-image. -/
theorem image_L₁_normalizes_U :
    image D g D.L₁ ≤ normalizer (image D g D.U : Set (Quotient D g)) := by
  have hn : D.L₁ ≤ normalizer (D.U : Set G) :=
    (le_sup_left.trans d.setup.local_le).trans (le_normalizer_conjugateSpanBy _ _)
  have hn' : D.L₁.subgroupOf (D.I g) ≤
      normalizer (D.U.subgroupOf (D.I g) : Set (D.I g)) :=
    (comap_mono hn).trans (D.U.le_normalizer_comap (D.I g).subtype)
  exact (map_mono hn').trans ((D.U.subgroupOf (D.I g)).le_normalizer_map _)

/-- Once the U-image is in the L-image, I/P inherits O²(L)=L. The
remaining local action argument must establish the displayed containment. -/
theorem isPPerfect_of_image_U_le_image_L
    (hstar : D.star (D.I g) = D.star D.L)
    (hUL : image D g D.U ≤ image D g D.L) :
    IsPPerfect 2 (Quotient D g) := by
  have hLI := d.L_le_I_of_star hstar.ge
  have hUI : D.U ≤ D.I g := le_sup_left
  have hgen : image D g D.L ⊔ image D g D.U = ⊤ := by
    change (D.L.subgroupOf (D.I g)).map (projection D g) ⊔
      (D.U.subgroupOf (D.I g)).map (projection D g) = ⊤
    rw [← Subgroup.map_sup, ← subgroupOf_sup hLI hUI, ← d.I_eq_LU_of_star hstar.ge,
      subgroupOf_self]
    exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hLtop : image D g D.L = ⊤ := by rwa [sup_eq_left.mpr hUL] at hgen
  let f := (projection D g).comp (inclusion hLI)
  have hf : Function.Surjective f := by
    intro y
    have hy : y ∈ image D g D.L := hLtop.symm ▸ mem_top y
    obtain ⟨i, hi, he⟩ := hy
    exact ⟨⟨i, hi⟩, he⟩
  exact ((pResidual_eq_top_iff 2 D.L).mp d.setup.residual).of_surjective f hf

/-- The marked U-image embeds into the original star quotient. -/
theorem image_U_disjoint_ker (hstar : D.star (D.I g) = D.star D.L) :
    Disjoint (image D g D.U) (starMap d hstar).ker := by
  apply disjoint_def.mpr
  rintro x ⟨u, hu, rfl⟩ hk
  have huS : (u : G) ∈ D.S g := by
    have huK : u ∈ (d.IStarProjection hstar).ker := hk
    rw [d.IStarProjection_ker hstar] at huK
    exact ⟨u, huK, rfl⟩
  have huP : (u : G) ∈ WProduct D g :=
    (show D.W g ≤ WProduct D g from le_sup_left) ⟨hu, huS⟩
  exact (QuotientGroup.eq_one_iff u).mpr huP

/-- Killing this kernel is precisely the remaining core-product conclusion. -/
theorem core_eq_product_of_ker_eq_bot (hstar : D.star (D.I g) = D.star D.L)
    (hk : (starMap d hstar).ker = ⊥) : D.S g = WProduct D g := by
  apply le_antisymm _ (d.WProduct_le_S hstar.ge)
  intro s hs
  let sI : D.I g := ⟨s, pCoreIn_le 2 (D.I g) hs⟩
  have him : projection D g sI ∈ (starMap d hstar).ker := by
    rw [starMap_ker]
    exact mem_map_of_mem (projection D g) hs
  have he : projection D g sI = 1 := by simpa only [hk, mem_bot] using him
  exact (QuotientGroup.eq_one_iff sI).mp he

end CFSG.Quasithin.ChapterG.Section02.AlternatingFive.CentralKernel
