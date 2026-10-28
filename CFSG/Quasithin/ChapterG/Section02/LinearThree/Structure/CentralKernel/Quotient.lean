module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.Reduction

/-!
# The literal central extension in G.2.5

The quotient is I/P for P = WWᵍWʰ, with the original marked conjugators.
The star map descends to a surjection onto the actual L*. Its kernel is
the image of S, a central two-group. The image of U meets that kernel
trivially, because U∩P = U∩S = W. These definitions let the local root
construction and the residual argument use exactly the same quotient.

Source: Aschbacher–Smith G.2.5(3), printed pp.335–336, referring to
G.2.3, printed pp.333–334. No vanishing of S/P is asserted here.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.CentralKernel
open Setup
variable {G : Type*} [Group G]

abbrev Quotient (D : Setup G) (g h : G)
    [((WProduct D g h).subgroupOf (I D g h)).Normal] :=
  I D g h ⧸ (WProduct D g h).subgroupOf (I D g h)

def projection (D : Setup G) (g h : G)
    [((WProduct D g h).subgroupOf (I D g h)).Normal] :
    I D g h →* Quotient D g h :=
  QuotientGroup.mk' ((WProduct D g h).subgroupOf (I D g h))

/-- Images always use restriction to the original I before quotienting. -/
def image (D : Setup G) (g h : G)
    [((WProduct D g h).subgroupOf (I D g h)).Normal] (A : Subgroup G) :
    Subgroup (Quotient D g h) :=
  (A.subgroupOf (I D g h)).map (projection D g h)

variable [Finite G] {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : Hypothesis D F n g h)

omit [Finite G] in
private theorem core_subgroupOf :
    (S D g h).subgroupOf (I D g h) = pCore 2 (I D g h) := by
  change ((pCore 2 (I D g h)).map (I D g h).subtype).comap (I D g h).subtype = _
  rw [comap_map_eq, (I D g h).ker_subtype, sup_bot_eq]

/-- The product denominator is killed by the original star map. -/
theorem product_le_star_ker (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L) :
    (WProduct D g h).subgroupOf (I D g h) ≤ (d.IStarProjection hUT hstar).ker := by
  rw [d.IStarProjection_ker hUT hstar, ← core_subgroupOf]
  exact comap_mono (d.WProduct_le_S hstar.ge)

variable [((WProduct D g h).subgroupOf (I D g h)).Normal]

/-- Descent of the original star map, with its original target L*. -/
def starMap (hUT : D.U ≤ D.T) (hstar : D.star (I D g h) = D.star D.L) :
    Quotient D g h →* D.star D.L :=
  QuotientGroup.lift _ (d.IStarProjection hUT hstar) (product_le_star_ker d hUT hstar)

theorem starMap_projection (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L) (i : I D g h) :
    starMap d hUT hstar (projection D g h i) = d.IStarProjection hUT hstar i := rfl

theorem starMap_surjective (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L) :
    Function.Surjective (starMap d hUT hstar) :=
  QuotientGroup.lift_surjective_of_surjective _ _
    (d.IStarProjection_surjective hUT hstar) _

theorem starMap_ker (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L) :
    (starMap d hUT hstar).ker = image D g h (S D g h) := by
  rw [starMap, QuotientGroup.ker_lift, d.IStarProjection_ker hUT hstar,
    ← core_subgroupOf]
  rfl

theorem starMap_ker_le_center (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L) :
    (starMap d hUT hstar).ker ≤ center (Quotient D g h) := by
  rw [starMap_ker]
  exact d.image_S_le_center_productQuotient hUT hstar.ge

theorem starMap_ker_isPGroup (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L) :
    IsPGroup 2 (starMap d hUT hstar).ker := by
  rw [starMap_ker]
  exact (isPGroup_pCoreIn 2 (I D g h)).comap_subtype.map (projection D g h)

/-- Mapping an actual quotient image back to Star recovers its original star. -/
theorem map_image_starMap (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L)
    (A : Subgroup G) (hAI : A ≤ I D g h) :
    (image D g h A).map ((D.star D.L).subtype.comp (starMap d hUT hstar)) =
      D.star A := by
  ext x
  constructor
  · rintro ⟨y, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨inclusion (d.I_le_LT hUT) i, hi, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    let i : I D g h := ⟨a, hAI ha⟩
    exact ⟨projection D g h i, ⟨i, ha, rfl⟩, rfl⟩

include d

/-- The image of the original Sylow normalizes the marked radical lift. -/
theorem image_T_normalizes_U :
    image D g h D.T ≤ normalizer (image D g h D.U : Set (Quotient D g h)) := by
  have hn : D.T.subgroupOf (I D g h) ≤
      normalizer (D.U.subgroupOf (I D g h) : Set (I D g h)) :=
    (comap_mono d.T_normalizes_U).trans (D.U.le_normalizer_comap (I D g h).subtype)
  exact (map_mono hn).trans ((D.U.subgroupOf (I D g h)).le_normalizer_map _)

/-- The genuine two-residual of the point stabilizer acts on the U-image. -/
theorem image_L₁_normalizes_U :
    image D g h D.L₁ ≤ normalizer (image D g h D.U : Set (Quotient D g h)) := by
  have hn : D.L₁ ≤ normalizer (D.U : Set G) :=
    (le_sup_left.trans d.setup.local_le).trans (le_normalizer_conjugateSpanBy _ _)
  have hn' : D.L₁.subgroupOf (I D g h) ≤
      normalizer (D.U.subgroupOf (I D g h) : Set (I D g h)) :=
    (comap_mono hn).trans (D.U.le_normalizer_comap (I D g h).subtype)
  exact (map_mono hn').trans ((D.U.subgroupOf (I D g h)).le_normalizer_map _)

/-- Once the U-image is in the L-image, I/P inherits O²(L)=L. The
remaining local action argument must establish the displayed containment. -/
theorem isPPerfect_of_image_U_le_image_L
    (hstar : D.star (I D g h) = D.star D.L)
    (hUL : image D g h D.U ≤ image D g h D.L) :
    IsPPerfect 2 (Quotient D g h) := by
  have hLI := d.L_le_I_of_star hstar.ge
  have hUI : D.U ≤ I D g h := le_sup_left.trans le_sup_left
  have hgen : image D g h D.L ⊔ image D g h D.U = ⊤ := by
    change (D.L.subgroupOf (I D g h)).map (projection D g h) ⊔
      (D.U.subgroupOf (I D g h)).map (projection D g h) = ⊤
    rw [← Subgroup.map_sup, ← subgroupOf_sup hLI hUI, ← d.I_eq_LU_of_star hstar.ge,
      subgroupOf_self]
    exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hLtop : image D g h D.L = ⊤ := by rwa [sup_eq_left.mpr hUL] at hgen
  let f := (projection D g h).comp (inclusion hLI)
  have hf : Function.Surjective f := by
    intro y
    have hy : y ∈ image D g h D.L := hLtop.symm ▸ mem_top y
    obtain ⟨i, hi, he⟩ := hy
    exact ⟨⟨i, hi⟩, he⟩
  exact ((pResidual_eq_top_iff 2 D.L).mp d.setup.residual).of_surjective f hf

/-- The marked U-image embeds into the original star quotient. -/
theorem image_U_disjoint_ker (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L) :
    Disjoint (image D g h D.U) (starMap d hUT hstar).ker := by
  apply disjoint_def.mpr
  rintro x ⟨u, hu, rfl⟩ hk
  have huS : (u : G) ∈ S D g h := by
    have huK : u ∈ (d.IStarProjection hUT hstar).ker := hk
    rw [d.IStarProjection_ker hUT hstar] at huK
    exact ⟨u, huK, rfl⟩
  have huP : (u : G) ∈ WProduct D g h :=
    (show W D g h ≤ WProduct D g h from le_sup_left.trans le_sup_left) ⟨hu, huS⟩
  exact (QuotientGroup.eq_one_iff u).mpr huP

/-- Killing this kernel is precisely the remaining core-product conclusion. -/
theorem core_eq_product_of_ker_eq_bot (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L)
    (hk : (starMap d hUT hstar).ker = ⊥) : S D g h = WProduct D g h := by
  apply le_antisymm _ (d.WProduct_le_S hstar.ge)
  intro s hs
  let sI : I D g h := ⟨s, pCoreIn_le 2 (I D g h) hs⟩
  have him : projection D g h sI ∈ (starMap d hUT hstar).ker := by
    rw [starMap_ker]
    exact mem_map_of_mem (projection D g h) hs
  have he : projection D g h sI = 1 := by simpa only [hk, mem_bot] using him
  exact (QuotientGroup.eq_one_iff sI).mp he

end CFSG.Quasithin.ChapterG.Section02.LinearThree.CentralKernel
