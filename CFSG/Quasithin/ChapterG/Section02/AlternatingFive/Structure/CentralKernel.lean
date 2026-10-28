module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Structure.CentralQuotient
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.TerminalReduction
public import Theory.GroupTheory.PResidual.CentralSylowFrattini

/-!
# Eliminating the central two-kernel in G.2.4

In I/P, where P=WWᵍ, the U-image maps faithfully into L*. The Borel
commutator calculation therefore lifts and places U⁺ in L⁺. Thus I/P is
two-perfect. A Sylow subgroup containing U⁺ has the same image as U⁺;
transfer puts the central kernel in its Frattini subgroup, so U⁺ is the
whole Sylow subgroup. Faithfulness on U⁺ kills the central two-kernel.

This completes the group-theoretic implication from the starred Borel,
generation, and commutator inputs. Their orthogonal-model construction
remains separate; the theorem below is not an unconditional G.2.4 claim.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(3), printed p.334, referring to G.2.3, printed pp.333–334.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive.CentralKernel
open Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}
  (d : Hypothesis D g) [((WProduct D g).subgroupOf (D.I g)).Normal]
include d

/-- The Sylow T normalizes the original two-residual, hence so does U. -/
theorem image_U_normalizes_L₁ :
    image D g D.U ≤ normalizer (image D g D.L₁ : Set (Quotient D g)) := by
  have hn : D.U ≤ normalizer (D.L₁ : Set G) :=
    d.setup.U_normal_in_T.1.trans (T_normalizes_L₁ d.setup.toBaseHypothesis)
  have hn' : D.U.subgroupOf (D.I g) ≤
      normalizer (D.L₁.subgroupOf (D.I g) : Set (D.I g)) :=
    (comap_mono hn).trans (D.L₁.le_normalizer_comap (D.I g).subtype)
  exact (map_mono hn').trans ((D.L₁.subgroupOf (D.I g)).le_normalizer_map _)

/-- The star commutator lifts because U⁺ meets the actual central kernel trivially. -/
theorem image_U_eq_commutator_of_star (hstar : D.star (D.I g) = D.star D.L)
    (hcomm : ⁅D.star D.U, D.star D.L₁⁆ = D.star D.U) :
    image D g D.U = ⁅image D g D.U, image D g D.L₁⁆ := by
  let f := starMap d hstar
  let f₀ := (D.star D.L).subtype.comp f
  have hL₁I : D.L₁ ≤ D.I g :=
    ((map_subtype_le _).trans inf_le_left).trans (d.L_le_I_of_star hstar.ge)
  have hCA : ⁅image D g D.U, image D g D.L₁⁆ ≤ image D g D.U :=
    le_normalizer_iff_commutator_le_left.mp (image_L₁_normalizes_U d)
  have hmapA : (image D g D.U).map f₀ = D.star D.U :=
    map_image_starMap d hstar D.U le_sup_left
  have hmapC : (⁅image D g D.U, image D g D.L₁⁆).map f₀ = D.star D.U := by
    rw [map_commutator, hmapA, map_image_starMap d hstar D.L₁ hL₁I, hcomm]
  apply le_antisymm _ hCA
  intro x hx
  have hfx : f₀ x ∈ (⁅image D g D.U, image D g D.L₁⁆).map f₀ := by
    rw [hmapC, ← hmapA]
    exact mem_map_of_mem f₀ hx
  obtain ⟨c, hc, he⟩ := hfx
  have hk : c⁻¹ * x ∈ f.ker := by
    apply Subtype.ext
    change f₀ (c⁻¹ * x) = 1
    rw [map_mul, map_inv, he, inv_mul_cancel]
  have hcx : c⁻¹ * x = 1 := disjoint_def.mp (image_U_disjoint_ker d hstar)
    ((image D g D.U).mul_mem ((image D g D.U).inv_mem (hCA hc)) hx) hk
  exact (inv_mul_eq_one.mp hcx) ▸ hc

/-- Full Borel commutators place the marked lift inside the image of L. -/
theorem image_U_le_image_L_of_star (hstar : D.star (D.I g) = D.star D.L)
    (hcomm : ⁅D.star D.U, D.star D.L₁⁆ = D.star D.U) :
    image D g D.U ≤ image D g D.L := by
  rw [image_U_eq_commutator_of_star d hstar hcomm]
  exact (le_normalizer_iff_commutator_le_right.mp (image_U_normalizes_L₁ d)).trans
    (map_mono (comap_mono ((map_subtype_le _).trans inf_le_left)))

/-- Transfer removes S/P using the actual starred Sylow, without a global
splitting assumption or a classification of central covers. -/
theorem starMap_ker_eq_bot_of_borel (hstar : D.star (D.I g) = D.star D.L)
    (hSylow : ∃ P : Sylow 2 (D.star D.L),
      (P : Subgroup (D.star D.L)).map (D.star D.L).subtype = D.star D.U)
    (hcomm : ⁅D.star D.U, D.star D.L₁⁆ = D.star D.U) :
    (starMap d hstar).ker = ⊥ := by
  let f := starMap d hstar
  let A := image D g D.U
  have hres : IsPPerfect 2 (Quotient D g) :=
    isPPerfect_of_image_U_le_image_L d hstar (image_U_le_image_L_of_star d hstar hcomm)
  obtain ⟨P, hP⟩ := hSylow
  have hAP : A.map f = (P : Subgroup (D.star D.L)) := by
    apply map_injective (D.star D.L).subtype_injective
    rw [map_map, map_image_starMap d hstar D.U le_sup_left, hP]
  have hpA : IsPGroup 2 A := d.setup.U_isPGroup.comap_subtype.map (projection D g)
  obtain ⟨R, hAR⟩ := hpA.exists_le_sylow
  have hcover : (R : Subgroup (Quotient D g)).map f ≤ A.map f := by
    rw [hAP]
    exact (P.is_maximal' (R.isPGroup'.map f) (hAP ▸ map_mono hAR)).le
  have he : A = (R : Subgroup (Quotient D g)) :=
    sylow_eq_of_map_eq_of_central_kernel_of_isPPerfect hres R f
      (starMap_ker_le_center d hstar) A hAR hcover
  apply bot_unique
  intro x hx
  have hxR := (starMap_ker_isPGroup d hstar).le_sylow_of_normal R hx
  exact disjoint_def.mp (image_U_disjoint_ker d hstar)
    (show x ∈ A by rw [he]; exact hxR) hx

end CFSG.Quasithin.ChapterG.Section02.AlternatingFive.CentralKernel

namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Hypothesis
open Setup CentralKernel
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G} (d : Hypothesis D g)
include d

/-- G.2.4(3) from the precise outstanding starred local-group calculations. -/
theorem S_eq_WProduct_of_borel (hstar : D.star (D.I g) = D.star D.L)
    (hSylow : ∃ P : Sylow 2 (D.star D.L),
      (P : Subgroup (D.star D.L)).map (D.star D.L).subtype = D.star D.U)
    (hcomm : ⁅D.star D.U, D.star D.L₁⁆ = D.star D.U) :
    D.S g = WProduct D g := by
  let := d.WProduct_normal hstar.ge
  exact core_eq_product_of_ker_eq_bot d hstar
    (starMap_ker_eq_bot_of_borel d hstar hSylow hcomm)

/-- The same implication gives the literal ordered set product WWᵍ. -/
theorem S_eq_product_of_borel (hstar : D.star (D.I g) = D.star D.L)
    (hSylow : ∃ P : Sylow 2 (D.star D.L),
      (P : Subgroup (D.star D.L)).map (D.star D.L).subtype = D.star D.U)
    (hcomm : ⁅D.star D.U, D.star D.L₁⁆ = D.star D.U) :
    (D.S g : Set G) = (D.W g : Set G) * (conjugate (D.W g) g : Set G) := by
  rw [d.S_eq_WProduct_of_borel hstar hSylow hcomm]
  exact d.WProduct_eq_product hstar.ge

end CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Hypothesis
