module
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.SupercriticalAction
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.TernaryObstruction
public import Theory.GroupTheory.Fitting.Centralizer

/-!
# Closing the nontrivial-action case of F.6.16

When both local two-residuals have nontrivial images, F.6.7 and F.6.8
make the actual matrix-action kernel solvable. Its three-residual
centralizes the ambient three-core. Fitting self-centralization and the
trivial prime-to-three core therefore make that kernel a three-group.
The quaternion obstruction forces the two local images to coincide;
their common two-perfect image has order three. Thus the whole
residual, including the actual kernel, is a three-group.

The supercritical witness and kernel-centralization input are constructed
in SupercriticalAction. Proving nontriviality from the two local
noncontainments remains the rank-two action step of source assembly.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
Lemma F.6.16, printed pp.308–309 (1 March 2004 manuscript).
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterF.Noncyclic
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

private theorem normal_three_group_of_residual_centralizes
    (hcore : pPrimeCore 3 G = ⊥) (W : Subgroup G) [W.Normal]
    (hs : Group.IsSolvable W)
    (hc : ((pResidual 3 W).map W.subtype) ≤ centralizer (pCore 3 G : Set G)) :
    IsPGroup 3 W := by
  have hWcore : pPrimeCore 3 W = ⊥ := by
    apply map_injective W.subtype_injective
    rw [Subgroup.map_bot]
    exact eq_bot_iff.mpr ((pPrimeCore_map_subtype_le_pPrimeCore_of_normal 3 W).trans hcore.le)
  have hF : fittingSubgroup W = pCore 3 W := Fitting_eq_pcore W 3 hWcore
  have hself : centralizer (pCore 3 W : Set W) ≤ pCore 3 W := by
    rw [← hF]
    exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hs
  have hPW : (pCore 3 W).map W.subtype ≤ pCore 3 G :=
    le_sSup ⟨inferInstance, pCore_isPGroup.map W.subtype⟩
  have hres : pResidual 3 W ≤ pCore 3 W := by
    intro x hx
    apply hself
    intro y hy
    exact Subtype.ext ((hc (mem_map_of_mem W.subtype hx)) y (hPW (mem_map_of_mem W.subtype hy)))
  let q := QuotientGroup.mk' (pResidual 3 W)
  have hker : IsPGroup 3 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.to_le hres
  have htop := ((isPGroup_quotient_pResidual (G := W) 3).to_subgroup ⊤).comap_of_ker_isPGroup q hker
  rw [comap_top] at htop
  exact htop.of_equiv Subgroup.topEquiv

/-- The actual action kernel is a three-group when both local images are
nontrivial. The solvability and self-centralization hypotheses are proved. -/
theorem ternary_kernel_isThreeGroup
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hprime : pPrimeCore 3 G = ⊥)
    (f : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (hc : ((pResidual 3 f.ker).map f.ker.subtype) ≤ centralizer (pCore 3 G : Set G))
    (h₁ : ((pResidual 2 G₁).map G₁.subtype).map f ≠ ⊥)
    (h₂ : ((pResidual 2 G₂).map G₂.subtype).map f ≠ ⊥) :
    IsPGroup 3 f.ker := by
  have hi (M : Subgroup G) (hne : ((pResidual 2 M).map M.subtype).map f ≠ ⊥) :
      ¬ (pResidual 2 M).map M.subtype ≤ f.ker := by
    intro hm
    apply hne
    exact eq_bot_iff.mpr (by
      rintro _ ⟨x, hx, rfl⟩
      exact mem_bot.mpr (hm hx))
  have hW₁ := (h.left_subnormal_core_iff_not_residual_le f.ker
    (Normal.isSubnormal inferInstance)).mpr (hi G₁ h₁)
  have hW₂ := (h.right_subnormal_core_iff_not_residual_le f.ker
    (Normal.isSubnormal inferInstance)).mpr (hi G₂ h₂)
  have hs : Group.IsSolvable f.ker :=
    odd_order_theorem _ (odd_card_normal_of_local_intersections h hcore f.ker hW₁ hW₂)
  exact normal_three_group_of_residual_centralizes hprime f.ker hs hc

/-- Nontrivial images of both local residuals force the entire residual to be
a three-group, using the concrete matrix obstruction and the actual kernel. -/
theorem residual_isThreeGroup_of_nontrivial_ternary_images
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hprime : pPrimeCore 3 G = ⊥)
    (f : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (hc : ((pResidual 3 f.ker).map f.ker.subtype) ≤ centralizer (pCore 3 G : Set G))
    (h₁ : ((pResidual 2 G₁).map G₁.subtype).map f ≠ ⊥)
    (h₂ : ((pResidual 2 G₂).map G₂.subtype).map f ≠ ⊥) :
    IsPGroup 3 (pResidual 2 G) := by
  have he := ternary_local_residual_images_eq h hcore f h₁ h₂
  have himage : (pResidual 2 G).map f = ((pResidual 2 G₁).map G₁.subtype).map f := by
    rw [h.twoResidual_eq_sup, Subgroup.map_sup, ← he, sup_idem]
  have hperfect := (isPPerfect_embedded_pResidual 2 G₁).of_surjective
    (f.subgroupMap _) (f.subgroupMap_surjective _)
  have hcard : Nat.card (((pResidual 2 G₁).map G₁.subtype).map f) = 3 := by
    rcases Matrix.GeneralLinearGroup.three_twoPerfect_subgroup _ hperfect h₁ with hcard | heq
    · exact hcard
    · exact (no_ternary_image_containing_specialLinear h hcore f
        (heq ▸ map_le_range _ _) h₁ h₂).elim
  have hpim : IsPGroup 3 ((pResidual 2 G).map f) := by
    rw [himage]
    exact IsPGroup.of_card (n := 1) hcard
  have hpker := ternary_kernel_isThreeGroup h hcore hprime f hc h₁ h₂
  exact ((hpim.comap_of_ker_isPGroup f hpker).to_le
    (le_comap_map f (pResidual 2 G)))

/-- Application to the literal supercritical Frattini representation.
Only the local nontrivial-image assertions remain; the kernel hypothesis
is discharged by the supercritical construction. -/
theorem residual_isThreeGroup_of_supercritical_images
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hprime : pPrimeCore 3 G = ⊥) (hr : primeRank 3 G ≤ 2)
    (X : Subgroup (pCore 3 G)) (hX : IsSupercriticalPSubgroup 3 X)
    (himages : letI : X.Characteristic := hX.characteristic
      ∀ j : MulAut (X ⧸ frattini X) →*
          Matrix.GeneralLinearGroup (Fin 2) (ZMod 3), Function.Injective j →
        let f := j.comp ((quotientAut (frattini X)).comp
          ((MulAut.characteristic X).comp (MulAut.conjNormal : G →* MulAut (pCore 3 G))))
        ((pResidual 2 G₁).map G₁.subtype).map f ≠ ⊥ ∧
        ((pResidual 2 G₂).map G₂.subtype).map f ≠ ⊥) :
    IsPGroup 3 (pResidual 2 G) := by
  let : X.Characteristic := hX.characteristic
  obtain ⟨j, hj, hc⟩ := supercritical_ternary_action hr X hX
  obtain ⟨h₁, h₂⟩ := himages j hj
  exact residual_isThreeGroup_of_nontrivial_ternary_images h hcore hprime _ hc h₁ h₂

end CFSG.Quasithin.ChapterF.Noncyclic
