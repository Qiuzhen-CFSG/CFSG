module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.CoveredZero
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.FirstFlagNormalizer
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.CoveredResidual
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationCoveredComparison
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.NormalizerAction

/-!
# Normalizing the full covered point residual

The original flag normalizer has two-residual L₁ = O^{3′}(C_L(z)).
The central residual L₀ lies in it. Its section centralizer normalizes
L₀, since L₀ is two-perfect and the relevant two-core lies in T.
Frattini factorization reduces the rest of N_G(L₁) to the normalizer of
O₂(L₁T). The proved augmentation Baumann comparison controls this last
normalizer. Together with N_G(L₀)=N_G(L), this proves the original
13.2.2(9) bound on L₁ without changing the five-dimensional module.

The subgroup O₂(L₁T) is used only here; it is not identified with the
original first action core R₁. CoveredSolvableReduction consumes the bound
to exclude full L₁ from the remaining relatively normal residual case.
The section-centralizer argument adapts EarlierResidual/CoveredNormalizer
with the actual augmentation hypotheses.

Source: Aschbacher--Smith 13.2.2(8)--(9), pp.877--878;
13.3.9, p.887; A.4.2(4)--(5), p.57.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Solvable Nonsolvable ChapterA.Section04
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem sectionCentralizer_normalizes_residual
    (X Z : Subgroup G) (hZX : Z ≤ X) (hp : IsPPerfect 2 Z)
    (hn : X.pCoreIn 2 ≤ normalizer (Z : Set G)) :
    twoSectionCentralizer X (normalizer (X : Set G)) ≤ normalizer (Z : Set G) := by
  let Q := X.pCoreIn 2
  let C := twoSectionCentralizer X (normalizer (X : Set G))
  have hCQ : C ≤ normalizer (Q : Set G) :=
    (twoSectionCentralizer_le_normalizer _ _).trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hCZQ : C ≤ normalizer ((Z ⊔ Q : Subgroup G) : Set G) := by
    apply le_normalizer_iff.mpr
    intro c hc z hz
    have hm : (Z ⊔ Q).map (MulAut.conj c).toMonoidHom ≤ Z ⊔ Q := by
      rw [Subgroup.map_sup]
      apply sup_le
      · rintro _ ⟨z,hz,rfl⟩
        have hcomm : ⁅c,z⁆ ∈ Q := hc.2.2 z (hZX hz)
        have hh := (Z ⊔ Q).mul_mem (mem_sup_right hcomm) (mem_sup_left hz)
        change c*z*c⁻¹ ∈ Z ⊔ Q
        simpa only [commutatorElement_def, mul_assoc,
          inv_mul_cancel, mul_one] using hh
      · rintro _ ⟨q,hq,rfl⟩
        exact mem_sup_right ((mem_normalizer_iff.mp (hCQ hc) q).mp hq)
    exact hm (mem_map_of_mem (MulAut.conj c).toMonoidHom hz)
  have he : residual (Z ⊔ Q) = Z :=
    embedded_pResidual_join_pGroup Z Q hp (isPGroup_pCoreIn 2 X) hn
  rw [←he]
  exact hCZQ.trans (normalizer_le_residual_normalizer _)

/-- The full covered L₁ is the residual of the original flag normalizer. -/
theorem covered_firstFlagNormalizer_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    one L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) =
      firstCentralizerResidual L z.val := by
  have he : parabolic L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) =
      firstCentralizerResidual L z.val ⊔ (T : Subgroup G) :=
    (first_flag_normalizer_eq_centralizer h structural D m z hzT hzL).trans
      (covered_augmentation_point_parabolic D m hc z hzT hzL).symm
  change (pResidual 2 (parabolic L (T : Subgroup G)
    (V ⊓ omegaOneCenterAmbient (T : Subgroup G)))).map
    (parabolic L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G))).subtype = _
  rw [he]
  exact embedded_pResidual_join_pGroup _ _ (firstCentralizerResidual_twoPerfect L z.val)
    T.isPGroup' (firstCentralizerResidual_sylow_normalizes D hzT)

/-- The central cubic residual lies in the actual covered point residual. -/
theorem covered_zero_le_firstResidual
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hzL : z.val ∉ centralizer (L : Set G)) :
    zero L ≤ firstCentralizerResidual L z.val := by
  have hZC : zero L ≤ L ⊓ centralizer ({z.val} : Set G) :=
    le_inf (zero_le L) ((covered_zero_centralizes_core D m).trans
      (centralizer_le (Set.singleton_subset_iff.mpr z.property)))
  have hp : IsPPerfect 2 (zero L) := isPPerfect_embedded_pResidual 2 _
  have he : residual (zero L) = zero L := by
    change (pResidual 2 (zero L)).map (zero L).subtype = _
    rw [(pResidual_eq_top_iff 2 _).mpr hp,←MonoidHom.range_eq_map,range_subtype]
  rw [firstCentralizerResidual_eq,
    ←twoResidual_eq_primeToResidual_three (covered_augmentation_point_twoThree D m hc z hzL)]
  exact he ▸ embedded_pResidual_mono 2 hZC

/-- The original covered L₁ normalizer bound on the augmentation module. -/
theorem covered_firstResidual_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    normalizer (firstCentralizerResidual L z.val : Set G) ≤ normalizer (L : Set G) := by
  let B := firstCentralizerResidual L z.val
  have hTB : (T : Subgroup G) ≤ normalizer (B : Set G) :=
    firstCentralizerResidual_sylow_normalizes D hzT
  have hcore : B.pCoreIn 2 ≤ T := (isPGroup_pCoreIn 2 B).le_sylow_of_normalized T
    (hTB.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))
  have hC : twoSectionCentralizer B (normalizer (B : Set G)) ≤ normalizer (L : Set G) := by
    apply (sectionCentralizer_normalizes_residual B (zero L)
      (covered_zero_le_firstResidual D m hc z hzL) (isPPerfect_embedded_pResidual 2 _)
      (hcore.trans (D.sylow_normalizes_component.trans (normalizer_le_zero_normalizer L)))).trans
    exact (covered_zero_normalizer h.toHypothesis1221 D.sylow_normalizes_component hc).le
  have hR : normalizer ((B ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤ normalizer (L : Set G) :=
    (normalizer_le_normalizer_baumann _).trans
      (covered_augmentation_baumann_normalizer h structural D m hc z hzT hzL)
  exact (normalizer_core_factorization T B (firstCentralizerResidual_twoPerfect L z.val) hTB).symm.le.trans
    (sup_le hC (inf_le_right.trans hR))

/-- Source 13.2.2(9) for the literal L₁ on the original Sylow-fixed plane. -/
theorem covered_one_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    normalizer (one L (T : Subgroup G)
      (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) : Set G) ≤ normalizer (L : Set G) := by
  rw [covered_firstFlagNormalizer_residual h structural D m hc z hzT hzL]
  exact covered_firstResidual_normalizer h structural D m hc z hzT hzL

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
