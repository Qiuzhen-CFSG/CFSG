module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.FullCoreTransfer.Assembly
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.FullCoreTransfer.Ordinary
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.ThreeRank

/-!
# Full-core best generation on the literal temporary actor

For H = temporaryLineNormalizer T V E, Q = O₂(H), and C = C_H(E),
this assembles best generation of I = q(J(C)) on the paired first summand.
The exact section-action kernel and Q = C_T(U/E) make the action kernel odd.
The original 15.3.49(5) normalizer bound and paired marker comparison make its
order prime to three. The actual quotient product and SQTK cover give the
three-rank bound. Core transvections and the paired projection supply every
ordinary maximum-image inequality. Assembly then proves best generation of
this same I, without identifying I with its faithful action image.

Replacement supplies TemporaryData, FixedGeometry, PairedSection, the paired
kernel, compatible centralizer Sylow and maximum-family comparison. The
preceding source marker identities are hfix, hspan and hmarker; hZ is precisely
the 15.3.49(5) input with Z ≤ V. BestReduction supplies the genuine universal
earlier classifier. There is no model, rank, no-strong, or generation premise.
The original-I₀ and index-three conclusions remain with Offenders.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 15.3.67, printed pp.1153–1154; B.1.2–4, p.68; B.5.1 and B.5.6,
pp.99–105.
-/

public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer
open Replacement.Transvections ChapterB.SourceInduction
universe u
variable {G L W : Type u} [Group G] [Finite G] [Group L]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- The same temporary Thompson image is best-generated on the actual paired
first summand, from the preceding local facts and universal earlier classifier. -/
theorem temporary_thompson_image_generated
    {K : GroupClass.{u}} (classify : AdequateClassificationInput.{u,u} K)
    (Y T V E Z : Subgroup G) [IsMulCommutative V]
    [(Replacement.Transvections.localSpan T V E).Normal]
    [IsElementaryAbelian 2 (Replacement.Transvections.localSpan T V E)]
    (d : TemporaryData Y T V E)
    (hG : IsSQTK K (temporaryLineNormalizer T V E))
    (hZV : Z ≤ V) (hZ : Nat.Coprime 3 (Nat.card (normalizer (Z : Set G))))
    (f : temporaryLineNormalizer T V E →* L) (hf : Function.Surjective f)
    (hker : f.ker = centralizer
      (Replacement.Transvections.localSpan T V E : Set (temporaryLineNormalizer T V E)))
    (geom : FixedGeometry (localRepresentation T V E f hf hker)
      (f d.tau) (f d.conjugator) (localLineSpace T V E))
    (σ : Representation (ZMod 2) ((temporaryLineNormalizer T V E) ⧸ localCore T V E) W)
    (paired : PairedSection (Replacement.Transvections.localSpan T V E) (localLine T V E)
      (localCentralizer T V E) (localCore T V E) f hf hker σ)
    (hpairedker : (σ.comp ((QuotientGroup.mk' (localCore T V E)).comp
      (localCentralizer T V E).subtype)).ker =
        ((Descent.sectionKernel V E).subgroupOf (temporaryLineNormalizer T V E)).subgroupOf
          (localCentralizer T V E))
    (hcompare : ∃ B ∈ Stellmacher.elementaryAbelianMaxSubgroups
      ((lineT T E).subgroupOf (temporaryLineNormalizer T V E)), B ≤ localCentralizer T V E)
    (product : ((temporaryLineNormalizer T V E) ⧸ localCore T V E) ≃*
      (Equiv.Perm (Fin 3) × (localCentralizer T V E).map (QuotientGroup.mk' (localCore T V E))))
    (S : Sylow 2 ((localCentralizer T V E).map (QuotientGroup.mk' (localCore T V E))))
    (hST : (S : Subgroup _).map ((localCentralizer T V E).map
      (QuotientGroup.mk' (localCore T V E))).subtype ≤
        ((lineT T E).subgroupOf (temporaryLineNormalizer T V E)).map
          (QuotientGroup.mk' (localCore T V E)))
    (P : Submodule (ZMod 2) W)
    (hfix : P ≤ fixedSpace σ ((S : Subgroup _).map
      ((localCentralizer T V E).map (QuotientGroup.mk' (localCore T V E))).subtype))
    (hspan : Submodule.span (ZMod 2)
      {w | ∃ (g : thompsonImage T V E) (v : W), v ∈ P ∧ σ g v = w} = ⊤)
    (hmarker : ∀ x ∈ localCentralizer T V E,
      QuotientGroup.mk' (localCore T V E) x ∈ thompsonImage T V E →
      (∀ w ∈ P, σ (QuotientGroup.mk' (localCore T V E) x) w = w) →
        ∀ v ∈ V.subgroupOf (temporaryLineNormalizer T V E), ⁅x, v⁆ ∈ localLine T V E) :
    offenderSubgroup (σ.comp (thompsonImage T V E).subtype) = ⊤ := by
  let q := QuotientGroup.mk' (localCore T V E)
  let C := localCentralizer T V E
  have hEU : localLine T V E ≤ Replacement.Transvections.localSpan T V E :=
    comap_mono (d.line_le.trans (le_conjugateSpanBy V (lineNormalizer E)))
  let : IsElementaryAbelian 2 (localLine T V E) := IsElementaryAbelian.of_le hEU
  have hP := temporary_markerCentralizer_coprime_three Y T V E Z d hZV hZ σ P hmarker
  obtain ⟨SI, hSI, hodd⟩ :=
    temporary_compatible_sylow_and_odd_kernel Y T V E d σ hpairedker S hST
  have hfixI : P ≤ fixedSpace (σ.comp (thompsonImage T V E).subtype) (SI : Subgroup _) := by
    intro v hv a
    have ha := hSI.le a.property
    exact hfix hv ⟨a.val, ha⟩
  have hQ : IsPGroup 2 (localCore T V E) := by
    rw [localCore_eq_pCore]
    exact pCore_isPGroup
  have hr : primeRank 3 (thompsonImage T V E) ≤ 1 :=
    BestReduction.thompsonImage_threeRank_le_one (localCore T V E) C
      (Stellmacher.elementaryAbelianMaxJ C) hQ
      (hG.stronglyQuasithin 3 (by decide) (by decide))
      (sSup_le fun _ hA => hA.1) product
  apply thompson_image_generated_of_classification_and_marker classify hG C q
    (QuotientGroup.mk'_surjective _) σ hodd hr SI P hfixI hspan hP
  exact temporary_maximum_images_ordinary Y T V E d f hf hker geom σ paired hcompare

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer
