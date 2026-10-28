module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.Source
public import Theory.Representation.BinaryOffender.UniformFixedSpace

/-!
# Retaining the module comparison in the seven-letter source marking

The source Thompson marking conjugates both the quotient and the permutation
coordinates. Fixed codimensions are unchanged by this conjugation, so the
same marking retains the natural-module comparison for every subgroup.
This is the comparison needed by the literal six-point replacement.

Source: Aschbacher–Smith, Lemma 13.6.22, printed p.932.
-/

public section
open scoped IsMulCommutative
open Subgroup Equiv Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal
open AlternatingBranches.OrdinarySeven SourcePlacement Marking ModuleComparison
variable {G : Type*} [Group G] [Finite G]

/-- The original marking retains its fixed-codimension comparison. -/
theorem exists_marking_with_comparison
    (K L T S : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLv : Lv L v ≤ K)
    (hY : K ∈ Yz L T z v)
    (hS : S = ChapterB.baumann (Tv T v))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hWT : WK K L T z v ≤ Tv T v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (hblock : ChapterC.IsAlternatingBlock K 7)
    (hUK : ⁅WK K L T z v, K⁆ =
      ⁅((center (pCore 2 K)).map (pCore 2 K).subtype).map K.subtype, K⁆) :
    ∃ (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
      (φ : Gplus K L T z v hL hz →* Perm (Fin 7)), Function.Injective φ ∧
      (∀ k : K, φ (plusMk K L T z v hL hz
        ⟨k, ComponentSelection.K_le_plusActor K L T v k.property⟩) =
          (blockProjection K e k : Perm (Fin 7))) ∧
      (plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v))).map φ =
        threeTranspositions ∧
      plusImage K L T z v hL hz S =
        plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v)) ∧
      (∀ A : Subgroup (Gplus K L T z v hL hz),
        fixedCodim (representation K L T z v hL hz hWT) A =
          fixedCodim (BinaryPermutation.naturalRepresentation (Fin 7)) (A.map φ)) := by
  obtain ⟨φ, hi, hAlt, hc, hcodim, hfixed⟩ :=
    ordinary_comparison_exists K L T z v hL hz hWT hn hLv hY hR hblock hUK
  obtain ⟨g, hg⟩ := plus_exists_conjugated_marking
    K L T z v hL hz hn hLv hY hWT φ hi hAlt hcodim
  have hg' : ((plusImage K L T z v hL hz
      (Stellmacher.elementaryAbelianMaxJ (Tv T v))).map φ).map
        (MulAut.conj g).toMonoidHom = threeTranspositions := by
    rw [map_map]
    exact hg
  refine ⟨conjugateQuotient K (ordinaryQuotientEquiv K hblock) g,
    (MulAut.conj g).toMonoidHom.comp φ, (MulAut.conj g).injective.comp hi,
    conjugate_compatible K L T z v hL hz (ordinaryQuotientEquiv K hblock) φ hc g,
    hg, ?_, ?_⟩
  · rw [hS]
    exact (hfixed g hg').2
  · intro A
    rw [← map_map, fixedCodim_map_conj]
    exact hcodim A

/-- Equality in natural coordinates gives equality of the literal centralizers
on W_K, with the original quotient action and all inclusions retained. -/
theorem centralizer_eq_of_natural_fixedSpace
    (K L T B : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hWT : WK K L T z v ≤ Tv T v)
    (hLB : Lv L v ≤ B) (hBK : B ≤ K)
    (φ : Gplus K L T z v hL hz →* Perm (Fin 7))
    (hcodim : ∀ A : Subgroup (Gplus K L T z v hL hz),
      fixedCodim (representation K L T z v hL hz hWT) A =
        fixedCodim (BinaryPermutation.naturalRepresentation (Fin 7)) (A.map φ))
    (hfixed : fixedSpace (BinaryPermutation.naturalRepresentation (Fin 7))
      ((plusImage K L T z v hL hz (Lv L v)).map φ) =
      fixedSpace (BinaryPermutation.naturalRepresentation (Fin 7))
        ((plusImage K L T z v hL hz B).map φ)) :
    WK K L T z v ⊓ centralizer (Lv L v : Set G) =
      WK K L T z v ⊓ centralizer (B : Set G) := by
  have hlin : fixedSpace (representation K L T z v hL hz hWT)
      (plusImage K L T z v hL hz B) =
      fixedSpace (representation K L T z v hL hz hWT)
        (plusImage K L T z v hL hz (Lv L v)) := by
    apply fixedSpace_eq_of_fixedCodim_eq _ (map_mono (comap_mono hLB))
    rw [hcodim, hcodim]
    exact congrArg (fun W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 7)) =>
      Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin 7) ⧸ W)) hfixed.symm
  apply le_antisymm _ (inf_le_inf_left _ (centralizer_le hLB))
  rintro w ⟨hw, hc⟩
  let w' : Additive (Carrier K L T z v) :=
    Additive.ofMul ⟨⟨w, (show Tv T v ≤ plusActor K L T v from le_sup_right) (hWT hw)⟩, hw⟩
  have hD := (mem_fixedSpace_image K L T z v hL hz hWT (Lv L v)
    (hLB.trans (hBK.trans (ComponentSelection.K_le_plusActor K L T v))) w').mpr hc
  rw [← hlin] at hD
  exact ⟨hw, (mem_fixedSpace_image K L T z v hL hz hWT B
    (hBK.trans (ComponentSelection.K_le_plusActor K L T v)) w').mp hD⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal
