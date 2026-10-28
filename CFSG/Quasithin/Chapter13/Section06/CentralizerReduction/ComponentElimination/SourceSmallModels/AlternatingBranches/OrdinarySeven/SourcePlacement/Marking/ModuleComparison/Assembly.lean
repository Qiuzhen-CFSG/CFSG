module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.ComponentSplitting
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.NormalizerExtension.Application

/-!+# The actual ordinary A₇ comparison on W_K

The chosen block coordinates first identify [W_K,K] with the natural A₇
module. Vanishing first cohomology splits it off, and W_K = ⟨z^K⟩ bounds
the fixed complement by one dimension. Relative normality and the scalar
commutant extend this splitting to the full plus actor in the SAME seven
point coordinates. Thus fixed codimensions agree for every subgroup.

The three pair-indicator vectors also detect the actual fixed centralizer.
Under a simultaneous three-transposition marking this gives Baum(Tᵥ)⁺ =
J(Tᵥ)⁺ through the original plus projection, without any further module,
codimension or centralizer premise.

The genuine earlier-source equality [W_K,K] = [Z(O₂(K)),K] remains explicit;
its producers are `qt-13-06-selection-modules` and
`qt-13-06-control-characteristic-normalizers`. The parent marking task
retains its discharge and construction of the offender-family marking.
No separate Irr⁺ assumption is needed: the block's two-perfection supplies
the intrinsic commutator generation used by `ComponentSplitting`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.3.3(1),
printed p.84/PDF p.95, and Lemma 13.6.22, printed p.932/PDF p.949.
-/

@[expose] public section

open Subgroup Equiv
open scoped IsMulCommutative
open Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison

variable {G : Type*} [Group G] [Finite G]
  (K L T : Subgroup G) (z v : G)
  (hL : Tv T v ≤ normalizer (Lv L v : Set G))
  (hz : Tv T v ≤ centralizer ({z} : Set G))
  [hW : IsElementaryAbelian 2 (WK K L T z v)]
  (hWT : WK K L T z v ≤ Tv T v)
  (hn : Tv T v ≤ normalizer (K : Set G)) (hLv : Lv L v ≤ K)
  (hY : K ∈ Yz L T z v)
  (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
  (hblock : ChapterC.IsAlternatingBlock K 7)
  (hUK : ⁅WK K L T z v, K⁆ =
    ⁅((center (pCore 2 K)).map (pCore 2 K).subtype).map K.subtype, K⁆)
  (φ : Gplus K L T z v hL hz →* Perm (Fin 7))
  (hφB : (plusImage K L T z v hL hz K).map φ = alternatingGroup (Fin 7))
  (hcoord : ∀ k : K, φ (plusMk K L T z v hL hz
    ⟨k, K_le_plusActor K L T v k.property⟩) =
      (blockProjection K (ordinaryQuotientEquiv K hblock) k : Perm (Fin 7)))

/-- Construct the full-plus natural summand from the original block model
and the earlier commutator identity; no splitting is an input. -/
noncomputable def ordinaryNaturalSummand :
    NaturalSummand (representation K L T z v hL hz hWT) φ := by
  let hs := ComponentSplitting.natural_component_summand
    K L T z v hL hz hWT hn hLv hY hR hblock hUK φ hcoord
  exact extend_plus K L T z v hL hz hn hLv hWT φ hφB hs.choose hs.choose_spec

include hn hLv hY hR hblock hUK hφB hcoord in
/-- The literal W₀ action has the natural fixed codimension on EVERY subgroup
of G⁺, in the coordinates of the same `ordinaryModuleModel`. -/
theorem ordinary_fixedCodim_eq (A : Subgroup (Gplus K L T z v hL hz)) :
    fixedCodim (representation K L T z v hL hz hWT) A =
      fixedCodim (BinaryPermutation.naturalRepresentation (Fin 7)) (A.map φ) :=
  (ordinaryNaturalSummand K L T z v hL hz hWT hn hLv hY hR hblock hUK φ hφB hcoord).fixedCodim_eq A

include hW hWT hn hLv hY hR hblock hUK hφB hcoord in
/-- Concrete fixed vectors, transported through the constructed summand,
discharge the fixed-centralizer bound under the simultaneous marking. -/
theorem ordinary_fixed_centralizer_le_thompson (hφ : Function.Injective φ)
    (g : Perm (Fin 7))
    (hg : ((plusImage K L T z v hL hz
      (Stellmacher.elementaryAbelianMaxJ (Tv T v))).map φ).map
        (MulAut.conj g).toMonoidHom = threeTranspositions) :
    plusImage K L T z v hL hz
      (Tv T v ⊓ centralizer
        (WK K L T z v ⊓ centralizer
          (Stellmacher.elementaryAbelianMaxJ (Tv T v) : Set G) : Set G)) ≤
      plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v)) :=
  fixed_centralizer_le_thompson K L T z v hL hz hWT φ hφ
    (ordinaryNaturalSummand K L T z v hL hz hWT hn hLv hY hR hblock hUK φ hφB hcoord) g hg

include hW hWT hn hLv hY hR hblock hUK hφB hcoord in
/-- The actual Baumann and Thompson plus-images agree under the marking;
neither this equality nor a centralizer bound is assumed. -/
theorem ordinary_baumann_image_eq_thompson (hφ : Function.Injective φ)
    (g : Perm (Fin 7))
    (hg : ((plusImage K L T z v hL hz
      (Stellmacher.elementaryAbelianMaxJ (Tv T v))).map φ).map
        (MulAut.conj g).toMonoidHom = threeTranspositions) :
    plusImage K L T z v hL hz (ChapterB.baumann (Tv T v)) =
      plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v)) :=
  baumann_plus_eq_of_fixed_centralizer K L T z v hL hz hWT
    (ordinary_fixed_centralizer_le_thompson K L T z v hL hz hWT hn hLv hY hR
      hblock hUK φ hφB hcoord hφ g hg)

include hn hLv hY hR hblock hUK in
/-- Choose the faithful source-compatible action and discharge its module
comparison and marked fixed-centralizer/Baumann conclusions together.
The parent only has to construct the simultaneous marking for this action. -/
theorem ordinary_comparison_exists :
    ∃ φ : Gplus K L T z v hL hz →* Perm (Fin 7), Function.Injective φ ∧
      (plusImage K L T z v hL hz K).map φ = alternatingGroup (Fin 7) ∧
      (∀ k : K, φ (plusMk K L T z v hL hz
        ⟨k, K_le_plusActor K L T v k.property⟩) =
          (blockProjection K (ordinaryQuotientEquiv K hblock) k : Perm (Fin 7))) ∧
      (∀ A : Subgroup (Gplus K L T z v hL hz),
        fixedCodim (representation K L T z v hL hz hWT) A =
          fixedCodim (BinaryPermutation.naturalRepresentation (Fin 7)) (A.map φ)) ∧
      ∀ g : Perm (Fin 7),
        ((plusImage K L T z v hL hz
          (Stellmacher.elementaryAbelianMaxJ (Tv T v))).map φ).map
            (MulAut.conj g).toMonoidHom = threeTranspositions →
        (plusImage K L T z v hL hz
          (Tv T v ⊓ centralizer
            (WK K L T z v ⊓ centralizer
              (Stellmacher.elementaryAbelianMaxJ (Tv T v) : Set G) : Set G)) ≤
          plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v))) ∧
        plusImage K L T z v hL hz (ChapterB.baumann (Tv T v)) =
          plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v)) := by
  obtain ⟨φ, hi, hm, hc⟩ := ordinary_action_exists K L T z v hL hz hn hLv hY hR hblock
  refine ⟨φ, hi, hm, hc,
    ordinary_fixedCodim_eq K L T z v hL hz hWT hn hLv hY hR hblock hUK φ hm hc, ?_⟩
  intro g hg
  exact ⟨ordinary_fixed_centralizer_le_thompson K L T z v hL hz hWT hn hLv hY hR
      hblock hUK φ hm hc hi g hg,
    ordinary_baumann_image_eq_thompson K L T z v hL hz hWT hn hLv hY hR
      hblock hUK φ hm hc hi g hg⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison

end
