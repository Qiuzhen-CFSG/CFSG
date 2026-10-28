module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.OffenderImages.Localization
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.Families
public import Theory.Representation.BinaryOffender.FixedCodimTransport

/-!
# Stable families from the actual maximal elementary images

B.2.7 and B.2.10 supply the nonempty stable relative image family. Equality
of fixed codimensions transports it to the natural seven-letter module.
One of its offenders contains an odd permutation, forcing an injective image
containing A₇ to be all of S₇. Sylow localization then identifies its locally
generated subgroup with the literal image of the elementary Thompson group.

The fixed-codimension comparison is an explicit module-theoretic input.
Source: Aschbacher–Smith B.2.7–9, B.3.2(4), and 13.6.22, printed pp.76–77,
83–84, and 932.
-/

@[expose] public section
open Subgroup Equiv Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking
variable {H Q : Type*} [Group H] [Group Q]

/-- The actual conjugate maximal-elementary image family in permutation coordinates. -/
def permutationOffenderImages (R V : Subgroup H) (q : H →* Q)
    (ι : Q →* Perm (Fin 7)) : Set (Subgroup (Perm (Fin 7))) :=
  (Subgroup.map ι) '' (ChapterB.relativeMaxOffenderImages R V q)

variable [Finite H] [Finite Q]

/-- Fixed-codimension comparison makes the action onto S₇ and identifies the
literal Sylow Thompson image with a stable natural-module family. -/
theorem exists_stable_sylow_image_family
    (V : Subgroup H) [V.Normal] [IsElementaryAbelian 2 V]
    (R : Sylow 2 H) (hVR : V ≤ R)
    (q : H →* Q) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set H))
    (ι : Q →* Perm (Fin 7)) (hι : Function.Injective ι)
    (hAlt : alternatingGroup (Fin 7) ≤ ι.range)
    (hJ : (elementaryAbelianMaxJ (R : Subgroup H)).map q ≠ ⊥)
    (hc : ∀ A : Subgroup Q,
      fixedCodim (NormalElementaryQuotient.representation V q hq hker) A =
        fixedCodim (BinaryPermutation.naturalRepresentation (Fin 7)) (A.map ι)) :
    Function.Surjective ι ∧
      ∃ (P : Set (Subgroup (Perm (Fin 7)))) (Rbar : Sylow 2 (Perm (Fin 7))),
        P = permutationOffenderImages R V q ι ∧
        IsStable (BinaryPermutation.naturalRepresentation (Fin 7)) P ∧
        (Rbar : Subgroup _) = ((R : Subgroup H).map q).map ι ∧
        (elementaryAbelianMaxJ (R : Subgroup H)).map (ι.comp q) =
          generatedBy P (Rbar : Subgroup _) := by
  have hj : ¬ elementaryAbelianMaxJ (R : Subgroup H) ≤ q.ker :=
    fun h => hJ ((Subgroup.map_eq_bot_iff _).mpr h)
  have hs := (ChapterB.lemma_B_2_10_relative V R hVR q hq hker hj).2.1
  obtain ⟨A, hA⟩ := hs.1
  have hbest := (hs.2.1 A hA).map_of_fixedCodim
    (NormalElementaryQuotient.representation V q hq hker)
    (BinaryPermutation.naturalRepresentation (Fin 7)) ι hι hc
  have hrange := eq_top_of_alternating_le_of_offender ι.range (A.map ι)
    hAlt hbest (A.map_le_range ι)
  have hsur : Function.Surjective ι := MonoidHom.range_eq_top.mp hrange
  let e : Q ≃* Perm (Fin 7) := MulEquiv.ofBijective ι ⟨hι, hsur⟩
  let Rbar := (R.mapSurjective hq).mapSurjective hsur
  refine ⟨hsur, permutationOffenderImages R V q ι, Rbar, rfl, ?_, rfl, ?_⟩
  · exact hs.map_of_fixedCodim _ (BinaryPermutation.naturalRepresentation (Fin 7)) e hc
  · change (elementaryAbelianMaxJ (R : Subgroup H)).map (ι.comp q) =
      generatedBy (permutationOffenderImages R V q ι) (((R : Subgroup H).map q).map ι)
    rw [← map_map, ChapterB.relativeMaxOffenderImages_sylow_generated R V q hq,
      generatedBy_map_injective ι hι]
    rfl

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking
