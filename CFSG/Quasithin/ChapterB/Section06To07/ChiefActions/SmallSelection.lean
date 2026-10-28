module
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallThompson
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallCubic
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallPair
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.PairCubic
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallSolvableCubic

/-!
# Selecting the subgroups on the literal small chief image

The natural-action markings select a cubic and an index-two subgroup for the
same original offender and mapped Sylow subgroup. This leaf keeps the actual
action homomorphism in every containment, relative index, and commutator
identity, so the result feeds the normalizer lift without changing actors.

Source: Aschbacher–Smith, 3.1.9(5) and15.1.12(4).
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The five-point branch supplies the exact geometry on the literal chief image. -/
theorem minimalParabolic_chief_five_selection
    (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ]
    (S : Sylow 2 G) (hS : IsMinimalParabolicOver S ⊤)
    (A : Subgroup G) (hAS : A ≤ S)
    (hA : IsOffender (imageRepresentation ρ) (A.map (actionHom ρ)))
    (hmark : ChiefFiveMarkedSection (imageRepresentation ρ)) :
    ∃ R L : Subgroup (actionImage ρ),
      R ≤ (S : Subgroup G).map (actionHom ρ) ∧
      A.map (actionHom ρ) ≤ normalizer (R : Set (actionImage ρ)) ∧
      L ≤ normalizer (R : Set (actionImage ρ)) ∧
      A.map (actionHom ρ) ≤ normalizer (L : Set (actionImage ρ)) ∧
      R.relIndex (A.map (actionHom ρ)) = 2 ∧
      L = ⁅L,A.map (actionHom ρ)⁆ ∧
      L ⊔ (S : Subgroup G).map (actionHom ρ) = ⊤ := by
  obtain ⟨⟨e⟩,_⟩ := minimalParabolic_chief_five_of_marked ρ S hS ⟨_,hA⟩ hmark
  have hq : Function.Surjective (actionHom ρ) := ρ.asGroupHom.rangeRestrict_surjective
  have hAS' : A.map (actionHom ρ) ≤ (S : Subgroup G).map (actionHom ρ) := map_mono hAS
  obtain ⟨L,R,_,hRA,hindex,hAR,hLR,hAL,hcomm,hgen⟩ :=
    five_action_cubic_selection (imageRepresentation ρ) (S.mapSurjective hq)
      (A.map (actionHom ρ)) hAS' hA e
  exact ⟨R,L,hRA.trans hAS',hAR,hLR.trans (Subgroup.centralizer_le_normalizer _),hAL,hindex,hcomm,hgen⟩
/-- The paired five-point marking supplies the geometry on the same chief image. -/
theorem minimalParabolic_chief_five_pair_selection
    (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ]
    (S : Sylow 2 G) (hS : IsMinimalParabolicOver S ⊤)
    (A : Subgroup G) (hAS : A ≤ S)
    (hA : IsOffender (imageRepresentation ρ) (A.map (actionHom ρ)))
    (hmark : ChiefFivePairMarkedSection (imageRepresentation ρ)) :
    ∃ R L : Subgroup (actionImage ρ),
      R ≤ (S : Subgroup G).map (actionHom ρ) ∧
      A.map (actionHom ρ) ≤ normalizer (R : Set (actionImage ρ)) ∧
      L ≤ normalizer (R : Set (actionImage ρ)) ∧
      A.map (actionHom ρ) ≤ normalizer (L : Set (actionImage ρ)) ∧
      R.relIndex (A.map (actionHom ρ)) = 2 ∧
      L = ⁅L,A.map (actionHom ρ)⁆ ∧
      L ⊔ (S : Subgroup G).map (actionHom ρ) = ⊤ := by
  let q := actionHom ρ
  have hq : Function.Surjective q := ρ.asGroupHom.rangeRestrict_surjective
  have hc := irreducible_image_twoCore_eq_bot ρ
  have hn : q.ker ≠ ⊤ := by
    intro he
    apply hA.1.1
    exact (Subgroup.map_eq_bot_iff A).mpr (show A ≤ q.ker by rw [he]; exact le_top)
  let := imageRepresentation_irreducible ρ inferInstance
  obtain ⟨d,⟨c⟩⟩ := hmark
  exact paired_five_action_cubic_selection (imageRepresentation ρ)
    (imageRepresentation_injective ρ) (S.mapSurjective hq)
    (minimalParabolic_reduced_image S hS q hq hc hn).2 ⟨_,hA⟩ hc d c
    (A.map q) (map_mono hAS) hA
/-- Each actual small natural branch supplies the same original offender's
index-two normalizer geometry on the literal chief-action image. -/
theorem minimalParabolic_chief_small_selection
    (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ]
    (S : Sylow 2 G) (hS : IsMinimalParabolicOver S ⊤)
    (A : Subgroup G) (hAS : A ≤ S)
    (hA : IsOffender (imageRepresentation ρ) (A.map (actionHom ρ)))
    (hsmall : SmallNaturalWreathAction (imageRepresentation ρ) ∨
      ChiefFiveMarkedSection (imageRepresentation ρ) ∨
      ChiefFivePairMarkedSection (imageRepresentation ρ)) :
    ∃ R L : Subgroup (actionImage ρ),
      R ≤ (S : Subgroup G).map (actionHom ρ) ∧
      A.map (actionHom ρ) ≤ normalizer (R : Set (actionImage ρ)) ∧
      L ≤ normalizer (R : Set (actionImage ρ)) ∧
      A.map (actionHom ρ) ≤ normalizer (L : Set (actionImage ρ)) ∧
      R.relIndex (A.map (actionHom ρ)) = 2 ∧
      L = ⁅L,A.map (actionHom ρ)⁆ ∧
      L ⊔ (S : Subgroup G).map (actionHom ρ) = ⊤ := by
  rcases hsmall with hsmall | hsmall | hsmall
  · exact chief_small_natural_image_geometry ρ S hS A hAS hA hsmall
  · exact minimalParabolic_chief_five_selection ρ S hS A hAS hA hsmall
  · exact minimalParabolic_chief_five_pair_selection ρ S hS A hAS hA hsmall
end CFSG.Quasithin.ChapterB

