module

public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.LongRoot.CoverModel.Definitions
public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.LongRoot.CoverModel.BaseQuotient
public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.LongRoot.OnanImageBounds

/-!
# Covered residual image bounds from an actual section comparison

An actual A₅ top quotient and a five-element with at most two fixed points
on the intrinsic Frattini section suffice for both seven-free image bounds.
The latter section may have order dividing 512. In particular an equivariant
epimorphism with kernel of order dividing two onto a fixed-free 256-element
module supplies the required data.

The resulting bounds feed the complete O'Nan consumer for the same V and X.
The marked cover definitions are re-exported for the intrinsic model
calculation. Construction of its section data remains an explicit obligation;
none of the conditional theorems here asserts that a G₂(4) cover already
has those data. In particular V=Φ(O₂(X)) is neither assumed nor concluded.

Source: Aschbacher–Smith, Lemma 16.5.13, printed pp.1201–1202.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot
open Subgroup

namespace CoverModel

/-- Structural outputs of the intrinsic cover calculation. The five-action
is the literal conjugation action of an element of X on its Frattini section. -/
structure SectionModel (X : Type*) [Group X] [Finite X] where
  topEquiv : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5)
  five : X
  five_pow : five ^ 5 = 1
  section_card : Nat.card (pCore 2 X ⧸ frattini (pCore 2 X)) ∣ 512
  fixed_card : Nat.card (innerSectionAction X five).fixedSubgroup ≤ 2

/-- A genuine section epimorphism constructs the structural input, even
when the covering kernel has not been shown to lie in the Frattini subgroup. -/
def sectionModel_of_epimorphism
    {X W : Type*} [Group X] [Finite X] [Group W] [Finite W]
    (e : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5))
    (s : X) (hs : s ^ 5 = 1)
    (f : (pCore 2 X ⧸ frattini (pCore 2 X)) →* W)
    (hf : Function.Surjective f) (hker : Nat.card f.ker ∣ 2)
    (hW : Nat.card W = 256) (b : MulAut W)
    (heq : ∀ v, f (innerSectionAction X s v) = b (f v))
    (hfree : ∀ w, b w = w → w = 1) : SectionModel X where
  topEquiv := e
  five := s
  five_pow := hs
  section_card := (small_fixed_of_section_epimorphism f hf hker hW _ b heq hfree).1
  fixed_card := (small_fixed_of_section_epimorphism f hf hker hW _ b heq hfree).2

/-- The structural model gives the two bounds for every actual ambient
simultaneous-normalizer action. No identification of V with the section is used. -/
theorem sourceImageBounds_of_sectionModel
    {G : Type*} [Group G] [Finite G] (V X : Subgroup G)
    (d : SectionModel X) : SourceImageBounds V X := by
  refine ⟨seven_coprime_top_of_equiv (residualAction V X) d.topEquiv, ?_⟩
  apply seven_coprime_kernel_image_of_small_fixed (residualAction V X)
    d.section_card d.five ?_ d.fixed_card
  rw [← map_pow, d.five_pow, map_one]

end CoverModel

open Representation Representation.BinaryOffender Representation.GoldschmidtONan
open scoped IsMulCommutative

/-- The source O'Nan contradiction with structural cover data in place of
assumed image bounds. The data producer remains an explicit premise. -/
theorem no_onan_action_of_section_models
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L X Z : Subgroup G} [IsElementaryAbelian 2 (space T X)]
    (S : Subgroup (action (space T X) X).range)
    (hinput : Input (representation (space T X) X) S)
    (hfixed : fixedSpace (representation (space T X) X) S =
      linearSpace (space T X) (commutingSylow T L))
    (hmoved : Representation.RegularCyclicNormalClosure.displacementSpan
      (representation (space T X) X) S ⊤ = linearSpace (space T X) Z)
    (hXL : X ≤ L) (hZ : Z ≠ ⊥) (hZV : Z ≤ space T X) (hZX : Z ≤ X)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hbound : ((T : Subgroup G) ⊓ normalizer (X : Set G)).relIndex T ≤ 2)
    (g : G) (hg : g ∈ actingGroup (space T X) X)
    (hmove : g ∉ normalizer (commutingSylow T L : Set G))
    (hcoverT : commutingSylow T L ≤ X → (T : Subgroup G) ≤ normalizer (X : Set G))
    (hmodel : space T X ≤ X → Nonempty (CoverModel.SectionModel X)) : False := by
  apply no_onan_action_of_source_image_bounds S hinput hfixed hmoved hXL hZ hZV hZX
    hTL hbound g hg hmove hcoverT
  intro hVX
  obtain ⟨d⟩ := hmodel hVX
  exact CoverModel.sourceImageBounds_of_sectionModel _ _ d

end CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot
