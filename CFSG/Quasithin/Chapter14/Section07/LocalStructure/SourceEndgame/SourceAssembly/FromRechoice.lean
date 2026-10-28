module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.GenerationModels
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.ParabolicSteinberg

/-!
# The literal theorem-70 consumer in the 14.7.71–72 argument

All clauses of 14.7.70 are used at the one reselected critical path supplied
by `Rechoice.Statement`. The earlier image and image-order hypotheses survive
that same permitted rechoice. The preceding marked-module calculations then
construct the generation inputs, and the proved centralizer part of 14.7.71
gives R=V and the Frattini and derived identities in 14.7.72.

The genuine earlier universal 14.7.13 implications, the opening point
commutator, and 14.7.68 centralizer implication remain explicit at their
original actors. The theorem-70 producer belongs to the enclosing source
assembly. The independent three-factor placement is needed only for the
subsequent Steinberg recognition.

Source: Aschbacher–Smith, 14.7.70–72, printed pp.1073–1076.
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.MarkedSpans
open SteinbergRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- The exact theorem-70 statement supplies a single coherent earlier record
for 14.7.71. Its order-two and image fields are transported, not assumed for
a second independently chosen critical path. -/
theorem chief_earlier_of_rechoice
    (c : CriticalPath (L := L) F) (images : c.EarlierImages)
    (sep : d.ModuleSeparation) (hc : d.SectionCentralizer)
    (h69 : Nat.card (star F c.Uα) = 2) (h70 : Rechoice.Statement c d) :
    ∃ n : Rechoice.group F L, ChiefFactors.Earlier d (c.reselect n) ∧
      primeRank 2 d.U₀ ≤ 2 := by
  obtain ⟨n, hp, hrank, hi, hV, hU₀, hb, hconj⟩ := h70
  refine ⟨n, ?_, hrank⟩
  exact {
    separation := sep
    sectionCentralizer := hc
    images := c.reselect_earlierImages images n
    point := hp
    image_order := (c.reselect_star_card images n).trans h69
    intersection := hi
    commutator_seed := hV
    commutator_fixed := hU₀
    distance := hb
    conjugate := hconj }

/-- The source centralizer step and all generation equalities follow from
literal70 and the independently earlier13/68 implications. The natural
irreducibility and fixed-space premises are proved by `GenerationModels`. -/
theorem generation_of_rechoice
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) (images : c.EarlierImages)
    (sep : d.ModuleSeparation) (hc : d.SectionCentralizer)
    (mark : UpperMarking d) (actors : LocalActors d)
    (h69 : Nat.card (star F c.Uα) = 2) (h70 : Rechoice.Statement c d)
    (h13 : ∀ n : Rechoice.group F L, SourceGeneration.EarlierThirteen (c.reselect n))
    (hpoint : ∀ n : Rechoice.group F L, F.Vi 1 ≤ ⁅F.U, (c.reselect n).Uα⁆)
    (h68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H) :
    SourceGeneration.Conclusion d := by
  obtain ⟨n, e, hrank⟩ := chief_earlier_of_rechoice d c images sep hc h69 h70
  exact GenerationModels.generation_of_source d structural (c.reselect n) e mark actors
    (h13 n) hrank (hpoint n) h68

/-- The parent theorem-70 assembly chooses this one `n` and supplies its
opening commutator at that same path. No universal point-commutator premise
or second rechoice is required. -/
theorem generation_of_selected_rechoice
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) (n : Rechoice.group F L)
    (images : c.EarlierImages) (sep : d.ModuleSeparation) (hc : d.SectionCentralizer)
    (mark : UpperMarking d) (actors : LocalActors d)
    (h69 : Nat.card (star F c.Uα) = 2)
    (hplane : (c.reselect n).Zα ≤ F.Vi 2) (hrank : primeRank 2 d.U₀ ≤ 2)
    (hinter : F.U ⊓ (c.reselect n).Uα = d.U₀ ⊔ V)
    (hseed : F.U ⊓ (c.reselect n).Uα = ⁅F.U, (c.reselect n).Uα⁆ ⊔ V)
    (hfixed : F.U ⊓ (c.reselect n).Uα = ⁅F.U, (c.reselect n).Uα⁆ ⊔ d.U₀)
    (hb : c.b = 3) (hconj : ∃ l ∈ L, (c.reselect n).Uα = conjugate F.U l)
    (h13 : SourceGeneration.EarlierThirteen (c.reselect n))
    (hpoint : F.Vi 1 ≤ ⁅F.U, (c.reselect n).Uα⁆)
    (h68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H) :
    SourceGeneration.Conclusion d := by
  let e : ChiefFactors.Earlier d (c.reselect n) := {
    separation := sep
    sectionCentralizer := hc
    images := c.reselect_earlierImages images n
    point := hplane
    image_order := (c.reselect_star_card images n).trans h69
    intersection := hinter
    commutator_seed := hseed
    commutator_fixed := hfixed
    distance := hb
    conjugate := hconj }
  exact GenerationModels.generation_of_source d structural (c.reselect n) e mark actors
    h13 hrank hpoint h68

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly
