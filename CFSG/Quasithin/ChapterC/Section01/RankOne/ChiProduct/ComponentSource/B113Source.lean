module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.ComponentSource.Models
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SQTKSectionImage
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.CyclicIntersection
public import CFSG.Quasithin.ChapterB.Section01.ComponentNormalization.Source

/-!
# The literal B.1.13 section-to-component step

The faithful B.1.11 section is applied to the selected component itself.  The
corrected B.4.2 action catalogue gives a Sylow-fixer bound on its actual image;
the marking equivalence transports that bound back to the original component.
The local quasisimple/cyclic dichotomy then forces the selected seed into the
component, retaining the original center and section maps.

Source: Aschbacher--Smith B.1.11--B.1.13, printed pp.72--74.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.ComponentSource
open CFSG.Quasithin.ChapterB
open ComponentRecognition ComponentRecognition.SylowOvergroups
open ChapterB.ComponentRecognition.SQTKSectionImage
open ChapterB.SourceInduction

universe u v
variable {G V : Type u} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The faithful section of the actual component supplies both intrinsic
Sylow estimates, with only actual A₅ and A₇ as alternatives to the second. -/
theorem component_bounds_of_classified_section
    (hfaith : Function.Injective ρ) (L A : Subgroup G) [IsQuasisimple L]
    (hLsqtk : IsSQTK KnownSimple.IsKnownSimple L)
    (hc : Nat.card (center L) = 1 ∨ Nat.card (center L) = 3)
    (hLA : ⁅L, A⁆ = L) (hA : IsBestOffender ρ A)
    (earlier : ChapterB.SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,u}
      KnownSimple.IsKnownSimple) :
    SylowFixerIsTwoGroup L ∧ (ProperSylowFittingBound L ∨
      Nonempty (L ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (L ≃* alternatingGroup (Fin 7))) := by
  obtain ⟨H, I, _, _, hI, hHI, hHN, _, hImage, hmark, hcase⟩ :=
    SQTKSectionImage.exists_classified_section ρ hfaith L A hLsqtk hc hLA hA earlier
  let σ := centralSectionRepresentation ρ L H I hHI hHN
  let M := actionSubgroup σ (L.subgroupOf H)
  let : IsQuasisimple M := hImage.quasisimple
  obtain ⟨hf, hb⟩ := source_action_sylow_bounds (imageRepresentation σ) M
    (offenderSubgroup (imageRepresentation σ)) hcase
  obtain ⟨e, _⟩ := hmark
  refine ⟨EvenLieFixers.fixer_of_equiv e hf, ?_⟩
  rcases hb with hb | ha
  · exact Or.inl (properSylowFittingBound_of_equiv e hb)
  · rcases ha with h5 | h7
    · obtain ⟨a⟩ := h5
      exact Or.inr (Or.inl ⟨e.trans a⟩)
    · obtain ⟨a⟩ := h7
      exact Or.inr (Or.inr ⟨e.trans a⟩)

/-- The actual classified section discharges the local B.1.13 containment
and proper-overgroup alternative on the original component and seed. -/
theorem component_containment_of_source_section
    (K L : Subgroup G) (T : Sylow 2 G) (hL : IsComponent G L)
    (hLK : ⁅L, K⁆ = L)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal)
    (hcomm : K = ⁅K, generatedBy {A | IsBestOffender ρ A} (T : Subgroup G)⁆)
    (hfaith : Function.Injective ρ)
    (hLsqtk : IsSQTK KnownSimple.IsKnownSimple L)
    (hc : Nat.card (center L) = 1 ∨ Nat.card (center L) = 3)
    (earlier : ChapterB.SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,u}
      KnownSimple.IsKnownSimple) :
    K ≤ L ∧ (K = L ∨ Nonempty (L ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (L ≃* alternatingGroup (Fin 7))) := by
  let : IsQuasisimple L := hL.2
  have hN := ChapterB.offenderSubgroup_le_normalizer_component ρ hfaith hL
  obtain ⟨A, hA, _, hLA⟩ :=
    exists_bestOffender_commutator ρ K L (T : Subgroup G) hL hLK hcomm hN
  obtain ⟨hLF, hb⟩ := component_bounds_of_classified_section ρ hfaith L A hLsqtk hc hLA hA earlier
  have hd : K ≤ L ∨ ⁅K, L ⊓ (K ⊔ (T : Subgroup G))⁆ = ⊥ := by
    rcases hkind with hq | h3
    · let : IsQuasisimple K := hq
      exact quasisimple_local_dichotomy K L T hL hK
    · exact cyclic_local_dichotomy ρ K L T hfaith h3 hK hcomm hL hLK hN
  have hKL := le_component_of_local_dichotomy K L T hL hLK hkind
    ((le_offenderSubgroup_of_local_commutator ρ K (T : Subgroup G) hcomm).trans hN) hd hLF
  refine ⟨hKL, ?_⟩
  rcases hb with hb | hb
  · exact Or.inl (eq_component_of_proper_sylow_fitting_bound K L T hL hLK hkind hK hKL hb)
  · exact Or.inr hb

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.ComponentSource
