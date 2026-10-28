module
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentModels.Classical
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentModels.OriginalImage

/-!
# The actual source component catalogue in H/J

Apply the completed component sieve to the literal image of the original
C-component in the normal-core quotient. Theorem A supplies SQTK for that
quotient, and the source image theorem supplies simplicity and the same
Sylow generating relation without assuming that K is normal. The final
existence statement constructs K from the original nonsolvable source
configuration before applying this catalogue.

The remaining odd-family geometry and witness constructions are separate
source obligations. The model parameter here is not asserted to equal the
generation parameter of H.

Source: Aschbacher–Smith E.2.2, printed pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

/-- The selected original C-component has the actual five-family star image, normal or exchanged. -/
theorem source_component_classical_star_models
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremC κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    let D := K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))
    ChapterA.Section02.IsTheoremCOddModel D ∨
    ClassificationModels.IsBenderModel D ∨
    (∃ f : ℕ, 1 ≤ f ∧ ClassicalGroup.IsPSL D 3 (2^f)) ∨
    (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSp D 2 (2^f)) ∨
    Nonempty (D ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  have hi := source_component_simple_image T hP hs K hK hgen
  let : IsSimpleGroup (K.map q) := hi.1
  exact source_simple_component_classical_models hC (source_star_sqtk hA hH T hP hs)
    S (source_star_minimal_core_free T hP).1 (K.map q) hi.2.1 hi.2.2.2

/-- Construct the original generating C-component and classify its literal H/J image. -/
theorem source_original_component_classical_models
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremC κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) :
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      K ⊔ (T : Subgroup H) = ⊤ ∧
      (let D := K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))
       ChapterA.Section02.IsTheoremCOddModel D ∨
       ClassificationModels.IsBenderModel D ∨
       (∃ f : ℕ, 1 ≤ f ∧ ClassicalGroup.IsPSL D 3 (2^f)) ∨
       (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSp D 2 (2^f)) ∨
       Nonempty (D ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) := by
  obtain ⟨K,hK,hq,hgen,_⟩ := source_original_component hH T hP hs
  exact ⟨K,hK,hq,hgen,source_component_classical_star_models hA hC hH T hP hs K hK hgen⟩
end CFSG.Quasithin.ChapterE.Structure
