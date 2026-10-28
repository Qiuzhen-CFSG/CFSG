module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceFF.TwistedExclusion.CanonicalDescent
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceFF.TwistedExclusion.RootDimensions
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Actors
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceImage
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.SourceFF

/-!
# The SL₃ source classification at quadratic ratio two

The original cubic module sieve recognizes the natural or half-field tensor
module. Transporting the literal ambient action into its Hermitian coordinates
preserves the quadratic bound; the proved root displacement and quadratic
actor geometry exclude the tensor at ratio two. The natural model therefore
supplies the complete B.4.2 action row on the original representation.

Source: Aschbacher–Smith B.4.5 and K.3.2.4, printed pp.87 and 455–456.
-/

public noncomputable section
open Representation Representation.BinaryOffender Subgroup Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.TwistedExclusion
open ChapterB.QuasisimpleSource ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G} {B : BinaryField}

/-- Neither absolute half-field tensor admits quadratic ratio at most two. -/
theorem not_twisted_of_quadratic_le_two {K : GroupClass.{u}} (h : SourceHypothesis K ρ L)
    (C : LinearCover B 3 L)
    (eQ : L ⧸ center L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) B.Carrier)
    (hq : quadraticRatio ρ ≤ 2)
    (hs : let := h.finite_module
      let := inflated_irreducible ρ C h.irreducible
      0 < schurDegree (inflated ρ C))
    (ht : let := h.finite_module
      let := inflated_irreducible ρ C h.irreducible
      B.degree = 2 * schurDegree (inflated ρ C))
    (hm : let := h.finite_module
      let := inflated_irreducible ρ C h.irreducible
      HasAbsoluteTwistedModel (inflated ρ C) (schurDegree (inflated ρ C))) : False := by
  let := h.finite_group
  let := h.finite_module
  let := inflated_irreducible ρ C h.irreducible
  let n := schurDegree (inflated ρ C)
  let : NeZero n := ⟨Nat.ne_of_gt hs⟩
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := h.fitting ▸ inferInstanceAs (generalizedFitting G).Normal
  obtain ⟨a, ⟨e⟩⟩ := exists_binary_hermitian_equiv n (inflated ρ C)
    (by rw [B.card_eq, ht]) rfl hm
  let π := C.projection.comp a.toMonoidHom
  have hπ : Function.Surjective π := C.surjective.comp a.surjective
  let d := hermitianActionEquiv (ρ.comp L.subtype) n π hπ
    (h.faithful.comp L.subtype_injective) e
  let M := sourceImage ρ L n d
  have hM : SourceOvergroup n M := sourceImage_isSource ρ L n d h.fitting B eQ
  let eG := sourceActionEquiv ρ L n d h.faithful
  have hle := quadraticRatio_le_of_injective_equivariant ρ (overgroupAction n M)
    eG.groupEquiv.toMonoidHom eG.groupEquiv.injective eG.linearEquiv eG.intertwines
  exact (not_le_of_gt (Tensor.quadraticRatio_gt_two_of_inner_source_dimensions n M hM
    (innerRootDimensions n M hM))) (hle.trans hq)

end CFSG.Quasithin.ChapterK.Linear.Recognition.TwistedExclusion

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.SourceQuadratic
open ChapterB.QuasisimpleSource ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : GroupClass.{u}} {L : Subgroup G} {B : BinaryField}

theorem naturalSourceInput_of_quadratic_le_two (h : SourceHypothesis K ρ L)
    (C : LinearCover B 3 L)
    (eQ : L ⧸ center L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) B.Carrier)
    (hq : quadraticRatio ρ ≤ 2) : Nonempty (Natural.SourceInput ρ L B 3 K) := by
  let := h.finite_module
  let := inflated_irreducible ρ C h.irreducible
  obtain ⟨hs, hn | ht⟩ := SourceFF.absolute_models h C eQ
  · exact SourceFF.naturalSourceInput_of_absolute h C hn.1 hn.2.2
  · exact (TwistedExclusion.not_twisted_of_quadratic_le_two h C eQ hq hs ht.1 ht.2.2).elim

theorem actionCase_of_quadratic_le_two (h : SourceHypothesis K ρ L)
    (r : ℕ) (hr : 0 < r)
    (hquot : ClassicalGroup.IsPSL (L ⧸ center L) 3 (2 ^ r))
    (hq : quadraticRatio ρ ≤ 2) :
    ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase
      ρ L (offenderSubgroup ρ) := by
  let := h.finite_group
  let := h.finite_module
  obtain ⟨B, _, eQ, C, _⟩ := SourceFF.exists_binaryField_cover h r hr hquot
  obtain ⟨hn⟩ := naturalSourceInput_of_quadratic_le_two h C eQ hq
  exact (Natural.source_natural ρ L B 3 hn).2.2.2
end CFSG.Quasithin.ChapterK.Linear.Recognition.SourceQuadratic
