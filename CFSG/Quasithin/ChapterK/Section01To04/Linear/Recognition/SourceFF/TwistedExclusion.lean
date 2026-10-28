module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceFF.TwistedExclusion.CanonicalDescent
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceFF.TwistedExclusion.RootDimensions
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Actors
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceImage
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Excluding the actual half-field tensor in an FF action

Absolute recognition supplies the original component action in Hermitian
coordinates, including both coefficient twists and the dual. The original
central quotient gives the source overgroup equation for the full ambient
image. Transporting an FF offender into that image contradicts its proved
strict quadratic-ratio bound.

Source: Aschbacher–Smith, K.3.2.4, printed pp.455–456.
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

/-- Neither permitted absolute half-field tensor can occur in the original FF action. -/
theorem not_twisted_of_ff {K : GroupClass.{u}} (h : SourceHypothesis K ρ L)
    (C : LinearCover B 3 L)
    (eQ : L ⧸ center L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) B.Carrier)
    (hff : IsFFModule ρ)
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
  have hffM : IsFFModule (overgroupAction n M) :=
    hff.map_equivariant ρ (overgroupAction n M) eG.groupEquiv.toMonoidHom
      eG.groupEquiv.injective eG.linearEquiv eG.intertwines
  exact not_isFFModule n M hM hffM

end CFSG.Quasithin.ChapterK.Linear.Recognition.TwistedExclusion
