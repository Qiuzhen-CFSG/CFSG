module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.NaturalLayer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.LocalPackage.InitialCover

/-!
# The nonbinary natural cover in the literal MS graph

The natural layer is transported through the original component and the
injective vertex coordinates. Its image is exactly U at every vertex of
original-group color; the actor is the vertex residual, and the projection
kernel is its centralizer. The field degree is the original n > 1.
Source: MS93 (3.2)(vi), with the cover convention of (1.5)(ii).
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)

/-- A natural cover of the actual graph layer, with literal conjugation and
its fixed kernel, follows from the original MS input for every n > 1. -/
theorem Input.initial_cover_at_vertex
    {a : Vertex R} (ha : color R a = false) :
    let C := K.map (QuotientGroup.mk' (pCore 2 H))
    letI : C.Normal := h.component_image_structure.2.1
    let ρ := NormalElementaryQuotient.representation
      (omegaCenterIn (pCore 2 H)) (QuotientGroup.mk' (pCore 2 H))
      (QuotientGroup.mk'_surjective _)
      ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)
    let s := MovedSection.ofNormal ρ C
    ∃ E : BinaryField, E.degree = n ∧
      ∃ e : ActionEquiv (s.action.comp C.subtype) (binaryNatural (K := E.Carrier)),
        IsCover (MovedSection.coverProjection s e) ∧
        ∃ j : Multiplicative s.space.toSubmodule →* FreeAmalgam R,
          Function.Injective j ∧ j.range = U R a ∧
          ∃ f : Ltilde R a →* commutator (Matrix.symplecticGroup (Fin 2) E.Carrier),
            Function.Surjective f ∧
            (∀ (k : Ltilde R a) (v : s.space.toSubmodule),
              j (Multiplicative.ofAdd (MovedSection.coverAction s e (f k) v)) =
                (k:FreeAmalgam R) * j (Multiplicative.ofAdd v) * (k:FreeAmalgam R)⁻¹) ∧
            (∀ v : s.space.toSubmodule, MovedSection.coverProjection s e v = 0 ↔
              j (Multiplicative.ofAdd v) ∈ centralizer (Ltilde R a : Set (FreeAmalgam R))) := by
  dsimp only
  let C := K.map (QuotientGroup.mk' (pCore 2 H))
  let : C.Normal := h.component_image_structure.2.1
  let q := QuotientGroup.mk' (pCore 2 H)
  let hq := QuotientGroup.mk'_surjective (pCore 2 H)
  let hk := (QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q hq hk) C
  obtain ⟨E,hE,e,he⟩ := h.centralOmega_initial_cover
  obtain ⟨i,hi,_,hiL,hiU⟩ := Sp4Four.LocalPackage.vertex_coordinates R ha
  rw [h.residual_eq] at hiL
  have hU : (⁅omegaOrbit R,K⁆).map i = U R a := by
    simpa only [Sp4Four.LocalPackage.initialLayer,h.residual_eq] using hiU
  let j := i.comp (ElementaryMovedCover.embedding (omegaCenterIn (pCore 2 H)) K q hq hk)
  refine ⟨E,hE,e,he,j,hi.comp (ElementaryMovedCover.embedding_injective _ _ _ _ _),?_,?_⟩
  · dsimp only [j]
    rw [MonoidHom.range_comp,ElementaryMovedCover.embedding_range,←h.initialCore_eq]
    exact hU
  · exact ElementaryMovedCover.exists_conjugationActor (omegaCenterIn (pCore 2 H))
      K q hq hk i hi (Ltilde R a) hiL e

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
