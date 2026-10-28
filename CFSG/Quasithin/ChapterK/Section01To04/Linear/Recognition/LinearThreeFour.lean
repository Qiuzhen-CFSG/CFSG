module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceFF.Natural
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceFF.TwistedExclusion.CanonicalDescent
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.CoverComparison
public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.Diagram
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison

/-!
# Recognition of the PSL₃(4) module with cubic ratio at most two

Apply the absolute natural/twisted alternatives of K.3.2 to the actual
faithful component action. The natural row would identify PSL₃(4) with
SL₃(4), contradicting their centers. In the twisted row the field degree
forces Schur degree one; binary descent supplies the Hermitian action
and its intertwining linear coordinates. No module-family label or
dimension-only identification is used as a recognition premise.

Source: Aschbacher–Smith K.3.2, printed p.454, used in 3.2.9(4),
pp.582–583, and 5.1.14, p.638 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Matrix.PSL3.LinearThree.OuterExtensions
namespace CFSG.Quasithin.ChapterK.Linear.Recognition
open ChapterB.QuasisimpleSource
open ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
universe u v
variable {A : Type u} [Group A] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) A W} {L : Subgroup A} {𝒦 : GroupClass.{u}}

private def four : BinaryField where
  Carrier := E 1
  degree := 2
  degree_pos := by decide
  card_eq := card_E 1

private theorem center_eq_bot (e : L ≃* PSL(3,E 1)) : center L = ⊥ := by
  have hz : center PSL(3,E 1) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot SL(3,E 1)
  apply Subgroup.card_eq_one.mp
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hz, Subgroup.card_bot]

/-- The source hypotheses recognize the actual faithful PSL₃(4) action,
including a linear intertwiner with the binary Hermitian tensor. -/
theorem linearThreeFour_hermitian_coordinates (h : SourceHypothesis 𝒦 ρ L)
    (e : L ≃* PSL(3,E 1)) :
    ∃ (j : L ≃* PSL(3,E 1)) (c : W ≃ₗ[ZMod 2] Space 1),
      ∀ (l : L) (w : W), c (ρ (l : A) w) = projectiveAction (j l) (c w) := by
  let := h.finite_group
  let := h.finite_module
  let eQ : L ⧸ center L ≃* PSL(3,E 1) :=
    (QuotientGroup.quotientMulEquivOfEq (center_eq_bot e)).trans
      ((QuotientGroup.quotientBot).trans e)
  obtain ⟨C, _⟩ := SourceFF.exists_linearCover h four eQ
  let := inflated_irreducible ρ C h.irreducible
  obtain ⟨_, hn | ht⟩ := SourceFF.absolute_models h C eQ
  · obtain ⟨d⟩ := SourceFF.naturalAction_of_absolute h C hn.1 hn.2.2
    have hc := Nat.card_congr (Subgroup.centerCongr d.groupEquiv).toEquiv
    rw [center_eq_bot e, Subgroup.card_bot] at hc
    change 1 = Nat.card (center SL(3,E 1)) at hc
    rw [Atlas.ExceptionalSupport.card_sl_center, card_E] at hc
    norm_num at hc
  · have hd : schurDegree (inflated ρ C) = 1 := by
      have h2 : 2 = 2 * schurDegree (inflated ρ C) := ht.1
      omega
    obtain ⟨a, ⟨f⟩⟩ := TwistedExclusion.exists_binary_hermitian_equiv 1
      (inflated ρ C) (card_E 1) hd (by simpa only [hd] using ht.2.2)
    let π := C.projection.comp a.toMonoidHom
    have hπ : Function.Surjective π := C.surjective.comp a.surjective
    let d := hermitianActionEquiv (ρ.comp L.subtype) 1 π hπ
      (h.faithful.comp L.subtype_injective) f
    let j := d.groupEquiv.trans ((binaryImageEquiv 1).symm.trans
      (imageEquivPSL 1 (by decide)))
    refine ⟨j,d.linearEquiv,?_⟩
    intro l w
    rw [show ρ (l : A) w = (ρ.comp L.subtype) l w from rfl, d.intertwines]
    change (d.groupEquiv l).val (d.linearEquiv w) =
      ((binaryImageEquiv 1) ((imageEquivPSL 1 (by decide)).symm
        ((imageEquivPSL 1 (by decide)) ((binaryImageEquiv 1).symm
          (d.groupEquiv l))))).val (d.linearEquiv w)
    rw [MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]

end CFSG.Quasithin.ChapterK.Linear.Recognition
