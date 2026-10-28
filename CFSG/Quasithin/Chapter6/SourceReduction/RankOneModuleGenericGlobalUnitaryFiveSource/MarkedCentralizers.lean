module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.CentralizerSylow
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.Marked

/-!
# Centralizer two-parts and fusion on the exact unitary-five marking

The full ambient plane normalizer controls fusion on its core center and
contains a Sylow subgroup of each point centralizer. The same marked endpoint
map therefore preserves those conjugacy relations and centralizer two-parts.
Both orientations retain all endpoint, whole-overlap and carrier/range equations
from the published realization, on the identical extension.

This supplies the inner centralizer comparison used in F.4.37–40.
Full ambient short-root centralizer equality still requires F.4.42.
Source: Aschbacher–Smith F.4.35–40, printed pp.292–294.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem endpoint_isConj_iff {B : Type*} [Group B]
    (e : normalizer (L : Set G) ≃* B) (x y : normalizer (L : Set G)) :
    IsConj x y ↔ IsConj (e x) (e y) := by
  constructor
  · exact e.toMonoidHom.map_isConj
  · intro hh
    have hh' : IsConj (e.symm (e x)) (e.symm (e y)) := e.symm.toMonoidHom.map_isConj hh
    simpa only [e.symm_apply_apply] using hh'

/-- Literal endpoint comparison of fusion and centralizer two-parts,
retaining the complete marking of the same extension. -/
theorem Preparation.unitaryFive_marked_plane_centralizers
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U) :
    (∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam,
      ∃ f : UnitaryNativeLift.Five.Lift U a,
      ∃ F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H)) r.extension.amalgam,
        (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
        (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
        (∀ z, (F.middle z).val = (f.action z).val) ∧
        r.extension.carrier = inner U.Carrier ⊔
          ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
        r.extension.left = U.leftParabolic.map MulAut.conj ⊔
          ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
        r.extension.right = U.rightParabolic.map MulAut.conj ⊔
          ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
        r.extension.middle =
          ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
        (∀ x : normalizer (L : Set G),
          x.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype →
          (Nat.card (centralizer ({x.val} : Set G))).factorization 2 =
            (Nat.card (centralizer ({F.left x} : Set r.extension.left))).factorization 2) ∧
        (∀ x y : normalizer (L : Set G),
          x.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype →
          y.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype →
          (IsConj x.val y.val ↔ IsConj (F.left x) (F.left y)))) ∨
    (∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam.reverse,
      ∃ f : UnitaryNativeLift.Five.LiftReverse U a,
      ∃ F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H)) r.extension.amalgam.reverse,
        (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
        (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
        (∀ z, (F.middle z).val = (f.action z).val) ∧
        r.extension.carrier = inner U.Carrier ⊔
          ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
        r.extension.left = U.leftParabolic.map MulAut.conj ⊔
          ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
        r.extension.right = U.rightParabolic.map MulAut.conj ⊔
          ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
        r.extension.middle =
          ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
        (∀ x : normalizer (L : Set G),
          x.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype →
          (Nat.card (centralizer ({x.val} : Set G))).factorization 2 =
            (Nat.card (centralizer ({F.left x} : Set r.extension.right))).factorization 2) ∧
        (∀ x y : normalizer (L : Set G),
          x.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype →
          y.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype →
          (IsConj x.val y.val ↔ IsConj (F.left x) (F.left y)))) := by
  rcases r.marking with ⟨a,f,F,h0,h1,hD,hE,hleft,hright,hmiddle⟩ |
    ⟨a,f,F,h0,h1,hD,hE,hleft,hright,hmiddle⟩
  · apply Or.inl
    refine ⟨a,f,F,h0,h1,hD,hE,hleft,hright,hmiddle,?_,?_⟩
    · intro x hx
      exact (d.unitaryFive_plane_center_centralizer_two_part h hH hp U hc x hx).trans
        (congrArg (fun k : ℕ => k.factorization 2)
          (Nat.card_congr (CentralizerSmallKernelTransport.centralizerEquiv F.left x).toEquiv))
    · intro x y hx hy
      exact (d.unitaryFive_plane_center_local_fusion h hH hp U hc x y hx hy).trans
        (endpoint_isConj_iff F.left x y)
  · apply Or.inr
    refine ⟨a,f,F,h0,h1,hD,hE,hleft,hright,hmiddle,?_,?_⟩
    · intro x hx
      exact (d.unitaryFive_plane_center_centralizer_two_part h hH hp U hc x hx).trans
        (congrArg (fun k : ℕ => k.factorization 2)
          (Nat.card_congr (CentralizerSmallKernelTransport.centralizerEquiv F.left x).toEquiv))
    · intro x y hx hy
      exact (d.unitaryFive_plane_center_local_fusion h hH hp U hc x y hx hy).trans
        (endpoint_isConj_iff F.left x y)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
