module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPlaneModel
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.AffinePlane

/-!
# The literal unitary plane in the original normal A₅ branch

The source plane model preserves the module V, its distinguished line V₁,
and the common subgroup L₁T. Composing its ordinary affine alternative with
the binary Hermitian model yields the literal U₄(2) plane parabolic, its
2-core, its long-root line, and its flag overlap. The full symmetric affine
alternative remains explicit for the extended branch.

Source: Aschbacher–Smith 13.5.17, printed p.922, using the Chapter F binary
unitary model F.4.27 and F.4.43.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.CentralizerReduction Section06.TerminalContradiction.Ratio Section08
open BinaryPermutation BinaryPermutation.FiveCentralizerGeometry
open ChapterF.GreenBook.LieModels.UnitaryFour

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
  (hn : ((residualCentralizer L V₁).subgroupOf H).Normal)
include d hA312 hH hU hn


/-- The ordinary original plane endpoint is the literal U₄(2) plane
parabolic, with its module, central line, and overlap all identified by one
isomorphism; the alternative is the symmetric affine five-point group. -/
theorem source_normal_plane_unitary_or_symmetric :
    (∃ E : (L ⊔ (T : Subgroup G) : Subgroup G) ≃* planeParabolic 1 (Nat.le_refl 1),
      (V.subgroupOf (L ⊔ (T : Subgroup G))).map E.toMonoidHom =
        pCore 2 (planeParabolic 1 (Nat.le_refl 1)) ∧
      (V₁.subgroupOf (L ⊔ (T : Subgroup G))).map E.toMonoidHom =
        zpowers ChapterF.UnitaryTwo.ModelClasses.longRight ∧
      ((residualCentralizer L V₁ ⊔ (T : Subgroup G)).subgroupOf
        (L ⊔ (T : Subgroup G))).map E.toMonoidHom =
        (overlap 1 (Nat.le_refl 1)).subgroupOf (planeParabolic 1 (Nat.le_refl 1))) ∨
    (∃ E : (L ⊔ (T : Subgroup G) : Subgroup G) ≃*
        Multiplicative (core (Fin 5)) ⋊[AlternatingFiveExtension.coreAction] Equiv.Perm (Fin 5),
      (V.subgroupOf (L ⊔ (T : Subgroup G))).map E.toMonoidHom =
        (SemidirectProduct.inl : Multiplicative (core (Fin 5)) →*
          Multiplicative (core (Fin 5)) ⋊[AlternatingFiveExtension.coreAction] Equiv.Perm (Fin 5)).range ∧
      (V₁.subgroupOf (L ⊔ (T : Subgroup G))).map E.toMonoidHom =
        zpowers (SemidirectProduct.inl (Multiplicative.ofAdd z)) ∧
      ((residualCentralizer L V₁ ⊔ (T : Subgroup G)).subgroupOf
        (L ⊔ (T : Subgroup G))).map E.toMonoidHom =
        centralizer ({SemidirectProduct.inl (Multiplicative.ofAdd z)} :
          Set (Multiplicative (core (Fin 5)) ⋊[AlternatingFiveExtension.coreAction] Equiv.Perm (Fin 5)))) := by
  rcases source_normal_plane_marked_models d hA312 hH hU hn with ⟨e,hV,hline,hB⟩ | h
  · obtain ⟨f,hz,hR,hC⟩ := ChapterF.UnitaryTwo.AffinePlane.exists_marked_plane_equiv
    refine Or.inl ⟨e.trans f,?_,?_,?_⟩
    · change (V.subgroupOf (L ⊔ (T : Subgroup G))).map
        (f.toMonoidHom.comp e.toMonoidHom) = _
      rw [←map_map,hV,hR]
    · change (V₁.subgroupOf (L ⊔ (T : Subgroup G))).map
        (f.toMonoidHom.comp e.toMonoidHom) = _
      rw [←map_map,hline,MonoidHom.map_zpowers]
      exact congrArg zpowers hz
    · change ((residualCentralizer L V₁ ⊔ (T : Subgroup G)).subgroupOf
        (L ⊔ (T : Subgroup G))).map (f.toMonoidHom.comp e.toMonoidHom) = _
      rw [←map_map,hB,hC]
  · exact Or.inr h

end CFSG.Quasithin.Chapter13.Section05.A5Source
