module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPointUnitary
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPlaneUnitary

/-!
# Both literal ordinary unitary endpoints

In the ordinary source branch the plane has order 960. The symmetric affine
alternative has order 1920, so the marked plane equivalence is necessarily
the ordinary unitary one. Together with NormalPointUnitary, this removes all
independent endpoint-recognition premises from the ordinary branch of
Aschbacher--Smith 13.5.17, printed p.922. The restriction maps on the common
Borel must still be made compatible before asserting an amalgam isomorphism.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ChapterF.GreenBook.LieModels.UnitaryFour
open ChapterF.UnitaryTwo
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

/-- The ordinary source branch selects the literal marked unitary plane. -/
theorem source_normal_ordinary_plane_unitary
    (hordinary : L ⊔ (T : Subgroup G) = L) :
    ∃ E : (L ⊔ (T : Subgroup G) : Subgroup G) ≃* planeParabolic 1 (Nat.le_refl 1),
      (V.subgroupOf (L ⊔ (T : Subgroup G))).map E.toMonoidHom =
        pCore 2 (planeParabolic 1 (Nat.le_refl 1)) ∧
      (V₁.subgroupOf (L ⊔ (T : Subgroup G))).map E.toMonoidHom =
        zpowers ModelClasses.longRight ∧
      ((residualCentralizer L V₁ ⊔ (T : Subgroup G)).subgroupOf
        (L ⊔ (T : Subgroup G))).map E.toMonoidHom =
        (overlap 1 (Nat.le_refl 1)).subgroupOf (planeParabolic 1 (Nat.le_refl 1)) := by
  rcases source_normal_plane_unitary_or_symmetric d hA312 hH hU hn with h | ⟨e,_,_,_⟩
  · exact h
  · have hsrc : Nat.card (L ⊔ (T : Subgroup G) : Subgroup G) = 960 := by
      rw [hordinary]
      exact normal_local_card d hA312 hH hU hn
    have hmodel : Nat.card (Multiplicative (BinaryPermutation.core (Fin 5)) ⋊[
        BinaryPermutation.AlternatingFiveExtension.coreAction] Equiv.Perm (Fin 5)) = 1920 := by
      rw [SemidirectProduct.card]
      have hV : Nat.card (Multiplicative (BinaryPermutation.core (Fin 5))) = 16 := by
        change Nat.card (BinaryPermutation.core (Fin 5)) = 16
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
          BinaryPermutation.finrank_core]
        rfl
      rw [hV,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
      decide
    have hc := Nat.card_congr e.toEquiv
    rw [hsrc,hmodel] at hc
    contradiction

end CFSG.Quasithin.Chapter13.Section05.A5Source
