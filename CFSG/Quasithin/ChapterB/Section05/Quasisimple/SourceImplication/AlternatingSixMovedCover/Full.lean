module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.AlternatingSixMovedCover
/-!
# The full five-dimensional A₆ central cover

If the original Irr+ moved space has order thirty-two, its universal
six-letter augmentation cover is an isomorphism. The equivalence retains
the component action and the literal projection to the natural quotient.
No complement to the central fixed line is asserted.

Source: Aschbacher--Smith B.5.1 and I.1.5--6, pp.99--103 and408.
-/
public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) D V} {L : Subgroup D}
theorem MovedSection.alternatingSix_core_equiv_of_card
    (s : MovedSection ρ L) (hi : IsIrrPlus ρ L s.space.toSubmodule)
    (e : ActionEquiv (s.action.comp L.subtype) (alternatingNatural 6))
    (hc : Nat.card s.space.toSubmodule = 32) :
    ∃ f : BinaryPermutation.core (Fin 6) ≃ₗ[ZMod 2] s.space.toSubmodule,
      (∀ g : alternatingGroup (Fin 6), ∀ v,
        f (BinaryPermutation.coreRepresentation (Fin 6) g.val v) =
          s.space.toRepresentation (e.groupEquiv.symm g) (f v)) ∧
      ∀ v, e.linearEquiv (s.central.toSubmodule.mkQ (f v)) =
        BinaryPermutation.coreToNatural (Fin 6) v := by
  obtain ⟨f,hf,ha,hq⟩ := s.alternatingSix_core_quotient hi e
  have hd : Module.finrank (ZMod 2) s.space.toSubmodule = 5 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := s.space.toSubmodule)
    rw [hc,Nat.card_zmod] at h
    exact h.symm
  have he : Module.finrank (ZMod 2) (BinaryPermutation.core (Fin 6)) =
      Module.finrank (ZMod 2) s.space.toSubmodule := by
    rw [BinaryPermutation.finrank_core,hd]
    rfl
  exact ⟨LinearEquiv.ofBijective f
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank he).mpr hf,hf⟩,ha,hq⟩
end CFSG.Quasithin.ChapterB.QuasisimpleSource
