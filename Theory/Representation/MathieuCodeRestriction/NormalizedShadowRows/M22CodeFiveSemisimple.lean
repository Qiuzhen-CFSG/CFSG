module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeChiefProjection
public import Theory.Representation.NormalSemisimpleSpan
import all Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeCommutant
import all Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeFiveAction

/-!
# The M22 quintet cannot embed in a semisimple module

The native five-space is a nonsplit extension of the trivial line by its
irreducible moved four-space. Every equivariant map from this quintet to a
semisimple module therefore kills the moved four-space. This is used to
identify the normal-closure intersection with the original B/U in 8.2.9.
Source: Aschbacher--Smith H.16.3(3) and 8.2.9, pp.403,721.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Sporadic.Mathieu MathieuCode MathieuCode.M22Quintet MathieuCode.M22Quintet.CocodeTransfer
open scoped IsMulCommutative MonoidAlgebra
namespace MathieuCode.NormalizedShadowRows.M22CodeSection
open M22ChapterH.Quintet

theorem fiveAction_not_semisimple : ¬ IsSemisimpleRepresentation fiveAction := by
  intro h
  let := h
  obtain ⟨C,hC⟩ := exists_isCompl fiveInner
  rcases five_subrepresentation C with hz | hle
  · have ht : fiveInner = ⊤ := by
      simpa only [hz,sup_bot_eq] using hC.sup_eq_top
    have hd := fiveInner_dim
    rw [ht] at hd
    change Module.finrank (ZMod 2)
      (⊤ : Submodule (ZMod 2) (Additive M22Quintet.K)) = 4 at hd
    rw [finrank_top,kernel_finrank] at hd
    omega
  · have hz : fiveInner = ⊥ := by
      rw [←inf_eq_left.mpr hle]
      exact hC.inf_eq_bot
    have hd := fiveInner_dim
    rw [hz] at hd
    change Module.finrank (ZMod 2)
      (⊥ : Submodule (ZMod 2) (Additive M22Quintet.K)) = 4 at hd
    rw [finrank_bot] at hd
    omega

/-- In particular, a nonzero projection on the moved four-space cannot be
extended over the whole five-space into a semisimple target. -/
theorem five_map_to_semisimple_kills_moved
    {R V : Type*} [Group R] [AddCommGroup V] [Module (ZMod 2) V]
    (r : R →* alternatingGroup (Fin 5)) (hr : Function.Surjective r)
    (τ : Representation (ZMod 2) R V)
    [IsSemisimpleModule (ZMod 2)[R] τ.asModule]
    (F : Representation.IntertwiningMap (fiveAction.comp r) τ) :
    fiveMoved.toSubmodule ≤ F.toLinearMap.ker := by
  let K : Subrepresentation fiveAction := {
    toSubmodule := F.toLinearMap.ker
    apply_mem_toSubmodule g v hv := by
      obtain ⟨a,rfl⟩ := hr g
      change F (fiveAction (r a) v) = 0
      change F v = 0 at hv
      calc
        _ = τ a (F v) := LinearMap.congr_fun (F.isIntertwining' a) v
        _ = 0 := by rw [hv,map_zero] }
  have hKn : K ≠ ⊥ := by
    intro hk
    have hker : F.toLinearMap.ker = ⊥ := congrArg Subrepresentation.toSubmodule hk
    have hi : Function.Injective F := LinearMap.ker_eq_bot.mp hker
    let a := IntertwiningMap.equivLinearMapAsModule (fiveAction.comp r) τ F
    let : IsSemisimpleModule (ZMod 2)[R] (Representation.asModule (fiveAction.comp r)) :=
      IsSemisimpleModule.of_injective a hi
    have hs : IsSemisimpleModule (ZMod 2)[alternatingGroup (Fin 5)] fiveAction.asModule :=
      (semisimple_comp_iff_of_surjective fiveAction r hr).mp inferInstance
    exact fiveAction_not_semisimple
      ((isSemisimpleRepresentation_iff_isSemisimpleModule_asModule fiveAction).mpr hs)
  have hm := (five_subrepresentation K).resolve_left hKn
  rw [fiveMoved_eq_inner]
  exact hm

end MathieuCode.NormalizedShadowRows.M22CodeSection
