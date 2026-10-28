module

public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.ActionRigidity
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic.FrattiniCoordinates

/-!
# Correcting quartic radical coordinates to intertwine the intrinsic action

An explicit group equivalence over the marked Frattini core transports the
actual complement action to the intrinsic model. Action rigidity corrects this
equivalence by a linear sign change. The resulting equivalence intertwines
conjugation by the original section with the intrinsic signed action, preserves
the literal core and natural projections, and agrees with the original
equivalence on Frattini. The original six-point section marking is retained.
The volume generator may be inverted, and this alternative is recorded.

This is the action-comparison step in Aschbacher–Smith I.2.2(6), printed
pp.410 and 412 / PDF pp.421 and 423, combined manuscript of 1 March 2004.
Group recognition remains an explicit input, owned by the final hexad assembly.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
universe u
variable {K : Type u} [Group K]
variable {e : (K ⧸ center K) ≃* M22}
variable {B : Finset (Fin 22)} {hB : B ∈ m22Blocks}

/-- Correct an explicit group recognition over the marked core so that it
intertwines the same complement with the intrinsic signed action. -/
theorem FrattiniCoordinates.exists_equivariant_equiv
    (d : FrattiniCoordinates e hB)
    (E : hexadRadical e B ≃* EvenCliffordSix.Model)
    (hE : ∀ r, EvenCliffordSix.projection (E r) = d.coreMap r) :
    ∃ E' : hexadRadical e B ≃* EvenCliffordSix.Model,
      (∀ r, EvenCliffordSix.projection (E' r) = d.coreMap r) ∧
      (∀ a r, E' (hexadConjugation e B (d.sectionHom a) r) =
        EvenCliffordSix.action a (E' r)) ∧
      (∀ r ∈ frattini (hexadRadical e B), E' r = E r) ∧
      (∀ r, EvenCliffordSix.naturalProjection (E' r) = Binary.naturalMap e hB r) ∧
      (E' (E.symm EvenCliffordSix.volume) = EvenCliffordSix.volume ∨
        E' (E.symm EvenCliffordSix.volume) = EvenCliffordSix.volume⁻¹) ∧
      (∀ a, hexadSixMap e hB (d.sectionHom a) = m22HexadMarking hB a) := by
  let φ := (hexadConjugation e B).comp d.sectionHom
  let ψ : EvenCliffordSix.A →* MulAut EvenCliffordSix.Model :=
    (MulAut.congr E).toMonoidHom.comp φ
  have hψ (a : EvenCliffordSix.A) (x : EvenCliffordSix.Model) :
      (EvenCliffordSix.projection (ψ a x)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) a.val
          (EvenCliffordSix.projection x).toAdd := by
    change (EvenCliffordSix.projection
      (E (hexadConjugation e B (d.sectionHom a) (E.symm x)))).toAdd = _
    rw [hE, d.equivariant, ← hE, E.apply_symm_apply]
  obtain ⟨T, hTcore, hTact, _, hTvol, hTsign⟩ :=
    EvenCliffordSix.exists_action_comparison ψ hψ
  refine ⟨E.trans T, ?_, ?_, ?_, ?_, ?_, d.section_marking⟩
  · intro r
    exact (hTcore (E r)).trans (hE r)
  · intro a r
    have h := hTact a (E r)
    change T (E (hexadConjugation e B (d.sectionHom a) (E.symm (E r)))) =
      EvenCliffordSix.action a (T (E r)) at h
    simpa only [MulEquiv.trans_apply, E.symm_apply_apply] using h
  · intro r hr
    apply hTsign
    change EvenCliffordSix.projection (E r) = 1
    rw [hE]
    exact (d.kernel.symm ▸ hr : r ∈ d.coreMap.ker)
  · intro r
    apply Multiplicative.toAdd.injective
    change BinaryPermutation.coreToNatural (Fin 6)
      (EvenCliffordSix.projection (T (E r))).toAdd = _
    rw [hTcore, hE, d.natural_projection]
  · simpa only [MulEquiv.trans_apply, E.apply_symm_apply] using hTvol

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic
