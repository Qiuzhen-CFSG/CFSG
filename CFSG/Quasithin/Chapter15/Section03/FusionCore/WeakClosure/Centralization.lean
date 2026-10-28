module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.Centralization.Normalizing
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.Centralization.CoreGeometry
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.Centralization.SingularPlane
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.Consequences

/-!
# Assembly for orthogonal weak-closure centralization

For every conjugate `A = V^g ≤ T`, split according to whether `V` normalizes
`A`. The mutually normalizing case is proved in `Normalizing`: singular
commutators give a fixed subgroup of index at most two, contradicting the
singularity bound after inverse conjugation.

In the nonnormalizing case, `CoreGeometry` computes the actual dual core
`U` and fixed subgroups: `|U| = 8`, `|C_U(A)| = 2`, and `|C_A(V)| = 4`.
Inverse conjugation makes `C_A(V)` a totally singular plane in `V`.
The pointwise fixer bound from `SingularPlane` then forces `8 ≤ 4`.

The final theorem discharges both calculations and proves the centralization
assertion of 15.3.46(4) from the earlier inputs and the explicit compatible
coordinate and fusion-calculation witnesses. Constructing those two witnesses
remains with the source assembly in `WeakClosure`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1141.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.Centralization

open Subgroup

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M V P : Subgroup G} [IsElementaryAbelian 2 V]

/-- Both source cases, with the remaining finite module calculations stated
explicitly. The core is the actual E.3.30 dual core of the induced automizer. -/
theorem weakClosure_zero_le_centralizer_of_core_calculations
    (d : NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (k : OrthogonalCoordinateModel d P)
    (c : OrthogonalFusionCalculations T M V P d.form)
    (hcore : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
      ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) →
      Nat.card (ChapterE.automizerDualCore V
        (ChapterE.inducedAutomizer V (V.map (MulAut.conj g).toMonoidHom)) 1) = 8 ∧
      Nat.card (ChapterE.automizerDualCore V
        (ChapterE.inducedAutomizer V (V.map (MulAut.conj g).toMonoidHom)) 1 ⊓
          centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) : Subgroup G) = 2 ∧
      Nat.card (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V : Set G) :
        Subgroup G) = 4)
    (hfixer : ∀ B X : Subgroup G, IsTotallySingular d.form B → Nat.card B = 4 →
      X ≤ M → X ≤ centralizer (B : Set G) →
      Nat.card X ≤ 2 * Nat.card (X ⊓ centralizer (V : Set G) : Subgroup G)) :
    ChapterE.indexedWeakClosure V T 0 ≤ centralizer (V : Set G) := by
  apply (weakClosure_zero_le_centralizer_iff V T).mpr
  intro g hgT
  by_cases hn : V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)
  · exact conjugate_le_centralizer_of_normalizes d h k c g hgT hn
  · obtain ⟨hU, hC, hB⟩ := hcore g hgT hn
    exact (false_of_not_normalizes_of_core_bounds d h c g hgT hn hU hC hB hfixer).elim

/-- The centralization assertion of 15.3.46(4), with both cases and all
dual-core and pointwise-fixer calculations discharged. Only the compatible
coordinate model and orbit-calculation witnesses remain explicit. -/
theorem weakClosure_zero_le_centralizer
    (d : NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (hP : IsDefinitePlane d.form P) (k : OrthogonalCoordinateModel d P)
    (c : OrthogonalFusionCalculations T M V P d.form) :
    ChapterE.indexedWeakClosure V T 0 ≤ centralizer (V : Set G) := by
  apply weakClosure_zero_le_centralizer_of_core_calculations d h k c
  · exact core_calculations_of_not_normalizes d h hP k c
  · intro B X hs hB hXM hXB
    exact card_le_two_mul_card_inf_centralizer_of_totallySingular d k hs hB hXM hXB

end CFSG.Quasithin.Chapter15.Section03.FusionCore.Centralization
