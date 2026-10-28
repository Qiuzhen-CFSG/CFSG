module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.Reciprocal.Action
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Linear.SmallCommutator

/-!
# Reciprocal field lines in the actual SL₃ module

The forward natural coordinates give order q for [A,⟨w⟩]. Conjugate this
literal subgroup back by g⁻¹. The proved small-commutator theorem excludes a
field twist in its involutory actor and recognizes a field line of the original
chosen SL₃ module. Conjugating forward recovers the same commutator in A.
No alignment, equality A=V, or reciprocal transvection hypothesis is used.

Source: Aschbacher--Smith, 11.3.7(4), refs/quasithin.pdf, printed p.773.
-/

@[expose] public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Reciprocal
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
  {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- Field-linearity of the actual reciprocal W action in the SL₃ marking.
Every actor is compared with its own small cyclic commutator, rather than
assuming that the whole reciprocal group already consists of transvections. -/
theorem sl3_reciprocal_action_linear
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 a)) (g : G) {m : ℕ}
    (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field m)
    (hN : omegaClosure T H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    ∀ (w : omegaClosure T H) (r : S.field.Carrier) v,
      reciprocalAction (.sl3 a) g hN w (r • v) =
        r • reciprocalAction (.sl3 a) g hN w v := by
  let E : Closure.Geometry D :=
    { input := S
      point := (Coordinates.sl3 a).binarySubspace (f.space 0)
      plane := (Coordinates.sl3 a).binarySubspace (f.space 1)
      threeSpace := (Coordinates.sl3 a).binarySubspace (f.space 2)
      X := ⊥, z := g, H := H }
  intro w r v
  let B := (zpowers (w : G)).map (MulAut.conj g⁻¹).toMonoidHom
  have hBV := cyclic_normalizes_seed g hN w
  have hBL := hBV.trans (WeakClosure.seed_normalizer_le D S)
  let b : B := ⟨(MulAut.conj g⁻¹) (w : G),
    mem_map_of_mem _ (mem_zpowers (w : G))⟩
  have hcard := cyclic_commutator_card_le g n w
  have hl := Closure.Amalgam.Even.Linear.linear_of_commutator_card_le
    (E := E) a B hBL hBV b (cyclic_square_eq_one g n w b) hcard r v
  change Closure.Amalgam.Even.Linear.normalizerAction (E := E) a
      (inclusion hBV b) (r • v) =
    r • Closure.Amalgam.Even.Linear.normalizerAction (E := E) a
      (inclusion hBV b) v
  rw [Closure.Amalgam.Even.Linear.normalizerAction_restrict (E := E) a B hBL hBV,
    Closure.Amalgam.Even.Linear.normalizerAction_restrict (E := E) a B hBL hBV]
  exact hl

/-- Recognition of every nontrivial individual displacement in the SL₃ branch.
The auxiliary closure record packages only the supplied input and flag data;
its later critical-distance conclusions are neither assumed nor used. -/
theorem sl3_commutator_field_line
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 a))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (g : G) {m : ℕ}
    (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field m)
    (hN : omegaClosure T H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (w : omegaClosure T H)
    (hw : (w : G) ∉ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    ∃ U : Submodule S.field.Carrier (Coordinates.sl3 a).Space,
      Module.finrank S.field.Carrier U = 1 ∧
      ⁅V.map (MulAut.conj g).toMonoidHom, zpowers (w : G)⁆ =
        ((Coordinates.sl3 a).preimage U).map (MulAut.conj g).toMonoidHom := by
  let E : Closure.Geometry D :=
    { input := S
      point := (Coordinates.sl3 a).binarySubspace (f.space 0)
      plane := (Coordinates.sl3 a).binarySubspace (f.space 1)
      threeSpace := (Coordinates.sl3 a).binarySubspace (f.space 2)
      X := ⊥, z := g, H := H }
  let B := (zpowers (w : G)).map (MulAut.conj g⁻¹).toMonoidHom
  have hc := cyclic_commutator_eq (V := V) g w
  have hne : ⁅B, V⁆ ≠ ⊥ := by
    rw [hc]
    intro he
    exact NaturalSylowCoordinates.vector_commutator_ne_bot w hw
      ((map_eq_bot_iff_of_injective _ (MulAut.conj g⁻¹).injective).mp he)
  have hcard : Nat.card (⁅B, V⁆ : Subgroup G) ≤ Nat.card S.field.Carrier := by
    rw [hc, card_map_of_injective (MulAut.conj g⁻¹).injective,
      n.card_vector_commutator w hw]
  have hsq : ∀ b : B, b ^ 2 = 1 := cyclic_square_eq_one g n w
  obtain ⟨U, hU, he⟩ := Closure.Amalgam.Even.Linear.commutator_isFieldLine_of_card_le
    (E := E) a hfixed B (cyclic_normalizes_seed g hN w) hsq hne hcard
  refine ⟨U, hU, ?_⟩
  have hh := congrArg (map (MulAut.conj g).toMonoidHom) he
  rw [hc, map_conj_inv_conj] at hh
  exact hh.symm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Reciprocal
