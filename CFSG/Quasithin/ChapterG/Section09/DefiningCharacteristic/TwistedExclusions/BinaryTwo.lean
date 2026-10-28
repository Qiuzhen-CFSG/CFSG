module

public import CFSG.Quasithin.ChapterG.Section09.Setup
public import Theory.Representation.Triality.BinaryTwoObstruction

/-!
# The remaining binary triality endpoint in G.9.3

Under the literal component hypothesis, the triality model at field order two
and the actor bound m ≤ 5 force d = 12 and m = 5. The proof transports the
faithful component action along the actual model isomorphism and applies the
order-thirteen lower bound. Whole-group order divisibility still holds at this
endpoint. Neither actual root parabolic can contain a subgroup of order 49;
the last theorem retains the precise map from the source component.

These results delimit the unresolved case. They do not exclude triality or
discharge the universal degree premise of `not_triality_of_estimates`.
In particular, the automorphism-rank estimate supplying m ≤ 5 and the stronger
representation obstruction remain separate obligations of the assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, G.9.3, printed
p.356 (PDF p.367), `refs/quasithin.pdf`.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions

universe u v

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
  {A L : Subgroup G} {m : ℕ}

/-- The actual G.9 hypotheses leave exactly degree twelve and actor rank five. -/
theorem triality_two_endpoint
    (h : ComponentHypothesis K ρ A L L m)
    (model : Triality.Standard.IsTrialityGroupAt 2 L) (hm : m ≤ 5) :
    Module.finrank (ZMod 2) V = 12 ∧ m = 5 := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_two_iff L).mp model
  have hd := Triality.BinaryTwoObstruction.degree_ge_twelve
    ((ρ.comp L.subtype).comp e.symm.toMonoidHom)
    ((h.faithful.comp L.subtype_injective).comp e.symm.injective)
  have hu := h.degree_le
  omega

omit [Finite G] in
/-- The literal component order passes the necessary GL₁₂ divisibility test. -/
theorem triality_two_order_test
    (model : Triality.Standard.IsTrialityGroupAt 2 L) :
    Nat.card L ∣ Nat.card (Matrix.GeneralLinearGroup (Fin 12) (ZMod 2)) := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_two_iff L).mp model
  rw [Nat.card_congr e.toEquiv]
  exact Triality.BinaryTwoObstruction.card_dvd_GL_twelve

omit [Finite G] in
/-- An order-49 subgroup of the component cannot map into either actual root
parabolic. This asserts no existence or normalizer shape for such a subgroup. -/
theorem triality_two_parabolic_obstruction
    (model : Triality.Standard.IsTrialityGroupAt 2 L) :
    ∃ e : L ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one,
      ∀ R : Subgroup L, 49 ∣ Nat.card R →
        ∀ a : Triality.Standard.Parabolics.Node,
          ¬ R.map e.toMonoidHom ≤
            Triality.Standard.Parabolics.parabolic
              (Triality.Standard.binaryParameters 1 Nat.zero_lt_one) a := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_two_iff L).mp model
  refine ⟨e, fun R hR a => ?_⟩
  apply Triality.BinaryTwoObstruction.not_le_parabolic_of_fortyNine_dvd
  rwa [Subgroup.card_map_of_injective e.injective]

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions
