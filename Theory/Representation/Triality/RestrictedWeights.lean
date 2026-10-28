module

public import Theory.AlgebraicGroup.RootSystems.TypeD4RestrictedWeights
public import Theory.AlgebraicGroup.Representations.Algebraic.WeightSpaces

/-!
# D4 basic-weight dimension bounds from genuine torus actions

Distinct algebraic torus characters have independent weight spaces. The explicit
D4 reflection words therefore give dimension at least eight whenever a nonzero
binary weight occurs in a representation with reflection-invariant support. For
a nonzero weight fixed by the pinned arm cycle, they give dimension at least
twenty-four. The support invariance is also derived here from actual conjugation
by four ambient group elements and their action on torus characters.

These statements apply to every basic highest-weight alternative, including the
single-factor case used when the finite field parameter is two. They do not
construct the simply connected D4 setup or classify its finite fixed-point
representations. In particular, the weight embedding, conjugation equations and
weight occurrence must still be proved for the genuine algebraic model before
assembling `Triality.BinaryDegree.TensorData`.

Sources: GLS3 §§1.14 and 2.8 (`refs/KGroup/GLS3/chapter2.tex`); Aschbacher--Smith,
printed p.356 (PDF p.367). No theorem from the unresolved bundled `theorem_1_14_6`
is used.
-/

public section

namespace Theory.AlgebraicGroup
open StandardRootSystem.D4RestrictedWeight
universe u v
variable {k : Type u} [Field k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The enumerated Weyl conjugates contribute independent nonzero weight spaces. -/
theorem d4_weight_witnesses_card_le_finrank
    (ρ : RationalRepresentation K V) (T : ClosedSubgroup K)
    (e : Weight ↪ TorusWeight T)
    (hreflection : ∀ (i : Fin 4) (a : Weight),
      weightSpace ρ T (e a) ≠ ⊥ → weightSpace ρ T (e (reflection i a)) ≠ ⊥)
    (a : BasicWeight) (ha : weightSpace ρ T (e (coefficient a)) ≠ ⊥) :
    (witnesses a).card ≤ Module.finrank k V := by
  classical
  have hs := witnesses_subset hreflection ha
  have hex : ∀ b : witnesses a,
      ∃ v ∈ weightSpace ρ T (e b), v ≠ (0 : V) := by
    intro b
    exact (Submodule.ne_bot_iff _).mp (hs b.property)
  choose w hw hne using hex
  have hinj : Function.Injective (fun b : witnesses a => e (b : Weight)) :=
    e.injective.comp Subtype.val_injective
  have hlin := ((weightSpace_iSupIndep ρ T).comp hinj).linearIndependent _ hw hne
  simpa using hlin.fintype_card_le_finrank

/-- The absolute lower bound for any nonzero binary D4 weight. -/
theorem d4_basic_finrank_ge_eight
    (ρ : RationalRepresentation K V) (T : ClosedSubgroup K)
    (e : Weight ↪ TorusWeight T)
    (hreflection : ∀ (i : Fin 4) (a : Weight),
      weightSpace ρ T (e a) ≠ ⊥ → weightSpace ρ T (e (reflection i a)) ≠ ⊥)
    (a : BasicWeight) (ha : weightSpace ρ T (e (coefficient a)) ≠ ⊥)
    (hne : a ≠ zeroWeight) : 8 ≤ Module.finrank k V :=
  (eight_le_card_witnesses a hne).trans
    (d4_weight_witnesses_card_le_finrank ρ T e hreflection a ha)

/-- The stronger bound for any nonzero diagram-fixed binary D4 weight. -/
theorem d4_fixed_basic_finrank_ge_twenty_four
    (ρ : RationalRepresentation K V) (T : ClosedSubgroup K)
    (e : Weight ↪ TorusWeight T)
    (hreflection : ∀ (i : Fin 4) (a : Weight),
      weightSpace ρ T (e a) ≠ ⊥ → weightSpace ρ T (e (reflection i a)) ≠ ⊥)
    (a : BasicWeight) (ha : weightSpace ρ T (e (coefficient a)) ≠ ⊥)
    (hne : a ≠ zeroWeight) (hfix : diagramAction a = a) : 24 ≤ Module.finrank k V :=
  (twenty_four_le_card_witnesses a hne hfix).trans
    (d4_weight_witnesses_card_le_finrank ρ T e hreflection a ha)

omit [FiniteDimensional k V] in
/-- Actual normalizer conjugation transports a nonzero weight space to its simple reflection. -/
theorem d4_weightSpace_reflection_of_conjugation
    (ρ : RationalRepresentation K V) (T : ClosedSubgroup K)
    (e : Weight ↪ TorusWeight T)
    (g : Fin 4 → Variety.Point K)
    (c : Fin 4 → Variety.Point T.carrierVariety → Variety.Point T.carrierVariety)
    (hconj : ∀ i t, T.includePoint t * g i = g i * T.includePoint (c i t))
    (hchar : ∀ i a t,
      (e (reflection i a)).pointCharacter t = (e a).pointCharacter (c i t))
    (i : Fin 4) (a : Weight) (ha : weightSpace ρ T (e a) ≠ ⊥) :
    weightSpace ρ T (e (reflection i a)) ≠ ⊥ := by
  obtain ⟨v, hv, hvne⟩ := (Submodule.ne_bot_iff _).mp ha
  refine (Submodule.ne_bot_iff _).mpr ⟨(ρ.action (g i)).1 v, ?_, ?_⟩
  · intro t
    calc
      (ρ.action (T.includePoint t)).1 ((ρ.action (g i)).1 v) =
          (ρ.action (T.includePoint t * g i)).1 v := by rw [map_mul]; rfl
      _ = (ρ.action (g i * T.includePoint (c i t))).1 v := by rw [hconj]
      _ = (ρ.action (g i)).1 ((ρ.action (T.includePoint (c i t))).1 v) := by
        rw [map_mul]; rfl
      _ = (e a).pointCharacter (c i t) • (ρ.action (g i)).1 v := by
        rw [hv (c i t), map_smul]
      _ = (e (reflection i a)).pointCharacter t • (ρ.action (g i)).1 v := by
        rw [hchar]
  · intro hzero
    have h := congrArg (fun w => (ρ.action (g i)⁻¹).1 w) hzero
    have hleft : (ρ.action (g i)⁻¹).1 ((ρ.action (g i)).1 v) = v := by
      change ((ρ.action (g i)⁻¹ * ρ.action (g i)).1 : Module.End k V) v = v
      simp
    rw [hleft, map_zero] at h
    exact hvne h

/-- Both D4 basic degree estimates, with weight-support invariance discharged
by actual ambient normalizers. There is no numerical lower-bound premise. -/
theorem d4_basic_finrank_lower_bounds_of_conjugation
    (ρ : RationalRepresentation K V) (T : ClosedSubgroup K)
    (e : Weight ↪ TorusWeight T)
    (g : Fin 4 → Variety.Point K)
    (c : Fin 4 → Variety.Point T.carrierVariety → Variety.Point T.carrierVariety)
    (hconj : ∀ i t, T.includePoint t * g i = g i * T.includePoint (c i t))
    (hchar : ∀ i a t,
      (e (reflection i a)).pointCharacter t = (e a).pointCharacter (c i t))
    (a : BasicWeight) (ha : weightSpace ρ T (e (coefficient a)) ≠ ⊥)
    (hne : a ≠ zeroWeight) :
    8 ≤ Module.finrank k V ∧
      (diagramAction a = a → 24 ≤ Module.finrank k V) := by
  have hreflection := d4_weightSpace_reflection_of_conjugation ρ T e g c hconj hchar
  exact ⟨d4_basic_finrank_ge_eight ρ T e hreflection a ha hne,
    fun hfix => d4_fixed_basic_finrank_ge_twenty_four ρ T e hreflection a ha hne hfix⟩

end Theory.AlgebraicGroup
