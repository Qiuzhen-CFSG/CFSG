/-
Comparator challenge for the converse direction of the Bender-Suzuki theorem.

The four statements below, together with `Defs.lean`, are everything a human must audit.
The import closure is Mathlib plus `Defs.lean`; no declaration of this repository is in
the trusted base.

The claims are: each of three explicitly defined groups satisfies Hypothesis (A), and
Hypothesis (A) forces the point stabiliser to be strongly embedded.  Composing 1 with each
of 2-4 gives that each group has a strongly embedded subgroup.  If you believe Bender's
classification of the groups with a strongly embedded subgroup, the three must be the
known families -- whatever their definitions happen to look like.

There are deliberately no entries in `definition_names`.  A definition hole would let a
solution define `IsStronglyEmbedded := fun _ => True` and discharge everything by
`trivial`.
-/
import BenderSuzukiConverse.Defs

namespace BSConverse

universe u v

/-- **1. Hypothesis (A) makes the point stabiliser strongly embedded.** -/
theorem hypothesisA_stronglyEmbedded {G : Type u} {Ω : Type v}
    [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t : G} (hA : HypothesisA G Ω H D Q t) :
    IsStronglyEmbedded H := sorry

/-- **2. `PSL(2, 2ᵏ)` satisfies Hypothesis (A)** for every `k ≥ 2`. -/
theorem psl2_hypothesisA (k : ℕ) (hk : 2 ≤ k) :
    ∃ (_ : Finite (PSL2Model k)) (Ω : Type) (_ : Finite Ω)
      (act : MulAction (PSL2Model k) Ω)
      (H D Q : Subgroup (PSL2Model k)) (t : PSL2Model k),
      @HypothesisA (PSL2Model k) Ω _ _ act _ H D Q t := sorry

/-- **3. `Sz(2^(2m+1))` satisfies Hypothesis (A)** for every `m ≥ 1`. -/
theorem suzuki_hypothesisA (m : ℕ) (hm : 0 < m) :
    ∃ (_ : Finite (SzModel m)) (Ω : Type) (_ : Finite Ω) (act : MulAction (SzModel m) Ω)
      (H D Q : Subgroup (SzModel m)) (t : SzModel m),
      @HypothesisA (SzModel m) Ω _ _ act _ H D Q t := sorry

/-- **4. `PSU(3, 2ᵏ)` satisfies Hypothesis (A)** for every `k ≥ 2`: for a field of order
`(2ᵏ)²` whose fixed field has order `2ᵏ`, and the Hermitian form with antidiagonal Gram
matrix. -/
theorem psu3_hypothesisA (k : ℕ) (hk : 2 ≤ k) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
      J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
      Nat.card E = (2 ^ k) ^ 2 ∧
      Nat.card {z : E // J.conj z = z} = 2 ^ k ∧
      ∃ (_ : Finite (PSUModel J)) (Ω : Type) (_ : Finite Ω)
        (act : MulAction (PSUModel J) Ω)
        (H D Q : Subgroup (PSUModel J)) (t : PSUModel J),
        @HypothesisA (PSUModel J) Ω _ _ act _ H D Q t := sorry

end BSConverse
