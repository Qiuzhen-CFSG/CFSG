module

public import Theory.SpecificGroups.G2.MarkedStrongClosure
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.MarkedQuotient
public import CFSG.Quasithin.ClassificationModels.Families

/-!
# Excluding the ordinary even-field G₂ models in the Bender inspection

The source supplies simplicity of L in row (a), so component perfectness
gives its trivial center and two-core. The original model equivalence then
identifies the literal L/O₂(L) with the same G₂ field model. The uniform
long-root marked-pair theorem and the source marked-quotient adapter give
the contradiction. The full G₂(2^f) family here has f at least two; the
separate derived group G₂(2)' is not identified with a full G₂ carrier.

Source: Aschbacher--Smith 1.1.5(3)(a), Theorem C(3), Remark A.2.4 and
Proposition 2.2.2, printed pp.33, 501--503 and 519--520
(combined 1 March 2004 manuscript).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

/-- Exclude the ordinary simple G₂(2^f) row with its actual field model
and the original marked inner action. -/
theorem LocalControlWitness.false_of_inner_even_g2_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (hsimple : IsSimpleGroup L)
    (F : Type*) [Field F] [Finite F] {f : ℕ} (_hf : 2 ≤ f)
    (hF : Nat.card F = 2 ^ f) (e : L ≃* Atlas.G2.Model F)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (f := f) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let : IsQuasisimple L := hL.quasisimple
  let : IsSimpleGroup L := hsimple
  have hc : center L = ⊥ := center_eq_bot_of_simple_perfect
  have hp : pCore 2 L = ⊥ :=
    bot_unique ((IsQuasisimple.pCore_le_center 2).trans hc.le)
  let e' : (L ⧸ pCore 2 L) ≃* Atlas.G2.Model F :=
    ((QuotientGroup.quotientMulEquivOfEq hp).trans QuotientGroup.quotientBot).trans e
  apply w.false_of_marked_twoCore_component H S hUS hST hcore L hL hLM e' hinner
  intro R v hv ho hvc
  exact Atlas.G2.MarkedStrongClosure.sylow_noncommuting_conjugates v
    ⟨ho, R, hv, fun x hx => mem_centralizer_singleton_iff.mpr (hvc x hx).symm.eq⟩ R

/-- The ordinary G₂ alternative from the exact Theorem C list maps to the
literal marked-quotient obstruction without additional model hypotheses. -/
theorem LocalControlWitness.false_of_inner_even_g2_model
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (hsimple : IsSimpleGroup L) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassificationModels.IsG2At L (2 ^ f))
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  exact w.false_of_inner_even_g2_component H S hUS hST hcore L hL hLM hsimple F hf hF e hinner

end CFSG.Quasithin.Chapter2.BenderFusion
