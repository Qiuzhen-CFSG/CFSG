module

public import Theory.SpecificGroups.BinaryLinear.MarkedStrongClosure
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.MarkedQuotient
public import CFSG.Quasithin.ClassificationModels.Families

/-!
# Excluding the binary linear models in the Bender inspection

Source simplicity and component perfectness make O₂(L) trivial. The literal
binary projective quotient is transported to its actual natural linear
action. The source marker becomes a Sylow-central transvection, and two
noncommuting returning conjugates contradict abelian strong closure through
the marked-quotient adapter. Arbitrary fields of order two are transported
by an actual field isomorphism before applying the binary calculation.

Source: Aschbacher--Smith 1.1.5(3)(a), Theorem C(4), and Proposition 2.2.2,
printed pp.33, 501--503 and 519--520 (combined 1 March 2004 manuscript).
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

/-- The actual simple binary PSL₄ and PSL₅ components in row (a) are
incompatible with the original Bender witness. -/
theorem LocalControlWitness.false_of_inner_binary_psl_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (hsimple : IsSimpleGroup L) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : L ≃* PSL(n, ZMod 2))
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  let : IsQuasisimple L := hL.quasisimple
  let : IsSimpleGroup L := hsimple
  have hc : center L = ⊥ := center_eq_bot_of_simple_perfect
  have hp : pCore 2 L = ⊥ :=
    bot_unique ((IsQuasisimple.pCore_le_center 2).trans hc.le)
  let e' : (L ⧸ pCore 2 L) ≃* BinaryLinear.OuterCyclic.LinearGroup n :=
    (((QuotientGroup.quotientMulEquivOfEq hp).trans QuotientGroup.quotientBot).trans e).trans
      (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega))
  let : Finite (BinaryLinear.OuterCyclic.LinearGroup n) :=
    Finite.of_injective
      (fun g : BinaryLinear.OuterCyclic.LinearGroup n =>
        (g : BinaryLinear.OuterCyclic.Space n → BinaryLinear.OuterCyclic.Space n))
      DFunLike.coe_injective
  apply w.false_of_marked_twoCore_component H S hUS hST hcore L hL hLM e' hinner
  intro R v hv ho hvc
  exact BinaryLinear.MarkedStrongClosure.sylow_noncommuting_conjugates hn v
    ⟨ho, R, hv, fun x hx => mem_centralizer_singleton_iff.mpr (hvc x hx).symm.eq⟩ R

/-- The original Theorem C(4) model predicate retains its specified field
and quotient map until transport to the binary linear action. -/
theorem LocalControlWitness.false_of_inner_binary_psl_model
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (hsimple : IsSimpleGroup L) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL L n 2)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  exact w.false_of_inner_binary_psl_component H S hUS hST hcore L hL hLM hsimple hn
    (e.trans (Atlas.fieldEquivPSL n eF)) hinner

end CFSG.Quasithin.Chapter2.BenderFusion
