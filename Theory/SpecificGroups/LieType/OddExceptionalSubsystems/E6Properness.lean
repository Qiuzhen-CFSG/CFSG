module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.E6Twisting

/-!
# Properness of the projected folded E6 subgroups

The pinned diagram fixes the folded subgroup. If its image filled the central
quotient, every diagram difference `σ(g) * g⁻¹` would commute with each fixed
folded element. This implication only uses the center of the group actually
being quotiented; it does not identify that center with an ambient matrix center.

On the integral Geck lattice, the positive pair `x₀(a) x₅(b)` can commute with
`x₋₀(1) x₋₅(1)` only if `a = 0`. Apply both products to the neighboring Cartan
vector and compare the root-zero coordinate: the equality forces `a² = 0`.
The split witness is `x₀(1)`. For the twisted group choose `t` moved by the
q-Frobenius and use `x₀(t) x₅(t^q)`. This additive root curve is fixed by the
actual graph–field involution and killed by p, so it belongs to the literal
O^{p′} subgroup. Its diagram difference has first parameter `t^q - t ≠ 0`.

The result uses no F4 identification, order formula, or simplicity assertion.
It holds over every field in the split case and for every prime in the twisted
case. In particular it proves both properness premises needed for the
odd-characteristic folded inclusions, including the parameter m = 0.

Sources: Aschbacher–Smith A.2.17, printed p.39 of `refs/quasithin.pdf`;
GLS3 §§2.2–2.4, especially the type-II root groups in Table 2.4
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup Matrix
namespace TwistedE6.FoldedSubsystem
noncomputable section
attribute [local instance] Classical.decEq
variable {F : Type*} [Field F]
local instance : InvolutiveNeg typeE6Roots := Pairing.indexNeg
private abbrev cv (i : Fin 6) : Index → F := Pi.single (.inl (simpleIndex i)) 1
private abbrev rv (i : typeE6Roots) : Index → F := Pi.single (.inr i) 1
private lemma pos_cartan (i j : Fin 6) (t : F) :
    (simpleRoot F true i t).val.val *ᵥ cv j =
      cv j + (t * (|typeE6CartanMatrix i j| : ℤ)) • rv (simpleIndex i) := by
  rw [simpleRoot_val]
  change positiveMatrix (simpleIndex i) t *ᵥ _ = _
  ext (a | a) <;>
    simp [positiveMatrix_formula, eDividedPower, eMatrix, Matrix.one_apply,
      Pi.single_apply, smul_eq_mul, typeE6RootPairing_base_cartan_apply, cv, rv]
private lemma neg_cartan (i j : Fin 6) (t : F) :
    (simpleRoot F false i t).val.val *ᵥ cv j =
      cv j + (t * (|typeE6CartanMatrix i j| : ℤ)) • rv (-(simpleIndex i) : typeE6Roots) := by
  rw [simpleRoot_val]
  change negativeMatrix (simpleIndex i) t *ᵥ _ = _
  rw [negativeMatrix_formula, fDividedPower_one]
  ext (a | a) <;>
    simp [fMatrix, fDividedPower, Matrix.mul_apply, omegaMatrix,
      eDividedPower, Matrix.one_apply, Pi.single_apply, smul_eq_mul,
      typeE6RootPairing_base_cartan_apply, cv, rv]
private lemma pos_cross (i : Fin 6) (t : F) :
    (simpleRoot F true i t).val.val (.inr (simpleIndex i))
      (.inr (-(simpleIndex i) : typeE6Roots)) = t ^ 2 := by
  have hz : Pairing.chainTopCoeff (simpleIndex i) (simpleIndex i) = 0 :=
    Pairing.chainTopCoeff_of_not_linearIndependent (by
      simp_rw [LinearIndependent.pair_iff, not_forall]
      exact ⟨1, -1, by simp, by simp⟩)
  have hr : Pairing.root (-(simpleIndex i) : typeE6Roots) =
      -Pairing.root (simpleIndex i) := by
    simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self]
  have h2 : Pairing.root (simpleIndex i) =
      Pairing.root (-(simpleIndex i) : typeE6Roots) + 2 • Pairing.root (simpleIndex i) := by
    rw [hr]; module
  have h3 : Pairing.root (simpleIndex i) ≠
      Pairing.root (-(simpleIndex i) : typeE6Roots) + 3 • Pairing.root (simpleIndex i) := by
    rw [hr]
    intro h
    apply Pairing.ne_zero (simpleIndex i)
    have h' : Pairing.root (simpleIndex i) =
        Pairing.root (simpleIndex i) + Pairing.root (simpleIndex i) := h.trans (by module)
    exact add_left_cancel (h'.symm.trans (add_zero _).symm)
  rw [simpleRoot_val]
  change positiveMatrix (simpleIndex i) t _ _ = _
  simp only [positiveMatrix_formula, Matrix.add_apply, Matrix.smul_apply,
    Matrix.map_apply, Int.coe_castRingHom, smul_eq_mul]
  have hb : Pairing.chainBotCoeff (simpleIndex i) (-(simpleIndex i) : typeE6Roots) = 0 := by
    change Pairing.chainBotCoeff _ (Pairing.reflectionPerm _ _) = 0
    rw [RootPairing.chainBotCoeff_reflectionPerm_right, hz]
  have h0 : Pairing.root (simpleIndex i) ≠
      Pairing.root (simpleIndex i) + Pairing.root (-(simpleIndex i) : typeE6Roots) := by
    rw [hr, add_neg_cancel]
    exact Pairing.ne_zero _
  simp only [eDividedPower, eMatrix, Matrix.fromBlocks_apply₂₂, Matrix.of_apply,
    Matrix.one_apply, Sum.inr.injEq, if_neg (Pairing.ne_neg (simpleIndex i)),
    if_neg h0, if_pos h2, if_neg h3, hb, zero_add, Nat.choose_self,
    Int.cast_zero, mul_zero, add_zero]
  simp only [Nat.cast_one, Int.cast_one, mul_one]

private lemma neg_diag (i : Fin 6) (t : F) :
    (simpleRoot F false i t).val.val (.inr (simpleIndex i)) (.inr (simpleIndex i)) = 1 := by
  have heq (x : typeE6Roots) : (simpleIndex i : typeE6Roots) = -x ↔
      x = -(simpleIndex i) := by
    constructor <;> intro h <;> simpa only [neg_neg] using congrArg Neg.neg h.symm
  rw [simpleRoot_val]
  change negativeMatrix (simpleIndex i) t _ _ = _
  simp [negativeMatrix_formula, fDividedPower, Matrix.mul_apply, omegaMatrix,
    eDividedPower, eMatrix, Pairing.ne_zero, heq,
    -RootPairing.indexNeg_neg, -typeE6RootPairing_root, -typeE6RootPairing_baseEquiv_val]

private lemma fixes_of_commute (A B : Ambient F) (c v : Index → F)
    (hc : Commute A B) (ha : A.val *ᵥ c = c) (hb : B.val *ᵥ c = c + v) :
    A.val *ᵥ v = v := by
  have he := congrArg (fun X : Ambient F => X.val *ᵥ c) hc.eq
  change (A.val * B.val) *ᵥ c = (B.val * A.val) *ᵥ c at he
  rw [← mulVec_mulVec, ← mulVec_mulVec, hb, ha, mulVec_add, ha, hb] at he
  exact add_left_cancel he

private lemma five_fixes_cartan (s : Bool) (t : F) :
    (simpleRoot F s 5 t).val.val *ᵥ cv 1 = cv 1 := by
  cases s
  · simpa [typeE6CartanMatrix] using neg_cartan 5 1 t
  · simpa [typeE6CartanMatrix] using pos_cartan 5 1 t

private lemma five_fixes_zero_root (s d : Bool) (t : F) :
    (simpleRoot F s 5 t).val.val *ᵥ
      rv (if d then (simpleIndex 0 : typeE6Roots) else -(simpleIndex 0) : typeE6Roots) =
    rv (if d then (simpleIndex 0 : typeE6Roots) else -(simpleIndex 0) : typeE6Roots) := by
  apply fixes_of_commute (simpleRoot F s 5 t).val (simpleRoot F d 0 1).val (cv 1)
  · have hc : Commute (simpleRoot F s 5 t) (simpleRoot F d 0 1) := by
      cases s <;> cases d
      · exact simpleRoot_commute F false 5 0 (by decide) (by decide) _ _
      · exact (simpleRoot_opposite_commute F 0 5 (by decide) _ _).symm
      · exact simpleRoot_opposite_commute F 5 0 (by decide) _ _
      · exact simpleRoot_commute F true 5 0 (by decide) (by decide) _ _
    exact hc.map (splitCarrier F).subtype
  · exact five_fixes_cartan s t
  · cases d
    · simpa [typeE6CartanMatrix] using neg_cartan (F := F) 0 1 1
    · simpa [typeE6CartanMatrix] using pos_cartan (F := F) 0 1 1

private def positivePair (a b : F) : splitCarrier F :=
  simpleRoot F true 0 a * simpleRoot F true 5 b

/-- The rank-one matrix obstruction inside the two orthogonal end nodes. -/
private lemma pair_commute_obstruction (a b : F)
    (hc : Commute (positivePair a b) (foldedSimple F false 0 1)) : a = 0 := by
  have hx : (positivePair a b).val.val *ᵥ cv 1 =
      cv 1 + a • rv (simpleIndex 0) := by
    change ((simpleRoot F true 0 a).val.val * (simpleRoot F true 5 b).val.val) *ᵥ _ = _
    rw [← mulVec_mulVec, five_fixes_cartan]
    simpa [typeE6CartanMatrix] using pos_cartan 0 1 a
  have hy : (foldedSimple F false 0 1).val.val *ᵥ cv 1 =
      cv 1 + rv (-(simpleIndex 0) : typeE6Roots) := by
    change ((simpleRoot F false 0 1).val.val * (simpleRoot F false 5 1).val.val) *ᵥ _ = _
    rw [← mulVec_mulVec, five_fixes_cartan]
    simpa [typeE6CartanMatrix] using neg_cartan (F := F) 0 1 1
  have hxv : (positivePair a b).val.val *ᵥ rv (-(simpleIndex 0) : typeE6Roots) =
      (simpleRoot F true 0 a).val.val *ᵥ rv (-(simpleIndex 0) : typeE6Roots) := by
    change ((simpleRoot F true 0 a).val.val * (simpleRoot F true 5 b).val.val) *ᵥ _ = _
    rw [← mulVec_mulVec]
    exact congrArg (fun v => (simpleRoot F true 0 a).val.val *ᵥ v)
      (five_fixes_zero_root true false b)
  have hyv : (foldedSimple F false 0 1).val.val *ᵥ rv (simpleIndex 0) =
      (simpleRoot F false 0 1).val.val *ᵥ rv (simpleIndex 0) := by
    change ((simpleRoot F false 0 1).val.val * (simpleRoot F false 5 1).val.val) *ᵥ _ = _
    rw [← mulVec_mulVec]
    exact congrArg (fun v => (simpleRoot F false 0 1).val.val *ᵥ v)
      (five_fixes_zero_root (F := F) false true 1)
  have he := congrArg (fun g : splitCarrier F => g.val.val *ᵥ cv 1) hc.eq
  change ((positivePair a b).val.val * (foldedSimple F false 0 1).val.val) *ᵥ cv 1 =
    ((foldedSimple F false 0 1).val.val * (positivePair a b).val.val) *ᵥ cv 1 at he
  rw [← mulVec_mulVec, ← mulVec_mulVec, hx, hy, mulVec_add, mulVec_add,
    mulVec_smul, hx, hy, hxv, hyv] at he
  have hh := congrFun he (.inr (simpleIndex 0))
  have hn : (simpleIndex 0 : typeE6Roots) ≠ -(simpleIndex 0) := Pairing.ne_neg _
  have hsq : a ^ 2 = 0 := by
    have hh' : a + a ^ 2 = a := by
      simp only [cv, rv, Matrix.mulVec_single_one, Matrix.col_apply,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, pos_cross, neg_diag] at hh
      simpa only [Pi.single_apply, Sum.inr.injEq, Sum.inr_ne_inl, if_false,
        if_pos rfl, ite_true, if_neg hn, zero_add, mul_one] using hh
    exact add_left_cancel (hh'.trans (add_zero a).symm)
  exact sq_eq_zero_iff.mp hsq

end
end TwistedE6.FoldedSubsystem

namespace TwistedE6.FoldedSubsystem
noncomputable section
attribute [local instance] Classical.decEq

/-- Equality in the actual central quotient forces the diagram difference to
centralize any diagram-fixed element of the original group. -/
private lemma central_quotient_obstruction {G A : Type*} [Group G] [Group A]
    (inc : G →* A) (σ : A ≃* A) (g h y : G)
    (hh : σ (inc h) = inc h) (hy : σ (inc y) = inc y)
    (he : QuotientGroup.mk' (Subgroup.center G) g =
      QuotientGroup.mk' (Subgroup.center G) h) :
    Commute (σ (inc g) * (inc g)⁻¹) (inc y) := by
  have hz : g * h⁻¹ ∈ Subgroup.center G := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (Subgroup.center G)) (g * h⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have hc : Commute (inc (g * h⁻¹)) (inc y) :=
    (show Commute (g * h⁻¹) y from
      (Subgroup.mem_center_iff.mp hz y).symm).map inc
  have hs := hc.map σ.toMonoidHom
  change Commute (σ (inc (g * h⁻¹))) (σ (inc y)) at hs
  rw [hy] at hs
  have h := hs.mul_left hc.inv_left
  simpa only [map_mul, map_inv, hh, _root_.mul_inv_rev, inv_inv, mul_assoc,
    inv_mul_cancel_left] using h

variable (p : ℕ) [Fact p.Prime] (m : ℕ)

private lemma simpleRoot_twist_all (s : Bool) (i : Fin 6) (t : CoefficientField p m) :
    graphFieldTwist p m (simpleRoot _ s i t) =
      simpleRoot _ s (typeE6DiagramPermutation i) (fieldTwist p m t) := by
  let := Pairing.indexNeg
  cases s
  · change graphFieldTwist p m (rootElement _ (-(simpleIndex i) : typeE6Roots) t) =
      rootElement _ (-(simpleIndex (typeE6DiagramPermutation i)) : typeE6Roots) _
    rw [graphFieldTwist_negative, fieldTwist_apply]
    congr 2
    exact congrArg Subtype.val (typeE6DiagramBasePermutation_numbered i)
  · change graphFieldTwist p m (rootElement _ (simpleIndex i) t) =
      rootElement _ (simpleIndex (typeE6DiagramPermutation i)) _
    rw [graphFieldTwist_positive, fieldTwist_apply]
    congr 1
    exact congrArg Subtype.val (typeE6DiagramBasePermutation_numbered i)

private def pairedSplit (t : CoefficientField p m) : rootGeneratedSubgroup p m :=
  simpleRoot _ true 0 t * simpleRoot _ true 5 (fieldTwist p m t)

private lemma pairedSplit_add (t u : CoefficientField p m) :
    pairedSplit p m (t + u) = pairedSplit p m t * pairedSplit p m u := by
  simp only [pairedSplit, map_add, simpleRoot_add]
  exact (simpleRoot_commute _ true 0 5 (by decide) (by decide)
    u (fieldTwist p m t)).mul_mul_mul_comm _ _

@[simp] private lemma pairedSplit_zero : pairedSplit p m 0 = 1 := by
  simp only [pairedSplit, map_zero, simpleRoot_zero, mul_one]

private lemma pairedSplit_fixed (t : CoefficientField p m) :
    graphFieldTwist p m (pairedSplit p m t) = pairedSplit p m t := by
  simp only [pairedSplit, map_mul, simpleRoot_twist_all, fieldTwist_twice]
  exact (simpleRoot_commute _ true 5 0 (by decide) (by decide)
    (fieldTwist p m t) t).eq

private def pairedFixed (t : CoefficientField p m) : rationalFixedSubgroup p m :=
  ⟨(pairedSplit p m t).val,
    (mem_rationalFixedSubgroup_iff p m _).mpr (pairedSplit_fixed p m t)⟩

private lemma pairedFixed_add (t u : CoefficientField p m) :
    pairedFixed p m (t + u) = pairedFixed p m t * pairedFixed p m u :=
  Subtype.ext (congrArg (fun g : rootGeneratedSubgroup p m => g.val) (pairedSplit_add p m t u))

@[simp] private lemma pairedFixed_zero : pairedFixed p m 0 = 1 :=
  Subtype.ext (congrArg (fun g : rootGeneratedSubgroup p m => g.val) (pairedSplit_zero p m))

private lemma pairedFixed_nsmul (t : CoefficientField p m) (n : ℕ) :
    pairedFixed p m (n • t) = pairedFixed p m t ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, pairedFixed_add, ih, pow_succ]

private lemma pairedFixed_pow (t : CoefficientField p m) : pairedFixed p m t ^ p = 1 := by
  rw [← pairedFixed_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, pairedFixed_zero]

/-- The conjugate-parameter pair lies in the actual defining-prime residual. -/
private def pairedRoot (t : CoefficientField p m) : definingCharacteristicSubgroup p m :=
  ⟨pairedFixed p m t,
    Subgroup.mem_primePowerGenerated_of_pow (n := 1) (by
      simpa only [pow_one] using pairedFixed_pow p m t)⟩

@[simp] private lemma pairedRoot_ambient (t : CoefficientField p m) :
    ambientInclusion p m (pairedRoot p m t) = (pairedSplit p m t).val := rfl

end
end TwistedE6.FoldedSubsystem


namespace TwistedE6.FoldedSubsystem
noncomputable section
attribute [local instance] Classical.decEq
variable {F : Type*} [Field F]

private lemma positivePair_add (a b c d : F) :
    positivePair (a + c) (b + d) = positivePair a b * positivePair c d := by
  simp only [positivePair, simpleRoot_add]
  exact (simpleRoot_commute F true 0 5 (by decide) (by decide) c b).mul_mul_mul_comm _ _

@[simp] private lemma positivePair_zero : positivePair (0 : F) 0 = 1 := by
  simp [positivePair]

private lemma positivePair_inv (a b : F) :
    (positivePair a b)⁻¹ = positivePair (-a) (-b) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← positivePair_add]
  simp

private lemma positivePair_diagram (a b : F) :
    pinnedDiagram F (positivePair a b) = positivePair b a := by
  simp only [positivePair, map_mul, simpleRoot_diagram]
  exact (simpleRoot_commute F true 5 0 (by decide) (by decide) a b).eq

private lemma diagram_difference (a b : F) :
    typeE6PinnedUnitsEquiv F (positivePair a b).val * (positivePair a b).val⁻¹ =
      (positivePair (b - a) (a - b)).val := by
  have h : pinnedDiagram F (positivePair a b) * (positivePair a b)⁻¹ =
      positivePair (b - a) (a - b) := by
    rw [positivePair_diagram, positivePair_inv, ← positivePair_add]
    simp only [sub_eq_add_neg]
  exact congrArg (fun g : splitCarrier F => g.val) h

/-- The literal folded image remains proper after the split E6 central quotient. -/
theorem splitModelMap_range_ne_top (F : Type*) [Field F] :
    (splitModelMap F).range ≠ ⊤ := by
  intro htop
  obtain ⟨h, hh⟩ := MonoidHom.range_eq_top.mp htop
    (ExceptionalSplit.projection Pairing Base F (positivePair (1 : F) 0))
  have hc := central_quotient_obstruction (splitCarrier F).subtype
    (typeE6PinnedUnitsEquiv F) (positivePair (1 : F) 0) h.val
    (foldedSimple F false 0 1)
    (congrArg (fun g : splitCarrier F => g.val) (splitSubgroup_fixed F h.property))
    (congrArg (fun g : splitCarrier F => g.val) (foldedSimple_fixed F false 0 1))
    hh.symm
  change Commute (typeE6PinnedUnitsEquiv F (positivePair (1 : F) 0).val *
    (positivePair (1 : F) 0).val⁻¹) (foldedSimple F false 0 1).val at hc
  rw [diagram_difference] at hc
  have he := pair_commute_obstruction (0 - 1 : F) (1 - 0)
    (show Commute (positivePair (0 - 1 : F) (1 - 0)) (foldedSimple F false 0 1) from
      Subtype.ext hc.eq)
  simp at he

private lemma splitFieldMap_diagram_fixed {K : Type*} [Field K] (f : F →+* K)
    {g : splitCarrier F} (hg : g ∈ splitSubgroup F) :
    pinnedDiagram K (splitFieldMap f g) = splitFieldMap f g := by
  have h : splitSubgroup F ≤
      ((pinnedDiagram K).toMonoidHom.comp (splitFieldMap f)).eqLocus (splitFieldMap f) := by
    rw [splitSubgroup, Subgroup.closure_le]
    rintro _ ⟨⟨s, i, t⟩, rfl⟩
    change pinnedDiagram K (splitFieldMap f (foldedSimple F s i t)) = _
    rw [splitFieldMap_foldedSimple]
    exact foldedSimple_fixed K s i (f t)
  exact h hg

variable (p : ℕ) [Fact p.Prime] (m : ℕ)

private lemma exists_moved_coefficient : ∃ t : CoefficientField p m, fieldTwist p m t ≠ t := by
  by_contra! h
  have hs : Function.Surjective (fixedField p m).subtype := by
    intro x
    exact ⟨⟨x, h x⟩, rfl⟩
  have hc := Nat.card_eq_of_bijective (fixedField p m).subtype
    ⟨(fixedField p m).subtype.injective, hs⟩
  rw [fixedField_card, field_card] at hc
  have hq := parameter_ge_two p m
  nlinarith

/-- The actual folded coefficient image is proper in the center quotient of O^{p'}.
The positive exponent m+1 includes m=0. -/
theorem modelMap_range_ne_top : (modelMap p m).range ≠ ⊤ := by
  intro htop
  obtain ⟨t, ht⟩ := exists_moved_coefficient p m
  obtain ⟨h, hh⟩ := MonoidHom.range_eq_top.mp htop (toModel p m (pairedRoot p m t))
  have hhfixed : typeE6PinnedUnitsEquiv (CoefficientField p m)
      (ambientInclusion p m (coverEmbedding p m h)) =
      ambientInclusion p m (coverEmbedding p m h) := by
    exact congrArg (fun g : splitCarrier (CoefficientField p m) => g.val)
      (splitFieldMap_diagram_fixed (coefficientEmbedding p m) h.property)
  have hyfixed : typeE6PinnedUnitsEquiv (CoefficientField p m)
      (ambientInclusion p m (foldedRoot p m false 0 1)) =
      ambientInclusion p m (foldedRoot p m false 0 1) := by
    exact congrArg (fun g : splitCarrier (CoefficientField p m) => g.val)
      (foldedSimple_fixed (CoefficientField p m) false 0 1)
  have hc := central_quotient_obstruction (ambientInclusion p m)
    (typeE6PinnedUnitsEquiv (CoefficientField p m)) (pairedRoot p m t)
    (coverEmbedding p m h) (foldedRoot p m false 0 1) hhfixed hyfixed hh.symm
  change Commute (typeE6PinnedUnitsEquiv (CoefficientField p m)
      (positivePair t (fieldTwist p m t)).val * (positivePair t (fieldTwist p m t)).val⁻¹)
      (foldedSimple (CoefficientField p m) false 0 1).val at hc
  rw [diagram_difference] at hc
  exact ht (sub_eq_zero.mp (pair_commute_obstruction _ _ (Subtype.ext hc.eq)))
end
end TwistedE6.FoldedSubsystem
