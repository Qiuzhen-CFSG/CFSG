module
public import Theory.SpecificGroups.Triality.OuterOddSubgroups
public import Theory.SpecificGroups.Triality.StandardTwoRank.Derived
public import Theory.FieldTheory.OddQuadraticCoefficientLift
public import Theory.GroupTheory.AutomorphismExtensionBorel

/-!
# Faithful triality extensions and the binary-field endpoint

Inner–coefficient coverage realizes every automorphism on the genuine binary
carrier. Evaluation on the arm root group proves coefficient faithfulness.
The same carrier embeds faithfully into every actual automorphism overgroup,
and a self-centralizing normal copy acts faithfully by transported conjugation.

At q = 2 the full outer group has order dividing three. Thus every outer
two-group is trivial, and every self-centralizing normal triality subgroup
with two-group quotient equals its ambient group. This establishes absence
of a proper extension without a splitting or automorphism-coverage premise.

Source: GLS3 2.5.12(d,f), retaining Aut(GF(q³)); Aschbacher–Smith F.1.12,
printed pp.263–264. Simplicity and perfectness are supplied by the genuine
binary carrier's root proofs in `StandardTwoRank.Derived`.
-/

public section
noncomputable section
namespace Triality.Standard.ParabolicOuterTwo
open OuterOdd

/-- Characteristic-prime coefficient Frobenius on the original central quotient. -/
@[expose] def primeCoefficientAction (P : Parameters) : MulAut (Carrier P) :=
  coefficientAction P (frobeniusEquiv (ExtensionField P) P.prime)

/-- The coefficient action retains the cubic-field period, including its odd part. -/
theorem primeCoefficientAction_period (P : Parameters) :
    primeCoefficientAction P ^ (3 * P.exponent) = 1 := by
  have hc : Nat.card (CoefficientAut P) = 3 * P.exponent :=
    GaloisField.card_ringAut P.prime (3 * P.exponent) (by have := P.exponent_pos; omega)
  have hf : frobeniusEquiv (ExtensionField P) P.prime ^ (3 * P.exponent) = 1 := by
    simpa only [hc] using
      (pow_card_eq_one' (x := (frobeniusEquiv (ExtensionField P) P.prime : CoefficientAut P)))
  change coefficientAction P _ ^ _ = _
  rw [← map_pow, hf, map_one]

/-- Coverage by cubic coefficient automorphisms bounds the actual outer group. -/
theorem outer_card_dvd (n : ℕ) (hn : 0 < n) :
    Nat.card (MulAut.Outer (BinaryCarrier n hn)) ∣ 3 * n := by
  have hs := (outerCoefficientAction_surjective_iff (binaryParameters n hn)).mpr
    (Coverage.binary_inner_coefficient n hn)
  have hd := Subgroup.card_dvd_of_surjective
    (outerCoefficientAction (binaryParameters n hn)) hs
  have hc : Nat.card (CoefficientAut (binaryParameters n hn)) = 3 * n :=
    GaloisField.card_ringAut 2 (3 * n) (by omega)
  exact hc ▸ hd

/-- Every two-subgroup of the actual automorphism group at q = 2 is inner. -/
theorem twoSubgroup_le_inner_at_two
    (S : Subgroup (MulAut (BinaryCarrier 1 Nat.zero_lt_one))) (hS : IsPGroup 2 S) :
    S ≤ MulAut.innerSubgroup (BinaryCarrier 1 Nat.zero_lt_one) := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (BinaryCarrier 1 Nat.zero_lt_one))
  intro s hs
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  have hp : q s ^ (2 ^ k) = 1 := by
    rw [← map_pow]
    exact (congrArg q (congrArg Subtype.val hk)).trans (map_one q)
  have h3 : orderOf (q s) ∣ 3 :=
    (orderOf_dvd_natCard _).trans (by simpa using outer_card_dvd 1 Nat.zero_lt_one)
  have h1 : q s = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 2 3).pow_left k)
      (orderOf_dvd_of_pow_eq_one hp) h3)
  exact (QuotientGroup.eq_one_iff s).mp h1

/-- Thus adjoining any two-subgroup of automorphisms gives no extension at q = 2. -/
theorem inner_sup_twoSubgroup_at_two
    (S : Subgroup (MulAut (BinaryCarrier 1 Nat.zero_lt_one))) (hS : IsPGroup 2 S) :
    MulAut.innerSubgroup (BinaryCarrier 1 Nat.zero_lt_one) ⊔ S =
      MulAut.innerSubgroup (BinaryCarrier 1 Nat.zero_lt_one) :=
  sup_eq_left.mpr (twoSubgroup_le_inner_at_two S hS)

open Theory.GroupTheory.AutomorphismExtensionBorel

/-- Two-subgroups of the full outer group vanish at q = 2. -/
theorem outerTwoSubgroup_eq_bot_at_two
    (D : Subgroup (MulAut.Outer (BinaryCarrier 1 Nat.zero_lt_one))) (hD : IsPGroup 2 D) :
    D = ⊥ := by
  apply bot_unique
  intro d hd
  obtain ⟨k, hk⟩ := hD ⟨d, hd⟩
  have hp : d ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h3 : orderOf d ∣ 3 :=
    (orderOf_dvd_natCard _).trans (by simpa using outer_card_dvd 1 Nat.zero_lt_one)
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 2 3).pow_left k)
      (orderOf_dvd_of_pow_eq_one hp) h3)

/-- An actual preimage extension by an outer two-group is the inner group at q = 2.
This uses exhaustiveness of coefficient coverage, not merely an order-three action. -/
theorem outerTwoPreimage_eq_inner_at_two
    (D : Subgroup (MulAut.Outer (BinaryCarrier 1 Nat.zero_lt_one))) (hD : IsPGroup 2 D) :
    outerPreimage D = MulAut.innerSubgroup (BinaryCarrier 1 Nat.zero_lt_one) := by
  rw [outerTwoSubgroup_eq_bot_at_two D hD, outerPreimage]
  exact QuotientGroup.ker_mk' _

/-- Recognition applies to every overgroup of the actual inner embedding with two-group
outer image, with no assumption that the extension splits. -/
theorem automorphismOvergroup_eq_inner_at_two
    (E : Subgroup (MulAut (BinaryCarrier 1 Nat.zero_lt_one)))
    (hE : MulAut.innerSubgroup (BinaryCarrier 1 Nat.zero_lt_one) ≤ E)
    (h2 : IsPGroup 2 (E.map (QuotientGroup.mk'
      (MulAut.innerSubgroup (BinaryCarrier 1 Nat.zero_lt_one))))) :
    E = MulAut.innerSubgroup (BinaryCarrier 1 Nat.zero_lt_one) := by
  rw [← outerPreimage_map_eq E hE]
  exact outerTwoPreimage_eq_inner_at_two _ h2

/-- The carrier embeds faithfully in every literal automorphism extension. -/
theorem carrierEmbedding_injective (n : ℕ) (hn : 0 < n)
    (E : Subgroup (MulAut (BinaryCarrier n hn)))
    (hE : MulAut.innerSubgroup (BinaryCarrier n hn) ≤ E) :
    Function.Injective (innerEmbedding E hE) := by
  apply innerEmbedding_injective E hE
  apply (MulAut.conj : BinaryCarrier n hn →* MulAut (BinaryCarrier n hn)).ker_eq_bot_iff.mp
  apply bot_unique
  intro x hx
  have hc : x ∈ Subgroup.center (BinaryCarrier n hn) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy := MulEquiv.congr_fun (show MulAut.conj x = 1 from hx) y
    change x * y * x⁻¹ = y at hy
    exact (mul_inv_eq_iff_eq_mul.mp hy).symm
  simpa only [binaryCarrier_center_eq_bot, Subgroup.mem_bot] using hc


/-- The cubic coefficient action is faithful on the genuine binary carrier. -/
theorem coefficientAction_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (coefficientAction P) := by
  intro e f hef
  apply RingEquiv.ext
  intro t
  apply Coverage.ParameterRigidity.rootElement_injective P hp true .arms
  have h := MulEquiv.congr_fun hef (ConcreteBruhat.rootElement P hp true .arms t)
  simpa only [Coverage.coefficientAction_rootElement, Coverage.coefficientRootField] using h

/-- Transport the actual conjugation action of a normal triality subgroup. -/
@[expose] def normalExtensionAction {E : Type*} [Group E] (L : Subgroup E) [L.Normal]
    (n : ℕ) (hn : 0 < n) (e : L ≃* BinaryCarrier n hn) : E →* MulAut (BinaryCarrier n hn) :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

theorem normalExtensionAction_injective {E : Type*} [Group E] (L : Subgroup E) [L.Normal]
    (n : ℕ) (hn : 0 < n) (e : L ≃* BinaryCarrier n hn)
    (hC : Subgroup.centralizer (L : Set E) = ⊥) :
    Function.Injective (normalExtensionAction L n hn e) :=
  (MulAut.congr e).injective.comp (MulAut.conjNormal_injective_of_centralizer_eq_bot L hC)

/-- Every element of a faithful extension has an actual inner–coefficient action. -/
theorem normalExtensionAction_inner_coefficient {E : Type*} [Group E]
    (L : Subgroup E) [L.Normal] (n : ℕ) (hn : 0 < n)
    (e : L ≃* BinaryCarrier n hn) (x : E) :
    ∃ g : BinaryCarrier n hn, ∃ c : CoefficientAut (binaryParameters n hn),
      normalExtensionAction L n hn e x = MulAut.conj g * coefficientAction _ c :=
  Coverage.binary_inner_coefficient n hn _

/-- Every self-centralizing normal copy of ³D₄(2) with two-group quotient is the whole
ambient extension. No splitting or exhaustiveness premise is required. -/
theorem normalExtension_eq_top_at_two {E : Type*} [Group E]
    (L : Subgroup E) [L.Normal] (e : L ≃* BinaryCarrier 1 Nat.zero_lt_one)
    (hC : Subgroup.centralizer (L : Set E) = ⊥) (h2 : IsPGroup 2 (E ⧸ L)) : L = ⊤ := by
  let f : E ⧸ L →* MulAut.Outer (BinaryCarrier 1 Nat.zero_lt_one) :=
    (MulAut.outerCongr e).toMonoidHom.comp (MulAut.outerAction L)
  have hf : Function.Injective f :=
    (MulAut.outerCongr e).injective.comp (MulAut.outerAction_injective L hC)
  have hr : f.range = ⊥ := outerTwoSubgroup_eq_bot_at_two f.range
    (h2.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  have htriv : Subsingleton (E ⧸ L) := by
    apply subsingleton_of_forall_eq 1
    intro x
    apply hf
    have hx : f x ∈ (⊥ : Subgroup (MulAut.Outer (BinaryCarrier 1 Nat.zero_lt_one))) :=
      hr ▸ (show f x ∈ f.range from ⟨x, rfl⟩)
    exact hx.trans (map_one f).symm
  exact QuotientGroup.subgroup_eq_top_of_subsingleton L htriv

end Triality.Standard.ParabolicOuterTwo
