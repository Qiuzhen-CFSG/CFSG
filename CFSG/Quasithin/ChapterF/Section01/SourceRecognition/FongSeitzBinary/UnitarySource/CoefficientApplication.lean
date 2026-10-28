module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.CoreCoefficients
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.QuadraticCoefficients
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.CoreModules

/-!
# Constructed unitary coefficient fields on the original quotient

The literal original local-characteristic-two hypotheses discharge
faithfulness in the coefficient-field construction. At the source core
orders, it gives dimension two over a quadratic field and dimension four
over its fixed-field size. The quadratic involution and fixed field are
constructed inside the same commuting ring. All conjugation equations
retain Q.q on generated L S and the actual relative Frattini quotient.
With the exact Cartan-kernel order, every nonzero scalar has an original
representative inducing that scalar on every vector of this same core.

These theorems discharge the scalar-field and dimension step of II (8B).
Remainder containment and the actual irreducible core action are still
explicit earlier-source premises. The irreducible-action source family
belongs to qt-dgs85-quadrangle-structure. Remainder containment, the original
Cartan orders, natural/tensor realizations, comparison of the two actions,
U5 equations and labelled torus/Weyl laws remain with
qt-dgs85-unitary-source-recognition. No model marking or field identification
is assumed in place of those remaining proofs.

Source: Fong--Seitz I (6A), pp.37--38; II (8B)--(8C), pp.201--203;
AS F.1.1 and DGS Theorem D, p.224.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (Q : SourceQuotient L S) (split : SplitData Q.tits) (i : Fin 2)
variable (hV : simpleRemainder Q split i ≤ HexagonStructure.localKernel Q i)
variable [Representation.IsIrreducible (coreActorRepresentation Q split i hV)]

theorem original_core_coefficient_dimension (h : HypothesisF11 L S)
    (n d : ℕ) (hn : 0 < n) (hd : 2^n-1 ∣ Nat.card (coreCartan Q i))
    (hcard : Nat.card (CoreSpace Q split i) = (2^n)^d) :
    Nat.card (CoreCoefficientField Q split i hV n) = 2^n ∧
    Module.finrank (CoreCoefficientField Q split i hV n)
      (coreActorRepresentation Q split i hV).asModule = d ∧
    (coreCoefficientRepresentation Q split i hV n).IsIrreducible := by
  have hc := MarkedLocal.parabolic_core_selfCentralizing Q (originalMarkedIso Q) h i
  exact ⟨coreCoefficientField_card Q split i hV n hn hc hd,
    coreCoefficient_finrank Q split i hV n d hn hc hd hcard,
    coreCoefficientRepresentation_irreducible Q split i hV n⟩

theorem original_unitary_natural_field (h : HypothesisF11 L S)
    (n : ℕ) (hn : 0 < n) (hd : (2^n)^2-1 ∣ Nat.card (coreCartan Q i))
    (hcard : Nat.card (CoreSpace Q split i) = (2^n)^4) :
    Nat.card (CoreCoefficientField Q split i hV (2*n)) = (2^n)^2 ∧
    Module.finrank (CoreCoefficientField Q split i hV (2*n))
      (coreActorRepresentation Q split i hV).asModule = 2 ∧
    Function.Involutive (ScalarSubfield.conjugation (CoreEnd Q split i hV) n) ∧
    Nat.card (FixedBy.subfield (CoreCoefficientField Q split i hV (2*n))
      (ScalarSubfield.conjugation (CoreEnd Q split i hV) n)) = 2^n ∧
    ScalarSubfield.conjugation (CoreEnd Q split i hV) n ≠ RingEquiv.refl _ := by
  have hd' : 2^(2*n)-1 ∣ Nat.card (coreCartan Q i) := by
    simpa only [pow_mul, Nat.mul_comm 2 n] using hd
  have hc := MarkedLocal.parabolic_core_selfCentralizing Q (originalMarkedIso Q) h i
  have hEnd := hd'.trans (coreCartan_card_dvd_field_sub_one Q split i hV hc)
  -- Reuse the exact field instances at the concrete original quotient.
  let K := CoreEnd Q split i hV
  let : Field K := inferInstanceAs (Field (CoreEnd Q split i hV))
  let : CharP K 2 := coreEnd_charTwo Q split i hV
  let : Finite K := inferInstanceAs (Finite (CoreEnd Q split i hV))
  have hdata := ScalarSubfield.quadratic_cards K n hn hEnd
  refine ⟨hdata.1,?_,ScalarSubfield.conjugation_involutive K n,hdata.2,
    ScalarSubfield.conjugation_ne_one K n hn hEnd⟩
  apply coreCoefficient_finrank Q split i hV (2*n) 2 (by omega) hc hd'
  rw [hcard]
  simp only [← pow_mul]
  congr 1
  omega

theorem original_unitary_tensor_field (h : HypothesisF11 L S)
    (n : ℕ) (hn : 0 < n) (hd : 2^n-1 ∣ Nat.card (coreCartan Q i))
    (hcard : Nat.card (CoreSpace Q split i) = (2^n)^4) :
    Nat.card (CoreCoefficientField Q split i hV n) = 2^n ∧
    Module.finrank (CoreCoefficientField Q split i hV n)
      (coreActorRepresentation Q split i hV).asModule = 4 ∧
    (coreCoefficientRepresentation Q split i hV n).IsIrreducible :=
  original_core_coefficient_dimension Q split i hV h n 4 hn hd hcard

theorem original_coefficient_actor_quotient (n : ℕ)
    (a v : generated L S) (ha : Q.q a ∈ coreActor Q split i)
    (hv : Q.q v ∈ simpleRemainder Q split i) :
    ∃ w : simpleRemainder Q split i,
      (w : (generated L S) ⧸ Q.D) = Q.q (a*v*a⁻¹) ∧
      (coreActorRepresentation Q split i hV).asModuleEquiv
        (coreCoefficientRepresentation Q split i hV n ⟨Q.q a,ha⟩
          ((coreActorRepresentation Q split i hV).asModuleEquiv.symm
            (Additive.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split i)) ⟨Q.q v,hv⟩)))) =
        Additive.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split i)) w) := by
  let w := coreActorAction Q split i hV ⟨Q.q a,ha⟩ ⟨Q.q v,hv⟩
  refine ⟨w,?_,?_⟩
  · change Q.q a * Q.q v * (Q.q a)⁻¹ = Q.q (a*v*a⁻¹)
    rw [map_mul,map_mul,map_inv]
  · rw [coreCoefficientRepresentation_apply,LinearEquiv.apply_symm_apply]
    exact congrArg Additive.ofMul (Subgroup.quotientAut_apply_mk
      (frattini (simpleRemainder Q split i))
      (coreActorAction Q split i hV ⟨Q.q a,ha⟩) ⟨Q.q v,hv⟩)

theorem original_nonzero_coefficient_conjugation (h : HypothesisF11 L S)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card (coreCartan Q i) = 2^n-1)
    (c : CoreCoefficientField Q split i hV n) (hc : c ≠ 0) :
    ∃ a : generated L S, Q.q a ∈ coreCartan Q i ∧
      ∀ (v : generated L S) (hv : Q.q v ∈ simpleRemainder Q split i),
      ∃ w : simpleRemainder Q split i,
        (w : (generated L S) ⧸ Q.D) = Q.q (a*v*a⁻¹) ∧
        (coreActorRepresentation Q split i hV).asModuleEquiv
          (c • (coreActorRepresentation Q split i hV).asModuleEquiv.symm
            (Additive.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split i)) ⟨Q.q v,hv⟩))) =
          Additive.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split i)) w) := by
  obtain ⟨k,hk⟩ := coreCoefficient_nonzero_scalar Q split i hV n hn
    (MarkedLocal.parabolic_core_selfCentralizing Q (originalMarkedIso Q) h i) hcard c hc
  obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective Q.D k.val
  have ha' : Q.q a = k.val := ha
  have hamem : Q.q a ∈ coreCartan Q i := by rw [ha']; exact k.property
  refine ⟨a,hamem,fun v hv => ?_⟩
  obtain ⟨w,hw,he⟩ := original_core_representation_quotient Q split i a v hamem hv
  refine ⟨w,hw,?_⟩
  rw [hk,LinearEquiv.apply_symm_apply]
  have heq : (⟨Q.q a,hamem⟩ : coreCartan Q i) = k := Subtype.ext ha'
  rwa [heq] at he

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
