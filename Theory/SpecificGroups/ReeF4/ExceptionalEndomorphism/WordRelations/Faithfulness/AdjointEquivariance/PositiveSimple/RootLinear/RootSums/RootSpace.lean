module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.Basic
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.RouteOperators
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basis


/-!
# The F4 operator commutator lies in its sum-root line

Extend the integral Geck construction to an algebraic closure of the rationals.
The Leibniz identity adds the Cartan weights of a commutator, and closure of
Geck's Lie algebra places it in the corresponding Lie root space. Multiplicity
one makes it proportional to a Tits conjugate at the sum root. Undoing that
conjugate and reading the primitive opposite-simple column shows that the
scalar is an integer. Specialization and the proved arbitrary-route comparison
then give proportionality for the actual F4 coordinate operators.

The Cartan-basis and root-space argument is adapted from
`GeckIrreducibleRationalRootspaceOne`; unlike its equal-route theorem, the first
matrix here is a commutator and is allowed to vanish. The integral coordinate
argument follows `Intertwining.Transport.RouteComparison`. Both are based on
Geck (2017), Lemmas 3.5 and 4.3, and the Killing-root multiplicity-one theorem
implemented in Mathlib. No operator commutator relation is assumed.
-/

public section

open scoped Matrix
open RootPairing.IntegralGeckConstruction
namespace ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple.RootSumSpace
noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

section Closed
variable {ι R M N : Type*} [Field R] [CharZero R] [IsAlgClosed R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic]
  [P.IsReduced] [P.IsIrreducible]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

private noncomputable def geckCartanBasis :
    Module.Basis b.support R
      (RootPairing.GeckConstruction.cartanSubalgebra' b) :=
  Module.Basis.mk
    (v := RootPairing.GeckConstruction.h' (P := P) (b := b)) (by
      apply LinearIndependent.of_comp
        ((RootPairing.GeckConstruction.lieAlgebra b).subtype.comp
          (RootPairing.GeckConstruction.cartanSubalgebra' b).subtype)
      exact RootPairing.GeckConstruction.linearIndependent_h b)
    (by rw [RootPairing.GeckConstruction.span_range_h'_eq_top])

private lemma geckCartanBasis_apply (l : b.support) :
    geckCartanBasis (P := P) (R := R) (b := b) l =
      RootPairing.GeckConstruction.h' l := by
  rw [geckCartanBasis]
  apply Module.Basis.mk_apply

private noncomputable def geckWeightLinear (k : ι) :
    RootPairing.GeckConstruction.cartanSubalgebra' b →ₗ[R] R :=
  (geckCartanBasis (P := P) (R := R) (b := b)).constr R
    (fun l => P.pairing k l)

private lemma geckWeightLinear_h' (k : ι) (l : b.support) :
    geckWeightLinear (P := P) (R := R) (b := b) k
        (RootPairing.GeckConstruction.h' l) = P.pairing k l := by
  rw [← geckCartanBasis_apply (P := P) (R := R) (b := b) l]
  apply Module.Basis.constr_basis

private lemma geckWeightLinear_ne_zero (k : ι) :
    geckWeightLinear (P := P) (R := R) (b := b) k ≠ 0 := by
  obtain ⟨j, hj, hj0⟩ := b.exists_mem_support_pos_pairingIn_ne_zero k
  have hrev : P.pairingIn ℤ k j ≠ 0 := by
    rw [ne_eq, P.pairingIn_eq_zero_iff]
    exact hj0
  have hpair : P.pairing k j ≠ 0 := by
    rw [← P.algebraMap_pairingIn ℤ]
    exact (FaithfulSMul.algebraMap_eq_zero_iff ℤ R).not.mpr hrev
  intro hzero
  apply hpair
  have h := LinearMap.congr_fun hzero
    (RootPairing.GeckConstruction.h' (b := b) ⟨j, hj⟩)
  simpa only [geckWeightLinear_h', LinearMap.zero_apply] using h

private lemma mem_geckWeightSpace_of_hasRootWeight (k : ι)
    {X : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R}
    (hXmem : X ∈ RootPairing.GeckConstruction.lieAlgebra b)
    (hXweight : HasRootWeight (P := P) (b := b) k X) :
    (⟨X, hXmem⟩ : RootPairing.GeckConstruction.lieAlgebra b) ∈
      LieModule.genWeightSpace (RootPairing.GeckConstruction.lieAlgebra b)
        (geckWeightLinear (P := P) (R := R) (b := b) k) := by
  let L := RootPairing.GeckConstruction.lieAlgebra b
  let H := RootPairing.GeckConstruction.cartanSubalgebra' b
  let X' : L := ⟨X, hXmem⟩
  rw [LieModule.mem_genWeightSpace]
  intro x
  have hx : x ∈ Submodule.span R (Set.range
      (RootPairing.GeckConstruction.h' (P := P) (b := b))) := by
    rw [RootPairing.GeckConstruction.span_range_h'_eq_top]
    exact Submodule.mem_top
  have heigen : ∀ y : H, y ∈ Submodule.span R (Set.range
      (RootPairing.GeckConstruction.h' (P := P) (b := b))) →
      ⁅(y : L), X'⁆ =
        geckWeightLinear (P := P) (R := R) (b := b) k y • X' := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        rcases hy with ⟨l, rfl⟩
        rw [geckWeightLinear_h']
        exact Subtype.ext (hXweight l)
    | zero => simp
    | add y z _ _ hy hz =>
        rw [show ((↑(y + z) : L)) = (y : L) + (z : L) by
          exact map_add H.subtype y z]
        rw [add_lie, map_add, hy, hz, add_smul]
    | smul c y _ hy =>
        rw [show ((↑(c • y) : L)) = c • (y : L) by
          exact map_smul H.subtype c y]
        rw [smul_lie, map_smul, hy, smul_smul]
        simp only [smul_eq_mul]
  refine ⟨1, ?_⟩
  simp only [pow_one, LinearMap.sub_apply, LieModule.toEnd_apply_apply,
    LinearMap.smul_apply, Module.End.one_apply]
  exact sub_eq_zero.mpr (heigen x hx)

private lemma undo_titsConjugate (word : List b.support)
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
    titsWordInv word * titsConjugate word A * titsWord word = A := by
  rw [titsConjugate_apply]
  calc
    titsWordInv word * (titsWord word * A * titsWordInv word) * titsWord word =
        (titsWordInv word * titsWord word) * A *
          (titsWordInv word * titsWord word) := by noncomm_ring
    _ = A := by rw [titsWord_inv_mul, Matrix.one_mul, Matrix.mul_one]

private lemma titsConjugate_ne_zero (word : List b.support) (i : b.support) :
    titsConjugate word (eMatrix i) ≠ 0 := by
  intro hzero
  have h := congrArg
    (fun A => titsWordInv word * A * titsWord word) hzero
  rw [undo_titsConjugate, Matrix.mul_zero, Matrix.zero_mul] at h
  have hvec := eMatrix_mulVec_v_neg (P := P) i
  rw [h, Matrix.zero_mulVec] at hvec
  have hentry := congrFun hvec (Sum.inl i)
  simpa [u, Pi.single_apply] using hentry

private lemma map_titsConjugate_ne_zero (word : List b.support) (i : b.support) :
    (titsConjugate word (eMatrix i)).map (algebraMap ℤ R) ≠ 0 := by
  intro hzero
  apply titsConjugate_ne_zero (P := P) word i
  apply Matrix.map_injective (FaithfulSMul.algebraMap_injective ℤ R)
  simpa using hzero

/-- Any matrix in Geck's Lie algebra with a specified root weight is a scalar
multiple of an integral Tits conjugate in that root line. -/
lemma exists_scalar_of_weight
    (X : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)
    (z : List b.support) (j : b.support)
    (hXmem : X ∈ RootPairing.GeckConstruction.lieAlgebra b)
    (hXweight : HasRootWeight (P := P) (b := b) (reflectionWord z j) X) :
    ∃ c : R,
      X =
        c • (titsConjugate z (eMatrix j)).map (algebraMap ℤ R) := by
  let L := RootPairing.GeckConstruction.lieAlgebra b
  let H := RootPairing.GeckConstruction.cartanSubalgebra' b
  let k : ι := reflectionWord z j
  let A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
    X
  let B : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
    (titsConjugate z (eMatrix j)).map (algebraMap ℤ R)
  have hAmem : A ∈ L := hXmem
  have hBmem : B ∈ L := by
    dsimp only [B]
    apply map_titsConjugate_mem_lieAlgebra (P := P) (R := R) (b := b) z
    rw [map_eMatrix]
    exact RootPairing.GeckConstruction.e_mem_lieAlgebra (P := P) j
  have hB0 : B ≠ 0 := map_titsConjugate_ne_zero (P := P) (R := R) z j
  have hAspace : (⟨A, hAmem⟩ : L) ∈
      LieModule.genWeightSpace L
        (geckWeightLinear (P := P) (R := R) (b := b) k) :=
    mem_geckWeightSpace_of_hasRootWeight (P := P) (R := R) (b := b) k hAmem
      hXweight
  have hBspace : (⟨B, hBmem⟩ : L) ∈
      LieModule.genWeightSpace L
        (geckWeightLinear (P := P) (R := R) (b := b) k) :=
    mem_geckWeightSpace_of_hasRootWeight (P := P) (R := R) (b := b) k hBmem
      (by simpa only [B, k] using
        map_titsConjugate_hasRootWeight (P := P) (R := R) (b := b) z j)
  have hspace0 : LieModule.genWeightSpace L
      (geckWeightLinear (P := P) (R := R) (b := b) k) ≠ ⊥ := by
    intro hbot
    rw [LieSubmodule.eq_bot_iff] at hbot
    apply hB0
    have hzero := hbot ⟨B, hBmem⟩ hBspace
    exact congrArg (fun x : L =>
      ((x : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R))) hzero
  let α : LieModule.Weight R H L :=
    ⟨geckWeightLinear (P := P) (R := R) (b := b) k, hspace0⟩
  have hAroot : (⟨A, hAmem⟩ : L) ∈ LieAlgebra.rootSpace H α := hAspace
  have hBroot : (⟨B, hBmem⟩ : L) ∈ LieAlgebra.rootSpace H α := hBspace
  have hα : α.IsNonZero := by
    intro hzero
    apply geckWeightLinear_ne_zero (P := P) (R := R) (b := b) k
    apply LinearMap.ext
    intro x
    exact congrFun hzero x
  let : LieAlgebra.HasTrivialRadical R L :=
    RootPairing.GeckConstruction.instHasTrivialRadical
  let : Module.Finite R L := inferInstance
  let : LieAlgebra.IsKilling R L := inferInstance
  have hfin : Module.finrank R (LieAlgebra.rootSpace H α) = 1 :=
    LieAlgebra.IsKilling.finrank_rootSpace_eq_one α hα
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp hfin
  obtain ⟨a, ha⟩ := hv ⟨⟨A, hAmem⟩, hAroot⟩
  obtain ⟨d, hd⟩ := hv ⟨⟨B, hBmem⟩, hBroot⟩
  have hd0 : d ≠ 0 := by
    intro hdzero
    apply hB0
    have := congrArg (fun x : LieAlgebra.rootSpace H α => ((x : L) :
      Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)) hd
    simpa [hdzero, B] using this.symm
  refine ⟨a / d, ?_⟩
  have hscaled := congrArg (fun x : LieAlgebra.rootSpace H α => ((x : L) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R))
      (show (a / d) • (d • v) = a • v by
        rw [smul_smul, div_mul_cancel₀ a hd0])
  simpa [ha, hd, A, B] using hscaled.symm

/-- An integral matrix of root weight in Geck's Lie algebra is an integral
multiple of the corresponding Tits conjugate. Undoing the conjugation and
reading its primitive opposite-simple column recovers the integer coefficient.
This applies to divided commutators as well as ordinary commutators. -/
lemma integral_matrix_eq_smul_titsConjugate_of_weight
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)
    (z : List b.support) (k : b.support)
    (hAmem : A.map (algebraMap ℤ R) ∈ RootPairing.GeckConstruction.lieAlgebra b)
    (hAweight : HasRootWeight (P := P) (b := b) (reflectionWord z k)
      (A.map (algebraMap ℤ R))) :
    ∃ n : ℤ, A = n • titsConjugate z (eMatrix k) := by
  obtain ⟨c, hc⟩ := exists_scalar_of_weight (P := P)
    (A.map (algebraMap ℤ R)) z k hAmem hAweight
  let := P.indexNeg
  let C := titsConjugate z (eMatrix k)
  let n := (titsWordInv z * A * titsWord z) (Sum.inl k) (Sum.inr (-k : ι))
  have hn : (n : R) = c := by
    have h := congrArg (fun X : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R =>
      ((titsWordInv z).map (algebraMap ℤ R) * X * (titsWord z).map (algebraMap ℤ R))
        (Sum.inl k) (Sum.inr (-k : ι))) hc
    have hu : titsWordInv z * C * titsWord z = eMatrix k := undo_titsConjugate z (eMatrix k)
    simp only [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.map_mul] at h
    change (n : R) = (c • (titsWordInv z * C * titsWord z).map (algebraMap ℤ R))
      (Sum.inl k) (Sum.inr (-k : ι)) at h
    rw [hu] at h
    simpa [eMatrix] using h
  refine ⟨n, ?_⟩
  apply Matrix.map_injective (FaithfulSMul.algebraMap_injective ℤ R)
  change A.map (algebraMap ℤ R) = (n • C).map (algebraMap ℤ R)
  rw [Matrix.map_smul _ _ (map_zsmul _ _), ← Int.cast_smul_eq_zsmul R, hn]
  exact hc

private lemma integral_bracket_line
    (i : b.support) (w z : List b.support) (j k : b.support)
    (hroot : P.root (reflectionWord z k) = P.root i + P.root (reflectionWord w j)) :
    ∃ n : ℤ,
      eMatrix i * titsConjugate w (eMatrix j) - titsConjugate w (eMatrix j) * eMatrix i =
        n • titsConjugate z (eMatrix k) := by
  let E := (eMatrix (P := P) i).map (algebraMap ℤ R)
  let B := (titsConjugate w (eMatrix j)).map (algebraMap ℤ R)
  let A := eMatrix i * titsConjugate w (eMatrix j) - titsConjugate w (eMatrix j) * eMatrix i
  have hA : A.map (algebraMap ℤ R) = ⁅E, B⁆ := by
    simp only [A, E, B, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Ring.lie_def]
  have hEmem : E ∈ RootPairing.GeckConstruction.lieAlgebra b := by
    rw [show E = RootPairing.GeckConstruction.e i from map_eMatrix i]
    exact RootPairing.GeckConstruction.e_mem_lieAlgebra i
  have hBmem : B ∈ RootPairing.GeckConstruction.lieAlgebra b := by
    apply map_titsConjugate_mem_lieAlgebra
    rw [map_eMatrix]
    exact RootPairing.GeckConstruction.e_mem_lieAlgebra j
  have hEweight : HasRootWeight (P := P) (b := b) i E := by
    have h := map_titsConjugate_hasRootWeight (P := P) ([] : List b.support) i
    simpa only [reflectionWord, titsConjugate_apply, titsWord, titsWordInv_nil,
      one_mul, mul_one] using h
  have hBweight := map_titsConjugate_hasRootWeight (P := P) w j
  have hAweight : HasRootWeight (P := P) (b := b) (reflectionWord z k)
      (A.map (algebraMap ℤ R)) := by
    rw [hA]
    intro l
    rw [leibniz_lie, hEweight l, hBweight l, smul_lie, lie_smul, ← add_smul,
      RootPairing.pairing_eq_add_of_root_eq_add hroot]
  exact integral_matrix_eq_smul_titsConjugate_of_weight (P := P) A z k
    (by rw [hA]; exact (RootPairing.GeckConstruction.lieAlgebra b).lie_mem hEmem hBmem)
    hAweight

end Closed

open Theory.AlgebraicGroup StandardRootSystem

private lemma extension_root_add {r t s : typeF4Roots}
    (h : typeF4RootPairing.root s = typeF4RootPairing.root r + typeF4RootPairing.root t) :
    (scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base)).root s =
      (scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base)).root r +
        (scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base)).root t := by
  have hs : typeF4RootPairing.rootSpanMem ℤ s =
      typeF4RootPairing.rootSpanMem ℤ r + typeF4RootPairing.rootSpanMem ℤ t :=
    Subtype.ext h
  change scalarExtensionRoot s = scalarExtensionRoot r + scalarExtensionRoot t
  ext l
  simp only [scalarExtensionRoot, hs, map_add, Finsupp.add_apply, Pi.add_apply]

/-- The actual root-sum commutator belongs to the actual sum-root operator line. -/
theorem positive_root_commutator_mem_line (m : ℕ) (i : typeF4RootPairing_base.support)
    (r s : typeF4Roots)
    (h : typeF4RootPairing.root s = typeF4RootPairing.root i + typeF4RootPairing.root r) :
    ∃ c : CoefficientField m,
      dividedPower m i 1 * coordinateOperator m (Sum.inr r) -
        coordinateOperator m (Sum.inr r) * dividedPower m i 1 =
          c • coordinateOperator m (Sum.inr s) := by
  let w := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
  let z := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) s
  have hroot :
      (scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base)).root
          (reflectionWord (P := scalarExtension (P := typeF4RootPairing)
            (b := typeF4RootPairing_base))
            (b := scalarExtensionBase (P := typeF4RootPairing) (b := typeF4RootPairing_base))
            z.word z.simple) =
        (scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base)).root i +
          (scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base)).root
            (reflectionWord (P := scalarExtension (P := typeF4RootPairing)
              (b := typeF4RootPairing_base))
              (b := scalarExtensionBase (P := typeF4RootPairing) (b := typeF4RootPairing_base))
              w.word w.simple) := by
    simpa only [scalarExtension_reflectionWord, w.target, z.target] using extension_root_add h
  obtain ⟨n, hn⟩ := integral_bracket_line
    (P := scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base))
    (b := scalarExtensionBase (P := typeF4RootPairing) (b := typeF4RootPairing_base))
    i w.word z.word w.simple z.simple hroot
  rw [scalarExtension_eMatrix, scalarExtension_eMatrix, scalarExtension_eMatrix,
    scalarExtension_titsConjugate, scalarExtension_titsConjugate] at hn
  refine ⟨n, ?_⟩
  rw [coordinateOperator_eq_transport m r w.word w.simple w.target,
    coordinateOperator_eq_transport m s z.word z.simple z.target]
  have hc := congrArg (fun A : Matrix Coordinate Coordinate ℤ =>
    A.map (Int.castRingHom (CoefficientField m))) hn
  change (eMatrix i * titsConjugate w.word (eMatrix w.simple) -
    titsConjugate w.word (eMatrix w.simple) * eMatrix i).map
      (Int.castRingHom (CoefficientField m)) =
        (n • titsConjugate z.word (eMatrix z.simple)).map
          (Int.castRingHom (CoefficientField m)) at hc
  simpa only [Matrix.map_sub _ (map_sub _), Matrix.map_mul,
    Matrix.map_smul _ _ (map_zsmul _ _), ← Int.cast_smul_eq_zsmul (CoefficientField m),
    titsConjugate_apply, transportedMatrix, dividedPower, eDividedPower_one] using hc

end
end ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple.RootSumSpace
