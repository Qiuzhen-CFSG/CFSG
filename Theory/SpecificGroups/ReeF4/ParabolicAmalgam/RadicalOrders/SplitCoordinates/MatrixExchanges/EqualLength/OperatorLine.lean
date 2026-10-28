module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges.RootSums
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.RootSums

/-!
# Integral sum-root lines for positive F4 operators

The commutator of two routed operators belongs to the Lie algebra and has
sum-root weight. Root-space multiplicity one and the primitive integral
coordinate of a routed simple operator put it in the integral sum-root line.
Cartan columns then determine its scalar in characteristic two, using the
all-root vector-action formula. No group commutator is assumed here.

Sources: Geck's integral construction and root-space argument, as developed
in `RootLinear.RootSums`; Chevalley collection underlying Aschbacher–Smith,
F.1.12(I)(5), printed p.263 of `refs/quasithin.pdf`.
-/

public section

open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped Matrix
namespace ReeF4.Parabolics.RadicalCoordinates.EqualLength
noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

private lemma integral_route_bracket_line
    {ι R M N : Type*} [Field R] [CharZero R] [IsAlgClosed R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced] [P.IsIrreducible] {b : P.Base} [Fintype ι] [DecidableEq ι]
    (u w z : List b.support) (i j k : b.support)
    (hroot : P.root (reflectionWord z k) =
      P.root (reflectionWord u i) + P.root (reflectionWord w j)) :
    ∃ n : ℤ,
      titsConjugate u (eMatrix i) * titsConjugate w (eMatrix j) -
        titsConjugate w (eMatrix j) * titsConjugate u (eMatrix i) =
          n • titsConjugate z (eMatrix k) := by
  let E := (titsConjugate u (eMatrix i)).map (algebraMap ℤ R)
  let B := (titsConjugate w (eMatrix j)).map (algebraMap ℤ R)
  let A := titsConjugate u (eMatrix i) * titsConjugate w (eMatrix j) -
    titsConjugate w (eMatrix j) * titsConjugate u (eMatrix i)
  have hA : A.map (algebraMap ℤ R) = ⁅E, B⁆ := by
    simp only [A, E, B, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Ring.lie_def]
  have hmem (v : List b.support) (l : b.support) :
      (titsConjugate v (eMatrix l)).map (algebraMap ℤ R) ∈
        RootPairing.GeckConstruction.lieAlgebra b := by
    apply map_titsConjugate_mem_lieAlgebra
    rw [map_eMatrix]
    exact RootPairing.GeckConstruction.e_mem_lieAlgebra l
  have hEweight := map_titsConjugate_hasRootWeight (P := P) u i
  have hBweight := map_titsConjugate_hasRootWeight (P := P) w j
  have hAweight : HasRootWeight (P := P) (b := b) (reflectionWord z k)
      (A.map (algebraMap ℤ R)) := by
    rw [hA]
    intro l
    rw [leibniz_lie, hEweight l, hBweight l, smul_lie, lie_smul, ← add_smul,
      RootPairing.pairing_eq_add_of_root_eq_add hroot]
  exact WordRelations.Faithfulness.Adjoint.PositiveSimple.RootSumSpace.integral_matrix_eq_smul_titsConjugate_of_weight (P := P) A z k
      (by
        rw [hA]
        exact (RootPairing.GeckConstruction.lieAlgebra b).lie_mem (hmem u i) (hmem w j)) hAweight

private lemma extension_root_add {r s t : F4Chevalley.Root}
    (h : typeF4RootPairing.root t = typeF4RootPairing.root r + typeF4RootPairing.root s) :
    (scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base)).root t =
      (scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base)).root r +
        (scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base)).root s := by
  have hs : typeF4RootPairing.rootSpanMem ℤ t =
      typeF4RootPairing.rootSpanMem ℤ r + typeF4RootPairing.rootSpanMem ℤ s :=
    Subtype.ext h
  change scalarExtensionRoot t = scalarExtensionRoot r + scalarExtensionRoot s
  ext l
  simp only [scalarExtensionRoot, hs, map_add, Finsupp.add_apply, Pi.add_apply]

/-- The commutator of positive integral operators is an integral multiple of
the sum-root operator. This is an equality of whole matrices. -/
theorem integralOperators_bracket_mem_sum_line (r s t : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (hs : typeF4RootPairing_base.IsPos s)
    (ht : typeF4RootPairing.root t = typeF4RootPairing.root r + typeF4RootPairing.root s) :
    ∃ n : ℤ,
      F4Chevalley.integralOperators.rootOperator r * F4Chevalley.integralOperators.rootOperator s -
        F4Chevalley.integralOperators.rootOperator s * F4Chevalley.integralOperators.rootOperator r =
          n • F4Chevalley.integralOperators.rootOperator t := by
  classical
  let u := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
  let w := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) s
  let z := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) t
  have hroot :
      (scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base)).root
        (reflectionWord (P := scalarExtension (P := typeF4RootPairing)
          (b := typeF4RootPairing_base))
          (b := scalarExtensionBase (P := typeF4RootPairing) (b := typeF4RootPairing_base))
          z.word z.simple) =
      (scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base)).root
        (reflectionWord (P := scalarExtension (P := typeF4RootPairing)
          (b := typeF4RootPairing_base))
          (b := scalarExtensionBase (P := typeF4RootPairing) (b := typeF4RootPairing_base))
          u.word u.simple) +
      (scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base)).root
        (reflectionWord (P := scalarExtension (P := typeF4RootPairing)
          (b := typeF4RootPairing_base))
          (b := scalarExtensionBase (P := typeF4RootPairing) (b := typeF4RootPairing_base))
          w.word w.simple) := by
    simpa only [scalarExtension_reflectionWord, u.target, w.target, z.target]
      using extension_root_add ht
  obtain ⟨n, hn⟩ := integral_route_bracket_line
    (P := scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base))
    (b := scalarExtensionBase (P := typeF4RootPairing) (b := typeF4RootPairing_base))
    u.word w.word z.word u.simple w.simple z.simple hroot
  simp only [scalarExtension_eMatrix, scalarExtension_titsConjugate] at hn
  refine ⟨n, ?_⟩
  change rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) r *
      rootOperator s - rootOperator s * rootOperator r = n • rootOperator t
  rw [rootOperator_of_pos r hr, rootOperator_of_pos s hs, rootOperator_of_pos t (hr.add hs ht)]
  exact hn

open WordRelations.Faithfulness.Adjoint WordRelations.Faithfulness.Adjoint.PositiveSimple

/-- The integral commutator scalar specializes to the lower-string coefficient.
In particular a coefficient two is zero even over the binary field. -/
theorem bracket_scalar_cast (m : ℕ) (r s t : F4Chevalley.Root) (n : ℤ)
    (ht : typeF4RootPairing.root t = typeF4RootPairing.root r + typeF4RootPairing.root s)
    (hn : F4Chevalley.integralOperators.rootOperator r *
        F4Chevalley.integralOperators.rootOperator s -
      F4Chevalley.integralOperators.rootOperator s * F4Chevalley.integralOperators.rootOperator r =
        n • F4Chevalley.integralOperators.rootOperator t) :
    (n : CoefficientField m) = (typeF4RootPairing.chainBotCoeff r s + 1 : CoefficientField m) := by
  classical
  have hc := congrArg (fun A : F4Chevalley.IntegralMatrix =>
    A.map (Int.castRingHom (CoefficientField m))) hn
  simp only [Matrix.map_sub _ (map_sub _), Matrix.map_mul,
    Matrix.map_smul _ _ (map_zsmul _ _), ← Int.cast_smul_eq_zsmul (CoefficientField m)] at hc
  change coordinateOperator m (Sum.inr r) * coordinateOperator m (Sum.inr s) -
    coordinateOperator m (Sum.inr s) * coordinateOperator m (Sum.inr r) =
      (n : CoefficientField m) • coordinateOperator m (Sum.inr t) at hc
  obtain ⟨j, hj⟩ := exists_pairingIn_cast_ne_zero m t
  have hv := congrArg (fun A : Matrix WordRelations.Coordinate WordRelations.Coordinate
    (CoefficientField m) => A *ᵥ Pi.single (Sum.inl j) 1) hc
  simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, coordinateOperator_mulVec_cartan,
    Matrix.mulVec_smul, Matrix.smul_mulVec] at hv
  rw [coordinateOperator_mulVec_root_add m r s t ht,
    coordinateOperator_mulVec_root_add m s r t (ht.trans (add_comm _ _)),
    chainBotCoeff_comm_of_root_add s r t (ht.trans (add_comm _ _))] at hv
  have he := congrFun hv (Sum.inr t)
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
    sub_eq_add_neg, CharTwo.neg_eq] at he
  have hpair : (typeF4RootPairing.pairingIn ℤ t j : CoefficientField m) =
      (typeF4RootPairing.pairingIn ℤ r j : CoefficientField m) +
        (typeF4RootPairing.pairingIn ℤ s j : CoefficientField m) := by
    rw [RootPairing.pairingIn_eq_add_of_root_eq_add (S := ℤ) ht, Int.cast_add]
  apply mul_right_cancel₀ hj
  rw [hpair] at he ⊢
  linear_combination -he

end
end ReeF4.Parabolics.RadicalCoordinates.EqualLength
