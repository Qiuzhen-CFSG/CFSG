module

public import Theory.Character.ModularBlock.ScalarAction
public import Theory.Character.ModularBlock.PrincipalReduction

/-!
# Algebra of localized central-character scalars

The scalar supplied by a localized central character is multiplicative:
embed into the complex numbers, use the representation action of a product,
and cancel its faithful scalar action on a nonzero irreducible module.
Subtraction follows termwise from the class-sum formula, and positive powers
follow from multiplicativity. The principal selector has its defining
zero-or-one scalar. Finally, coefficientwise zero reduction forces every
central scalar to reduce to zero.

These are the scalar identities for the DVR proof of block primitivity.
Ported from the scalar-algebra portion of
`c3503435:glauberman_zStar/Submission/ZStar/BlockPrimitivity.lean`, reusing
the canonical localization and representation APIs.
-/

public section
noncomputable section
namespace ModularBlock.BlockPrimitivity
open BlockOrthogonality
attribute [local instance] Fintype.ofFinite
open scoped BigOperators

private theorem smul_one_injective
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Nontrivial V] :
    Function.Injective
      (fun a : ℂ => a • (1 : Module.End ℂ V)) := by
  intro a b hab
  apply FaithfulSMul.algebraMap_injective ℂ (Module.End ℂ V)
  simpa [Algebra.algebraMap_eq_smul_one] using hab


theorem localizedCentralScalar_mul
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (i : d.I)
    (z w : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)) :
    CentralScalarCongruence.localizedCentralScalar d.eta_spec
        d.primeIdeal (d.chi i) (d.complete.1 i) (z * w) =
      CentralScalarCongruence.localizedCentralScalar d.eta_spec
          d.primeIdeal (d.chi i) (d.complete.1 i) z *
        CentralScalarCongruence.localizedCentralScalar d.eta_spec
          d.primeIdeal (d.chi i) (d.complete.1 i) w := by
  rcases (d.complete.1 i).1 with ⟨n, ρ, hρ⟩
  have hρirr : Representation.IsIrreducible ρ := by
    apply (irreducible_iff_character_norm_one (ρ := ρ)).2
    simpa [hρ] using (d.complete.1 i).2
  let : Representation.IsIrreducible ρ := hρirr
  let : Nontrivial (Fin n → ℂ) :=
    irreducible_nontrivial (ρ := ρ)
  have hz := localizedCentralScalar_action d i ρ hρ z
  have hw := localizedCentralScalar_action d i ρ hρ w
  have hzw := localizedCentralScalar_action d i ρ hρ (z * w)
  have hscalar :
      localizationToComplex d.primeIdeal
          (CentralScalarCongruence.localizedCentralScalar d.eta_spec
            d.primeIdeal (d.chi i) (d.complete.1 i) (z * w)) =
        localizationToComplex d.primeIdeal
            (CentralScalarCongruence.localizedCentralScalar d.eta_spec
              d.primeIdeal (d.chi i) (d.complete.1 i) z) *
          localizationToComplex d.primeIdeal
            (CentralScalarCongruence.localizedCentralScalar d.eta_spec
              d.primeIdeal (d.chi i) (d.complete.1 i) w) := by
    apply smul_one_injective
      (V := Fin n → ℂ)
    change
      localizationToComplex d.primeIdeal
          (CentralScalarCongruence.localizedCentralScalar d.eta_spec
            d.primeIdeal (d.chi i) (d.complete.1 i) (z * w)) •
          (1 : Module.End ℂ (Fin n → ℂ)) =
        (localizationToComplex d.primeIdeal
            (CentralScalarCongruence.localizedCentralScalar d.eta_spec
              d.primeIdeal (d.chi i) (d.complete.1 i) z) *
          localizationToComplex d.primeIdeal
            (CentralScalarCongruence.localizedCentralScalar d.eta_spec
              d.primeIdeal (d.chi i) (d.complete.1 i) w)) •
          (1 : Module.End ℂ (Fin n → ℂ))
    calc
      _ = ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (localizationToComplex d.primeIdeal) (z * w)) :=
        hzw.symm
      _ = ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (localizationToComplex d.primeIdeal) z) *
          ρ.asAlgebraHom
            (MonoidAlgebra.mapRingHom G (localizationToComplex d.primeIdeal) w) := by
        rw [map_mul, map_mul]
      _ = _ := by rw [hz, hw]; simp [Algebra.smul_def]
  apply localizationToComplex_injective d
  simpa using hscalar

/-- Localized central-character scalars preserve subtraction. -/

theorem localizedCentralScalar_sub
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (i : d.I)
    (z w : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)) :
    CentralScalarCongruence.localizedCentralScalar d.eta_spec
        d.primeIdeal (d.chi i) (d.complete.1 i) (z - w) =
      CentralScalarCongruence.localizedCentralScalar d.eta_spec
          d.primeIdeal (d.chi i) (d.complete.1 i) z -
        CentralScalarCongruence.localizedCentralScalar d.eta_spec
          d.primeIdeal (d.chi i) (d.complete.1 i) w := by
  classical
  rw [CentralScalarCongruence.localizedCentralScalar,
    CentralScalarCongruence.localizedCentralScalar,
    CentralScalarCongruence.localizedCentralScalar,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _hc
  change
    (z.1.coeff (CentralScalarCongruence.classRepresentative c) -
        w.1.coeff (CentralScalarCongruence.classRepresentative c)) * _ =
      z.1.coeff (CentralScalarCongruence.classRepresentative c) * _ -
        w.1.coeff (CentralScalarCongruence.classRepresentative c) * _
  exact sub_mul _ _ _


theorem localizedCentralScalar_pow_of_pos
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (i : d.I)
    (z : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G))
    (N : ℕ) (hN : 0 < N) :
    CentralScalarCongruence.localizedCentralScalar d.eta_spec
        d.primeIdeal (d.chi i) (d.complete.1 i) (z ^ N) =
      CentralScalarCongruence.localizedCentralScalar d.eta_spec
          d.primeIdeal (d.chi i) (d.complete.1 i) z ^ N := by
  induction N using Nat.case_strong_induction_on with
  | hz => omega
  | hi N ih =>
      by_cases hN0 : N = 0
      · subst N
        simp
      · rw [pow_succ, pow_succ, localizedCentralScalar_mul]
        rw [ih N (by omega) (Nat.pos_of_ne_zero hN0)]


theorem localizedCentralScalar_localizedPrincipalBlockElement
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (i : d.I) :
    let e : Subring.center
        (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G) :=
      ⟨BlockOrthogonality.localizedPrincipalBlockElement d,
        BlockOrthogonality.localizedPrincipalBlockElement_mem_center d⟩
    CentralScalarCongruence.localizedCentralScalar d.eta_spec
        d.primeIdeal (d.chi i) (d.complete.1 i) e =
      if i ∈ d.block then 1 else 0 := by
  dsimp only
  let e : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G) :=
    ⟨BlockOrthogonality.localizedPrincipalBlockElement d,
      BlockOrthogonality.localizedPrincipalBlockElement_mem_center d⟩
  rcases (d.complete.1 i).1 with ⟨n, rho, hrho⟩
  have hrhoIrr : Representation.IsIrreducible rho := by
    apply (irreducible_iff_character_norm_one (ρ := rho)).2
    simpa [hrho] using (d.complete.1 i).2
  let : Representation.IsIrreducible rho := hrhoIrr
  let : Nontrivial (Fin n → ℂ) :=
    irreducible_nontrivial (ρ := rho)
  apply localizationToComplex_injective d
  apply smul_one_injective (V := Fin n → ℂ)
  have hscalar := localizedCentralScalar_action d i rho hrho e
  have hindicator :=
    BlockOrthogonality.principalBlockElement_action d i rho hrho
  have hmap :=
    BlockOrthogonality.mapRingHom_localizedPrincipalBlockElement_eq_principalBlockElement
      d (localizationToComplex d.primeIdeal) (localizationToComplex_algebraMap d.primeIdeal)
  calc
    localizationToComplex d.primeIdeal
          (CentralScalarCongruence.localizedCentralScalar d.eta_spec
            d.primeIdeal (d.chi i) (d.complete.1 i) e) •
        (1 : Module.End ℂ (Fin n → ℂ)) =
      rho.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (localizationToComplex d.primeIdeal)
          (BlockOrthogonality.localizedPrincipalBlockElement d)) := by
        simpa [e] using hscalar.symm
    _ = rho.asAlgebraHom (BlockOrthogonality.principalBlockElement d) := by
      rw [hmap]
    _ = (if i ∈ d.block then (1 : ℂ) else 0) •
        (1 : Module.End ℂ (Fin n → ℂ)) := hindicator
    _ = localizationToComplex d.primeIdeal
          (if i ∈ d.block then (1 : Localization.AtPrime d.primeIdeal)
            else 0) • (1 : Module.End ℂ (Fin n → ℂ)) := by
        split <;> simp


theorem localizationToResidue_localizedCentralScalar_eq_zero_of_map_eq_zero
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (i : d.I)
    (z : Subring.center
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G))
    (hz : MonoidAlgebra.mapRingHom G
        (BrauerBlockReduction.localizationToResidue d) z.1 = 0) :
    BrauerBlockReduction.localizationToResidue d
        (CentralScalarCongruence.localizedCentralScalar d.eta_spec
          d.primeIdeal (d.chi i) (d.complete.1 i) z) = 0 := by
  classical
  rw [CentralScalarCongruence.localizedCentralScalar, map_sum]
  apply Finset.sum_eq_zero
  intro c _hc
  rw [map_mul]
  have hc := congrArg
    (fun a : MonoidAlgebra
        (BrauerBlockReduction.principalResidueField d) G =>
      a.coeff (CentralScalarCongruence.classRepresentative c)) hz
  change BrauerBlockReduction.localizationToResidue d
      (z.1.coeff (CentralScalarCongruence.classRepresentative c)) = 0 at hc
  have hcoeff : BrauerBlockReduction.localizationToResidue d
      (CentralScalarCongruence.centralClassCoefficient z c) = 0 := by
    exact hc
  rw [hcoeff, zero_mul]


end ModularBlock.BlockPrimitivity
