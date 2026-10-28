/-
Uses Gerald Höhn's ATLAS icosian and Conway constructions, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianAlternatingConwayProduct
public import Theory.AtlasPort.Janko2.Conway.IcosianMonomialFaithfulness
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.PrimeRankWitness

/-!
# A rank-three elementary subgroup of the lattice Conway quotient

Uniform diagonal blocks `diag(s⁻¹,s)`, with `s` in the units of the golden
field of order four, commute with cyclic permutation of the three blocks.
Their explicit product embedding in the icosian glue stabilizer gives an
elementary abelian subgroup of order nine. Coprime lifting through the
order-eight monomial kernel, followed by the faithful Hermitian representation
and the order-two central-sign quotient, preserves this subgroup.

An explicit three-cycle in `alternatingGroup (Fin 5)` supplies a third factor.
The established product embedding lands in the literal Leech lattice central
quotient, giving `3 ≤ primeRank 3 LeechCentralQuotient`. This discharges the
lattice-rank premise of the Monster local obstruction; it uses no comparison
with a catalogue carrier or ambient-order inference.

Sources: Gerald Höhn, ATLAS, `Codes/IcosianGlueStabilizer.lean`,
`Codes/IcosianGlueMonomial.lean`, and `Conway/IcosianAlternatingConwayProduct.lean`;
Aschbacher–Smith, A.2.19, for the consuming Monster exclusion.
-/

@[expose] public section

open Atlas.Algebra Atlas.Codes Atlas.Conway
open scoped IsMulCommutative
noncomputable section
namespace Sporadic.Monster.Construction.QuasithinObstruction

private theorem scalar_matrix_one {F : Type*} [Field F] :
    icosianGlueMatrix (1 : Fˣ) 0 = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [icosianGlueMatrix, Matrix.SpecialLinearGroup.coe_one]

private theorem scalar_matrix_mul {F : Type*} [Field F] (s t : Fˣ) :
    icosianGlueMatrix (s * t) 0 = icosianGlueMatrix s 0 * icosianGlueMatrix t 0 := by
  apply Subtype.ext
  change (!![((s : F) * (t : F))⁻¹, 0; 0, (s : F) * (t : F)] :
    Matrix (Fin 2) (Fin 2) F) =
      !![(s : F)⁻¹, 0; 0, (s : F)] * !![(t : F)⁻¹, 0; 0, (t : F)]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/-- Uniform diagonal blocks commute with the full permutation group of the three blocks. -/
def uniformMonomial : GoldenFourˣ × Equiv.Perm (Fin 3) →*
    icosianGlueMonomialStabilizer GoldenFour where
  toFun x := ⟨⟨fun _ => icosianGlueMatrix x.1 0, x.2⟩, by
    apply (icosianGlueMonomialStabilizer_iff _).mpr
    have h := (icosianGlueBlockParameterElement (x.1, 0, 0)).property
    convert h using 1
    funext i
    fin_cases i <;> simp [icosianGlueBlockParameterElement, icosianGlueBlockParameter]⟩
  map_one' := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · funext i
      exact scalar_matrix_one
    · rfl
  map_mul' x y := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · funext i
      exact scalar_matrix_mul x.1 y.1
    · rfl

/-- Both the scalar and the permutation are recovered from the actual coordinates. -/
theorem uniformMonomial_injective : Function.Injective uniformMonomial := by
  intro x y h
  have he := congrArg Subtype.val h
  apply Prod.ext
  · exact Units.ext (congrArg (fun g : IcosianGlueMonomialGroup GoldenFour =>
      g.left 0 1 1) he)
  · exact congrArg SemidirectProduct.right he

private def blockCycle : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
private theorem blockCycle_cube : blockCycle ^ 3 = 1 := by decide
private theorem blockCycle_ne_one : blockCycle ≠ 1 := by decide
private theorem blockCycle_order : orderOf blockCycle = 3 :=
  orderOf_eq_prime blockCycle_cube blockCycle_ne_one

private abbrev E9 := GoldenFourˣ × Subgroup.zpowers blockCycle

private theorem goldenUnits_card : Nat.card GoldenFourˣ = 3 := by
  rw [Nat.card_units, Nat.card_eq_fintype_card, goldenFour_card]

private theorem E9_card : Nat.card E9 = 9 := by
  rw [Nat.card_prod, goldenUnits_card, Nat.card_zpowers, blockCycle_order]

private theorem E9_cube (x : E9) : x ^ 3 = 1 := by
  apply Prod.ext
  · change x.1 ^ 3 = 1
    simpa only [goldenUnits_card] using pow_card_eq_one' (x := x.1)
  · have hcard : Nat.card (Subgroup.zpowers blockCycle) = 3 :=
      (Nat.card_zpowers _).trans blockCycle_order
    change x.2 ^ 3 = 1
    simpa only [hcard] using pow_card_eq_one' (x := x.2)

private def glueE9Hom : E9 →* icosianGlueMonomialStabilizer GoldenFour :=
  uniformMonomial.comp ((MonoidHom.id _).prodMap (Subgroup.zpowers blockCycle).subtype)

private theorem glueE9Hom_injective : Function.Injective glueE9Hom := by
  apply uniformMonomial_injective.comp
  intro a b h
  change (a.1, (a.2 : Equiv.Perm (Fin 3))) = (b.1, (b.2 : Equiv.Perm (Fin 3))) at h
  exact Prod.ext (congrArg (fun p : GoldenFourˣ × Equiv.Perm (Fin 3) => p.1) h)
    (Subtype.ext (congrArg Prod.snd h))

/-- The scalar group and a cyclic permutation of the blocks give the concrete order-nine witness. -/
theorem exists_glue_elementary_nine :
    ∃ D : Subgroup (icosianGlueMonomialStabilizer GoldenFour),
      IsElementaryAbelian 3 D ∧ Nat.card D = 9 := by
  refine ⟨glueE9Hom.range, ?_, ?_⟩
  · refine { toIsMulCommutative := inferInstance
             exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
    intro x
    obtain ⟨a, rfl⟩ := glueE9Hom.rangeRestrict_surjective x
    rw [← map_pow, E9_cube, map_one]
  · exact (Nat.card_congr (MonoidHom.ofInjective glueE9Hom_injective).toEquiv).symm.trans E9_card

/-- The order-nine witness lifts through monomial reduction and survives the central signs. -/
theorem exists_icosian_projective_elementary_nine :
    ∃ E : Subgroup IcosianProjectiveModel,
      IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨D, hD, hDc⟩ := exists_glue_elementary_nine
  let := hD
  obtain ⟨A, hA, _, hAc⟩ :=
    Subgroup.exists_elementaryAbelian_map_eq_of_surjective_coprime
      icosianLiftedMonomialProjection icosianLiftedMonomialProjection_surjective
      (p := 3) (by rw [icosianLiftedMonomialProjection_kernel_card]; decide) D
  let := hA
  let B := A.map icosianMonomialToHermitian
  let : IsElementaryAbelian 3 B := IsElementaryAbelian.map icosianMonomialToHermitian
  have hBc : Nat.card B = 9 := by
    rw [Subgroup.card_map_of_injective icosianMonomialToHermitian_injective, hAc, hDc]
  have hi : Function.Injective (icosianProjectiveProjection.comp B.subtype) :=
    Subgroup.injective_comp_subtype_of_coprime_ker icosianProjectiveProjection
      (p := 3) (by
        change Nat.Coprime 3 (Nat.card (QuotientGroup.mk' icosianCentralSigns).ker)
        rw [QuotientGroup.ker_mk', icosianCentralSigns_card]
        decide) B (IsElementaryAbelian.isPGroup 3 B)
  let e : B ≃* B.map icosianProjectiveProjection :=
    MulEquiv.ofBijective (icosianProjectiveProjection.subgroupMap B)
      ⟨fun x y h => hi (congrArg Subtype.val h),
        icosianProjectiveProjection.subgroupMap_surjective B⟩
  exact ⟨B.map icosianProjectiveProjection, IsElementaryAbelian.map _,
    (Nat.card_congr e.toEquiv).symm.trans hBc⟩

private def alternatingCycle : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
private theorem alternatingCycle_cube : alternatingCycle ^ 3 = 1 := by decide
private theorem alternatingCycle_ne_one : alternatingCycle ≠ 1 := by decide
private theorem alternatingCycle_order : orderOf alternatingCycle = 3 :=
  orderOf_eq_prime alternatingCycle_cube alternatingCycle_ne_one

/-- The literal lattice Conway quotient contains an elementary abelian group of order 27. -/
theorem leechCentralQuotient_three_le_primeRank :
    3 ≤ primeRank 3 LeechCentralQuotient := by
  obtain ⟨E, hE, hEc⟩ := exists_icosian_projective_elementary_nine
  let := hE
  let C := Subgroup.zpowers alternatingCycle
  let : IsElementaryAbelian 3 C :=
    IsElementaryAbelian.zpowers_of_pow_eq_one alternatingCycle_cube
  let : CommGroup E := IsMulCommutative.instCommGroup
  let : CommGroup C := IsMulCommutative.instCommGroup
  let f : C × E →* LeechCentralQuotient :=
    icosianAlternatingProjectiveToCo1.comp (C.subtype.prodMap E.subtype)
  have hf : Function.Injective f := by
    apply icosianAlternatingProjectiveToCo1_injective.comp
    intro x y h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
      (Subtype.ext (congrArg Prod.snd h))
  apply primeRank_ge_of_elementary_embedding (f := f) ?_ ?_ hf
  · intro x
    exact Prod.ext
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 3 C) x.1)
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 3 E) x.2)
  · rw [Nat.card_prod, hEc, Nat.card_zpowers, alternatingCycle_order]
    norm_num

end Sporadic.Monster.Construction.QuasithinObstruction
