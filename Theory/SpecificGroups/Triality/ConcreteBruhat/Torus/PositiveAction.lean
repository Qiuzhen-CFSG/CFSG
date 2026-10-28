module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus.DiagonalData
public import Theory.SpecificGroups.Triality.ConcreteBruhat.LatticeInstances
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates

/-!
# Coroot action on the positive triality subgroup

Assuming the concrete coroot diagonal formula, the integral divided-power
weight support gives the action on all twelve positive Geck curves. In each
matrix entry, the weight difference is the divided-power degree times the
root-coroot pairing. Thus diagonal multiplication rescales the curve parameter.
The four simple curves generate the existing positive subgroup, which is
therefore normalized by the existing split torus.

Every torus matrix is diagonal, as follows by containment in the image of the
diagonal homomorphism on units. In characteristic two a diagonal matrix of
two-power order is identity, proving disjointness from any positive two-group.
The binary specialization supplies that two-group property from the proved
positive-root normal form, including exponent one.

Source: GLS3 1.12.1(g), 2.3.4(c), 2.3.8(a), and §2.4
(`refs/KGroup/GLS3/Chapter1.tex` and `refs/KGroup/GLS3/chapter2.tex`).
The source uses right conjugation and h(t) = n(1)⁻¹n(t); the code uses
h(t) = n(t)n(-1), so its equivalent formula is h(t)x(s)h(t)⁻¹.
The diagonal identity remains an explicit input for the parent torus assembly.
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.ConcreteBruhat
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Parabolics Parabolics.RankOneMatrices TorusCoordinates
open PositiveCoordinates.Injectivity
attribute [local instance] instDecidableEqLatticeIndex

private lemma weight_cast (i : Fin 4) (k : LatticeIndex) :
    ((corootWeight i k : ℤ) : ℝ) =
      (typeDRootPairing 2).coroot' (typeDSimpleRootIndex 2 i)
        (rootWeight (b := typeDRootPairing_base 2) k) := by
  rcases k with k | k
  · simp [corootWeight, rootWeight]
  · change ((typeDRootPairing 2).pairingIn ℤ k (typeDSimpleRootIndex 2 i) : ℝ) =
      (typeDRootPairing 2).coroot' (typeDSimpleRootIndex 2 i) ((typeDRootPairing 2).root k)
    rw [RootPairing.root_coroot'_eq_pairing]
    exact (typeDRootPairing 2).algebraMap_pairingIn ℤ k (typeDSimpleRootIndex 2 i)

private lemma weight_support (i : Fin 4) (j : Fin 12) (n : ℕ) (a b : LatticeIndex)
    (hab : rootDividedPower (b := typeDRootPairing_base 2)
      (PositiveCoordinates.rootIndex j) n a b ≠ 0) :
    corootWeight i a = n * (typeDRootPairing 2).pairingIn ℤ
      (PositiveCoordinates.rootIndex j) (typeDSimpleRootIndex 2 i) + corootWeight i b := by
  have h := congrArg ((typeDRootPairing 2).coroot' (typeDSimpleRootIndex 2 i))
    (rootDividedPower_homogeneous _ (PositiveCoordinates.rootIndex_positive j) n a b hab)
  rw [map_add, map_nsmul, ← weight_cast, ← weight_cast,
    RootPairing.root_coroot'_eq_pairing,
    ← (typeDRootPairing 2).algebraMap_pairingIn ℤ] at h
  simp only [nsmul_eq_mul, eq_intCast] at h
  exact_mod_cast h

private lemma diagonal_term (P : Parameters) (i : Fin 4) (t : (ExtensionField P)ˣ)
    (j : Fin 12) (n : ℕ) (s : ExtensionField P) :
    corootDiagonal P i t *
      (s ^ n • specializeMatrix (rootDividedPower (b := typeDRootPairing_base 2)
        (PositiveCoordinates.rootIndex j) n)) =
      ((t.val ^ ((typeDRootPairing 2).pairingIn ℤ
        (PositiveCoordinates.rootIndex j) (typeDSimpleRootIndex 2 i)) * s) ^ n •
        specializeMatrix (rootDividedPower (b := typeDRootPairing_base 2)
          (PositiveCoordinates.rootIndex j) n)) * corootDiagonal P i t := by
  ext a b
  simp only [corootDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.smul_apply, smul_eq_mul, specializeMatrix, Matrix.map_apply]
  by_cases h : rootDividedPower (b := typeDRootPairing_base 2)
      (PositiveCoordinates.rootIndex j) n a b = 0
  · simp [h]
  · rw [weight_support i j n a b h, zpow_add₀ t.ne_zero,
      mul_comm (n : ℤ), zpow_mul, zpow_natCast, mul_pow]
    ring

private lemma diagonal_curve (P : Parameters) (i : Fin 4) (t : (ExtensionField P)ˣ)
    (j : Fin 12) (s : ExtensionField P) :
    corootDiagonal P i t * (PositiveCoordinates.curve P j s).val.val =
      (PositiveCoordinates.curve P j (t.val ^ ((typeDRootPairing 2).pairingIn ℤ
        (PositiveCoordinates.rootIndex j) (typeDSimpleRootIndex 2 i)) * s)).val.val *
          corootDiagonal P i t := by
  change corootDiagonal P i t * (1 + s • _ + s ^ 2 • _ + s ^ 3 • _) =
    (1 + _ • _ + _ ^ 2 • _ + _ ^ 3 • _) * corootDiagonal P i t
  simp only [mul_add, add_mul, mul_one, one_mul]
  dsimp only [integralChevalleyRootOperators]
  rw [diagonal_term P i t j 2, diagonal_term P i t j 3]
  have h1 := diagonal_term P i t j 1 s
  simp only [pow_one] at h1
  rw [h1]

/-- A coroot word scales the parameter of each actual positive integral Geck curve
by its root-coroot pairing. The input is precisely the matrix diagonal formula. -/
theorem torusWord_curve_conjugate_of_diagonal (P : Parameters)
    (hdiag : ∀ i t, (Parabolics.torusWord P i t).val.val = corootDiagonal P i t)
    (i : Fin 4) (t : (ExtensionField P)ˣ) (j : Fin 12) (s : ExtensionField P) :
    Parabolics.torusWord P i t * PositiveCoordinates.curve P j s *
      (Parabolics.torusWord P i t)⁻¹ =
        PositiveCoordinates.curve P j (t.val ^ ((typeDRootPairing 2).pairingIn ℤ
          (PositiveCoordinates.rootIndex j) (typeDSimpleRootIndex 2 i)) * s) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  apply Units.ext
  change (Parabolics.torusWord P i t).val.val * _ = _ * (Parabolics.torusWord P i t).val.val
  rw [hdiag]
  exact diagonal_curve P i t j s


/-- The same action on the original pinned positive simple generators. -/
theorem torusWord_positiveRoot_conjugate_of_diagonal (P : Parameters)
    (hdiag : ∀ i t, (torusWord P i t).val.val = corootDiagonal P i t)
    (i : Fin 4) (t : (ExtensionField P)ˣ) (j : Fin 4) (s : ExtensionField P) :
    torusWord P i t * positiveRoot P j s * (torusWord P i t)⁻¹ =
      positiveRoot P j (t.val ^ ((typeDRootPairing 2).pairingIn ℤ
        (typeDSimpleRootIndex 2 j) (typeDSimpleRootIndex 2 i)) * s) := by
  simpa only [PositiveCoordinates.curve_simple, PositiveCoordinates.rootIndex_simple] using
    torusWord_curve_conjugate_of_diagonal P hdiag i t (PositiveCoordinates.simplePosition j) s

/-- The subgroup generated by the original coroot words normalizes the original
subgroup generated by the positive simple root curves. -/
theorem splitTorus_le_normalizer_positiveSubgroup_of_diagonal (P : Parameters)
    (hdiag : ∀ i t, (torusWord P i t).val.val = corootDiagonal P i t) :
    splitTorus P ≤ Subgroup.normalizer (positiveSubgroup P) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, t, rfl⟩
  apply Subgroup.normalizer_le_normalizer_closure
  apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
  apply Set.Subset.antisymm
  · rintro _ ⟨g, ⟨j, s, rfl⟩, rfl⟩
    exact ⟨j, _, torusWord_positiveRoot_conjugate_of_diagonal P hdiag i t j s⟩
  · rintro _ ⟨j, s, rfl⟩
    let c := t.val ^ ((typeDRootPairing 2).pairingIn ℤ
      (typeDSimpleRootIndex 2 j) (typeDSimpleRootIndex 2 i))
    refine ⟨positiveRoot P j (c⁻¹ * s), ⟨j, _, rfl⟩, ?_⟩
    change torusWord P i t * _ * (torusWord P i t)⁻¹ = _
    rw [torusWord_positiveRoot_conjugate_of_diagonal P hdiag]
    change positiveRoot P j (c * (c⁻¹ * s)) = positiveRoot P j s
    rw [← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ t.ne_zero), one_mul]

private lemma splitTorus_diagonal (P : Parameters)
    (hdiag : ∀ i t, (torusWord P i t).val.val = corootDiagonal P i t)
    {g : SplitGroup P} (hg : g ∈ splitTorus P) :
    ∃ d : LatticeIndex → ExtensionField P, g.val.val = Matrix.diagonal d := by
  let f : (LatticeIndex → ExtensionField P)ˣ →*
      (Matrix LatticeIndex LatticeIndex (ExtensionField P))ˣ :=
    Units.map (Matrix.diagonalRingHom LatticeIndex (ExtensionField P)).toMonoidHom
  have hle : splitTorus P ≤ f.range.comap (Subgroup.subtype _) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, t, rfl⟩
    let d : (LatticeIndex → ExtensionField P)ˣ :=
      { val := fun r => t.val ^ corootWeight i r
        inv := fun r => (t.val ^ corootWeight i r)⁻¹
        val_inv := funext fun r => mul_inv_cancel₀ (zpow_ne_zero _ t.ne_zero)
        inv_val := funext fun r => inv_mul_cancel₀ (zpow_ne_zero _ t.ne_zero) }
    refine ⟨d, ?_⟩
    apply Units.ext
    exact (hdiag i t).symm
  obtain ⟨d, hd⟩ := hle hg
  exact ⟨d.val, congrArg Units.val hd.symm⟩

/-- A positive two-element which is diagonal is identity: its diagonal entries
have two-power order in a field of characteristic two. No torus order is used. -/
theorem disjoint_positiveSubgroup_splitTorus_of_diagonal (P : Parameters) (hp : P.prime = 2)
    (hdiag : ∀ i t, (torusWord P i t).val.val = corootDiagonal P i t)
    (hU : IsPGroup 2 (positiveSubgroup P)) :
    Disjoint (positiveSubgroup P) (splitTorus P) := by
  let := rankOneExtensionCharTwo P hp
  apply Subgroup.disjoint_def.mpr
  intro g hgU hgT
  obtain ⟨d, hd⟩ := splitTorus_diagonal P hdiag hgT
  obtain ⟨k, hk⟩ := hU ⟨g, hgU⟩
  have hpow : g.val.val ^ (2 ^ k) = 1 :=
    congrArg (fun x : positiveSubgroup P => x.val.val.val) hk
  rw [hd, Matrix.diagonal_pow] at hpow
  have hentry (r : LatticeIndex) : d r ^ (2 ^ k) = 1 := by
    simpa using congrFun (congrFun hpow r) r
  have hone (r : LatticeIndex) : d r = 1 := by
    have inj (m : ℕ) : Function.Injective (fun x : ExtensionField P => x ^ (2 ^ m)) := by
      induction m with
      | zero =>
          intro x y h
          simpa only [pow_zero, pow_one] using h
      | succ m ih =>
          intro x y h
          apply ih
          apply CharTwo.sq_injective
          simpa only [pow_succ 2 m, pow_mul] using h
    apply inj k
    simpa using hentry r
  apply Subtype.ext
  apply Units.ext
  change g.val.val = 1
  rw [hd]
  rw [show d = 1 from funext hone]
  exact Matrix.diagonal_one

/-- Binary parameters discharge the positive two-group input for every n > 0,
including n = 1. Only the coroot diagonal formula remains conditional. -/
theorem disjoint_positiveSubgroup_splitTorus_binary_of_diagonal (n : ℕ) (hn : 0 < n)
    (hdiag : ∀ i t, (torusWord (binaryParameters n hn) i t).val.val =
      corootDiagonal (binaryParameters n hn) i t) :
    Disjoint (positiveSubgroup (binaryParameters n hn)) (splitTorus (binaryParameters n hn)) :=
  disjoint_positiveSubgroup_splitTorus_of_diagonal _ rfl hdiag
    (PositiveCoordinates.isPGroup_positiveSubgroup_binary n hn)

end Triality.Standard.ConcreteBruhat
