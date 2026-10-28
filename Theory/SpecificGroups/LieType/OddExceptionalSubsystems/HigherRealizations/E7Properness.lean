module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations

/-!
# Properness of the folded E7 subgroup after central projection

In Geck's Cartan basis, the vector with coordinates
`(2, -4, 6, -3, -5, 4, -3)` is fixed by both signs of the first six
simple curves, hence by every marked folded generator. The Tits word on
nodes `4, 5, 6` sends it to the Cartan vector
`(2, -4, 6, -3, -3, 2, -1)`. The positive node-2 curve at parameter one
moves this new vector by twice its root basis vector.

If the folded subgroup surjected onto the ambient central quotient, every
ambient element would be a product of a central element and an element of
the folded subgroup. Its translate of the original vector would then still
be fixed by the folded subgroup, contradicting the displayed calculation.
Only `2 ≠ 0` is needed: the argument includes GF(3), uses the literal matrix
curves and central projection, and does not require a folding identification.

The final adapter discharges precisely the properness premise of
`e7ProperEmbeddingOfWordKernels`; the word comparison and source-center
premise remain with that construction's assembly owner.

Sources: Aschbacher--Smith A.2.17, printed p.39 of `refs/quasithin.pdf`;
GLS3 §2.6.2--3, `refs/KGroup/GLS3/chapter2.tex` (common-lattice subsystems).
-/

@[expose] public section

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open scoped Matrix

noncomputable section
namespace TwistedE6.FoldedSubsystem.HigherRealizations
attribute [local instance] Classical.decEq
local instance : Fintype typeE7Roots := Fintype.ofFinite _
private abbrev base := typeE7RootPairing_base
private abbrev node := typeE7RootPairing_baseEquiv
private abbrev Index := base.support ⊕ typeE7Roots
private def cartan (c : Fin 7 → ℤ) : Index → ℤ := ∑ j, c j • u (node j)
private def coeff : Fin 7 → ℤ := ![2, -4, 6, -3, -5, 4, -3]
private def movedCoeff : Fin 7 → ℤ := ![2, -4, 6, -3, -3, 2, -1]
private def vector : Index → ℤ := cartan coeff
private def movedVector : Index → ℤ := cartan movedCoeff

private theorem pairing_coeff (i : Fin 6) :
    ∑ j : Fin 7, coeff j * |typeE7CartanMatrix (i.castLE (by decide)) j| = 0 := by
  fin_cases i <;> decide

private theorem eMatrix_cartan (i : Fin 7) (c : Fin 7 → ℤ) :
    eMatrix (node i) *ᵥ cartan c =
      (∑ j, c j * |typeE7CartanMatrix i j|) • v (b := base) (node i) := by
  simp only [cartan, Matrix.mulVec_sum, Matrix.mulVec_smul, eMatrix_mulVec_u,
    typeE7RootPairing_base_cartan_apply, smul_smul, Finset.sum_smul]

private theorem fMatrix_cartan (i : Fin 7) (c : Fin 7 → ℤ) :
    fMatrix (node i) *ᵥ cartan c =
      (∑ j, c j * |typeE7CartanMatrix i j|) •
        v (b := base) (typeE7RootPairing.reflectionPerm (node i) (node i)) := by
  simp only [cartan, Matrix.mulVec_sum, Matrix.mulVec_smul, fMatrix_mulVec_u,
    typeE7RootPairing_base_cartan_apply, smul_smul, Finset.sum_smul]

private theorem dividedPower_vector (s : Bool) (i : Fin 6) (n : ℕ) (hn : 0 < n) :
    (simpleFamily (b := base)).dividedPower (s, node (i.castLE (by decide))) n *ᵥ vector = 0 := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero =>
      cases s
      · change fDividedPower _ 1 *ᵥ cartan coeff = 0
        rw [fDividedPower_one]
        rw [fMatrix_cartan, pairing_coeff, zero_smul]
      · change eMatrix _ *ᵥ cartan coeff = 0
        rw [eMatrix_cartan, pairing_coeff, zero_smul]
    | succ n =>
      cases s <;>
        simp only [simpleFamily, vector, cartan, Matrix.mulVec_sum, Matrix.mulVec_smul,
          eDividedPower_add_two_mulVec_u, fDividedPower_add_two_mulVec_u,
          smul_zero, Finset.sum_const_zero]

private theorem tits_cartan (i : Fin 7) (c : Fin 7 → ℤ) :
    titsLift (node i) *ᵥ cartan c = cartan c -
      (∑ j, c j * |typeE7CartanMatrix i j|) • u (node i) := by
  simp only [cartan, Matrix.mulVec_sum, Matrix.mulVec_smul, titsLift_mulVec_u,
    typeE7RootPairing_base_cartan_apply, smul_sub, smul_smul, Finset.sum_sub_distrib,
    Finset.sum_smul]

private theorem tits_vector :
    titsWord [node 4, node 5, node 6] *ᵥ vector = movedVector := by
  simp only [titsWord, mul_one, ← Matrix.mulVec_mulVec]
  simp only [vector, tits_cartan, Matrix.mulVec_sub, Matrix.mulVec_smul,
    titsLift_mulVec_u]
  have h4 : (∑ j, coeff j * |typeE7CartanMatrix 4 j|) = 0 := by decide
  have h5 : (∑ j, coeff j * |typeE7CartanMatrix 5 j|) = 0 := by decide
  have h6 : (∑ j, coeff j * |typeE7CartanMatrix 6 j|) = -2 := by decide
  rw [h4, h5, h6]
  simp only [typeE7RootPairing_base_cartan_apply]
  norm_num only [show typeE7CartanMatrix 4 5 = -1 from rfl,
    show typeE7CartanMatrix 4 6 = 0 from rfl,
    show typeE7CartanMatrix 5 6 = -1 from rfl,
    abs_neg, abs_one, abs_zero, zero_smul, one_smul, sub_zero]
  change
    (2 • u (node 0) + ((-4) • u (node 1) + (6 • u (node 2) + ((-3) • u (node 3) +
      ((-5) • u (node 4) + (4 • u (node 5) + ((-3) • u (node 6) + 0))))))) -
      (-2 : ℤ) • (u (node 6) - (u (node 5) - u (node 4))) =
    2 • u (node 0) + ((-4) • u (node 1) + (6 • u (node 2) + ((-3) • u (node 3) +
      ((-3) • u (node 4) + (2 • u (node 5) + ((-1) • u (node 6) + 0))))))
  module

private theorem eUnipotent_movedVector :
    eUnipotent (node 2) 1 *ᵥ movedVector = movedVector + 2 • v (b := base) (node 2) := by
  simp only [eUnipotent, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    eDividedPower_one, movedVector, eMatrix_cartan]
  have hz (n : ℕ) : eDividedPower (node 2) (n + 2) *ᵥ cartan movedCoeff = 0 := by
    simp only [cartan, Matrix.mulVec_sum, Matrix.mulVec_smul,
      eDividedPower_add_two_mulVec_u, smul_zero, Finset.sum_const_zero]
  rw [hz 0, hz 1]
  rw [show (∑ j, movedCoeff j * |typeE7CartanMatrix 2 j|) = 2 by decide]
  simp only [one_smul, one_pow, smul_zero, add_zero]
  rfl

private def castVector (F : Type*) [Field F] (w : Index → ℤ) : Index → F :=
  fun j => (w j : F)

private theorem cast_mulVec (F : Type*) [Field F] (A : Matrix Index Index ℤ)
    (w : Index → ℤ) :
    specializeMatrix (S := F) A *ᵥ castVector F w = castVector F (A *ᵥ w) := by
  ext j
  exact ((Int.castRingHom F).map_mulVec A w j).symm

private theorem signedSimple_vector (F : Type*) [Field F]
    (s : Bool) (i : Fin 6) (t : F) :
    (e7Simple F s (i.castLE (by decide)) t).val.val *ᵥ castVector F vector =
      castVector F vector := by
  have hz (n : ℕ) (hn : 0 < n) :
      (simpleFamily (b := base)).coefficient (S := F)
        (s, node (i.castLE (by decide))) n *ᵥ castVector F vector = 0 := by
    change specializeMatrix _ *ᵥ castVector F vector = 0
    rw [cast_mulVec, dividedPower_vector s i n hn]
    ext j
    exact Int.cast_zero
  rw [signedSimple_val]
  change (simpleFamily.curve (s, node (i.castLE (by decide))) t) *ᵥ _ = _
  simp only [IntegralCubicFamily.curve, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, hz 1 (by decide), hz 2 (by decide), hz 3 (by decide),
    smul_zero, add_zero]

private instance matrixAction (F : Type*) [Field F] :
    MulAction (ExceptionalSplit.e7Cover F) (Index → F) where
  smul g w := g.val.val *ᵥ w
  one_smul w := Matrix.one_mulVec w
  mul_smul g h w := (Matrix.mulVec_mulVec w g.val.val h.val.val).symm

private theorem folded_fixes (F : Type*) [Field F] :
    e7FoldedSubgroup F ≤ MulAction.stabilizer _ (castVector F vector) := by
  rw [e7FoldedSubgroup, Subgroup.closure_le]
  rintro _ ⟨⟨s, i, t⟩, rfl⟩
  have hs (j : Fin 7) (hj : j.val < 6) : e7Simple F s j t • castVector F vector =
      castVector F vector := signedSimple_vector F s ⟨j.val, hj⟩ t
  change e7FoldedSimple F s i t • castVector F vector = castVector F vector
  fin_cases i
  · exact hs 3 (by decide)
  · exact hs 2 (by decide)
  · change (e7Simple F s 1 t * e7Simple F s 4 t) • _ = _
    rw [mul_smul, hs 4 (by decide), hs 1 (by decide)]
  · change (e7Simple F s 0 t * e7Simple F s 5 t) • _ = _
    rw [mul_smul, hs 5 (by decide), hs 0 (by decide)]

private def movingWord (F : Type*) [Field F] : ExceptionalSplit.e7Cover F :=
  ⟨rootCurveTitsWord (S := F) [node 4, node 5, node 6], by
    change rootCurveTitsWord _ ∈ allRootCurveSubgroup base F
    rw [allRootCurveSubgroup_eq_simpleSubgroup]
    exact rootCurveTitsWord_mem _⟩

private theorem movingWord_vector (F : Type*) [Field F] :
    movingWord F • castVector F vector = castVector F movedVector := by
  change specializeMatrix (S := F) (titsWord _) *ᵥ castVector F vector = _
  rw [cast_mulVec, tits_vector]

private theorem positive_one_matrix (F : Type*) [Field F] :
    (e7Simple F true 2 1).val.val = specializeMatrix (S := F) (eUnipotent (node 2) 1) := by
  rw [signedSimple_val]
  change positiveMatrix _ _ = _
  ext j k
  simp [positiveMatrix_formula, specializeMatrix, eUnipotent, Matrix.one_apply]

private theorem moved_not_fixed (F : Type*) [Field F] (hodd : Odd (ringChar F)) :
    e7Simple F true 2 1 • (movingWord F • castVector F vector) ≠
      movingWord F • castVector F vector := by
  rw [movingWord_vector]
  change (e7Simple F true 2 1).val.val *ᵥ castVector F movedVector ≠ _
  rw [positive_one_matrix, cast_mulVec, eUnipotent_movedVector]
  intro he
  have hentry := congrFun he (Sum.inr (node 2))
  have htwo : (2 : F) = 0 := by
    simpa [castVector, movedVector, cartan, u, v, Pi.single_apply] using hentry
  have hd : ringChar F ∣ 2 := ringChar.dvd htwo
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact CharP.ringChar_ne_one (R := F) h
  · exact hodd.not_two_dvd_nat (by rw [h])

private theorem central_range_ne_top_of_moves
    {G V : Type*} [Group G] [MulAction G V] (H : Subgroup G) (w : V)
    (hfix : ∀ h ∈ H, h • w = w) (a : H) (g : G)
    (hmove : a.val • (g • w) ≠ g • w) :
    ((QuotientGroup.mk' (Subgroup.center G)).comp H.subtype).range ≠ ⊤ := by
  intro htop
  obtain ⟨k, hk⟩ := MonoidHom.range_eq_top.mp htop
    (QuotientGroup.mk' (Subgroup.center G) g)
  have hz : k.val / g ∈ Subgroup.center G := QuotientGroup.eq_iff_div_mem.mp hk
  have hcomm : Commute a.val ((k.val / g)⁻¹) :=
    (show Commute a.val (k.val / g) from Subgroup.mem_center_iff.mp hz a.val).inv_right
  have hg : g = (k.val / g)⁻¹ * k.val := by simp [div_eq_mul_inv, mul_assoc]
  apply hmove
  rw [hg, mul_smul, hfix k.val k.property, ← mul_smul, hcomm.eq,
    mul_smul, hfix a.val a.property]

/-- The marked folded subgroup has proper image under the literal E7 central
projection, over every field of odd characteristic (including GF(3)). -/
theorem e7FoldedProjection_proper (F : Type*) [Field F] (hodd : Odd (ringChar F)) :
    (e7FoldedProjection F).range ≠ ⊤ := by
  apply central_range_ne_top_of_moves (e7FoldedSubgroup F) (castVector F vector)
    (fun h hh => folded_fixes F hh)
    ⟨e7Simple F true 2 1, e7FoldedSimple_mem F true 1 1⟩ (movingWord F)
  exact moved_not_fixed F hodd


/-- A homomorphism with the marked folded generator formulas also has proper
image after the ambient central projection. -/
theorem e7_marked_projection_proper (F : Type*) [Field F] (hodd : Odd (ringChar F))
    (f : splitSubgroup F →* ExceptionalSplit.e7Cover F)
    (hf : ∀ s i t, f (f4Simple F s i t) = e7FoldedSimple F s i t) :
    ((ExceptionalSplit.projection typeE7RootPairing typeE7RootPairing_base F).comp f).range
      ≠ ⊤ := by
  intro htop
  apply e7FoldedProjection_proper F hodd
  rw [MonoidHom.range_comp, e7_range_eq F f hf] at htop
  simpa only [e7FoldedProjection, MonoidHom.range_comp, Subgroup.range_subtype] using htop

/-- The existing word-kernel constructor with its projected-properness premise
discharged. The independent word comparison and source-center premise are retained. -/
def e7ProperEmbeddingOfWordKernelsOdd (F : Type*) [Field F] (hodd : Odd (ringChar F))
    (hk : (sourceWord F).ker = (e7Word F).ker)
    (hc : Subgroup.center (splitSubgroup F) = ⊥) :
    ExceptionalSplit.ProperEmbedding (splitSubgroup F) (ExceptionalSplit.E7 F) :=
  e7ProperEmbeddingOfWordKernels F hk (e7FoldedProjection_proper F hodd) hc

end TwistedE6.FoldedSubsystem.HigherRealizations
