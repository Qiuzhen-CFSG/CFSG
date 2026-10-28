module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.Torus

/-!
# Residue diagonals for the higher E6 central characters

For the six marked simple roots, take the integral coroot weight with
coefficients `(1,2,0,0,1,2)`. Its negative is the exponent on the actual
Chevalley basis: the torus convention is inverse root-character evaluation.
Reduce that exponent to `{-1,0,1}` modulo three and use it to define an
ambient diagonal `D(u)` for every unit `u`.

Integral homogeneity shows that each six-node divided power preserves these
residue classes. Thus `D(u)` commutes with every evaluated six-node word,
without a cubic assumption. This is an ambient centralizer statement; it
supplies no assertion that `D(u)` belongs to the word image.

When `u³ = 1`, reducing the exponent does not change its power. Consequently
`D(u)` equals the actual six-coroot matrix with parameters
`(u,u²,1,1,u,u²)`. In E7 and E8 the seventh simple-root entry is `u⁻¹`,
so the parameter is unique. The sibling `TorusPlacement` module applies
this bridge once scalar form and the word-image cubic constraint are proved.

Sources: GLS3 §§1.12.5–6 and 2.6.2, and Aschbacher–Smith A.2.17,
printed p.39. All calculations here are valid in characteristic three.
-/

@[expose] public section

open RootPairing.IntegralGeckConstruction
open Theory.AlgebraicGroup.StandardRootSystem
open scoped BigOperators
noncomputable section
namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement
attribute [local instance] Classical.decEq

/-- The representative of an integer modulo three in `{-1,0,1}`. -/
def balancedResidue (n : ℤ) : ℤ := (n + 1) % 3 - 1

/-- The balanced representative has the original residue modulo three. -/
theorem balancedResidue_mod (n : ℤ) : balancedResidue n % 3 = n % 3 := by
  unfold balancedResidue
  omega

/-- Cubic roots of unity do not distinguish balanced and original exponents. -/
theorem zpow_balancedResidue {G : Type*} [Group G] (u : G) (hu : u ^ 3 = 1) (n : ℤ) :
    u ^ balancedResidue n = u ^ n := by
  calc
    u ^ balancedResidue n = u ^ (balancedResidue n % (3 : ℤ)) := by
      simpa using zpow_eq_zpow_emod' (balancedResidue n) hu
    _ = u ^ (n % 3) := congrArg (fun k : ℤ => u ^ k) (balancedResidue_mod n)
    _ = u ^ n := by simpa using (zpow_eq_zpow_emod' n hu).symm

section Generic
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]
  (F : Type*) [Field F]

/-- The negative central coroot weight, matching the matrix torus convention. -/
def centralExponent (j : Fin 6 → b.support) (a : b.support ⊕ ι) : ℤ :=
  -(chevalleyBasisWeight (P := P) a (j 0) +
    2 * chevalleyBasisWeight (P := P) a (j 1) +
    chevalleyBasisWeight (P := P) a (j 4) +
    2 * chevalleyBasisWeight (P := P) a (j 5))

/-- The ambient scalar diagonal on the three central-weight classes. -/
def residueDiagonal (j : Fin 6 → b.support) (u : Fˣ) :
    (Matrix (b.support ⊕ ι) (b.support ⊕ ι) F)ˣ where
  val := Matrix.diagonal fun a => (u ^ balancedResidue (centralExponent j a) : Fˣ)
  inv := Matrix.diagonal fun a => ((u ^ balancedResidue (centralExponent j a))⁻¹ : Fˣ)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    ext a c
    simp [Matrix.one_apply, Matrix.diagonal_apply, zpow_ne_zero _ (Units.ne_zero u)]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    ext a c
    simp [Matrix.one_apply, Matrix.diagonal_apply, zpow_ne_zero _ (Units.ne_zero u)]

/-- The actual central coroot parameter acts with the specified integral exponent. -/
theorem centralParameter_basisUnit (j : Fin 6 → b.support) (u : Fˣ)
    (a : b.support ⊕ ι) :
    chevalleyBasisTorusUnit (P := P) (centralParameter F j u) a =
      u ^ centralExponent j a := by
  cases a with
  | inl i => simp [chevalleyBasisTorusUnit, chevalleyBasisWeight, centralExponent]
  | inr r =>
    simp only [chevalleyBasisTorusUnit_root, centralParameter,
      integralChevalleyRootScale_mul, integralChevalleyRootScale_simpleCorootParameter,
      centralExponent, chevalleyBasisWeight]
    rw [← zpow_natCast u 2]
    simp only [← zpow_mul, ← zpow_add, zpow_neg, Nat.cast_ofNat]

/-- At a cubic parameter the residue diagonal is the literal central coroot matrix. -/
theorem residueDiagonal_eq_centralMatrix (j : Fin 6 → b.support) (u : Fˣ)
    (hu : u ^ 3 = 1) : residueDiagonal F j u = centralMatrix F j u := by
  apply Units.ext
  change Matrix.diagonal _ = Matrix.diagonal _
  congr 1
  funext a
  rw [centralParameter_basisUnit, zpow_balancedResidue u hu]

/-- The six actual coroot parameters witnessing torus placement of a cubic diagonal. -/
theorem residueDiagonal_eq_sixCorootMatrix (j : Fin 6 → b.support) (u : Fˣ)
    (hu : u ^ 3 = 1) :
    residueDiagonal F j u = sixCorootMatrix F j ![u,u^2,1,1,u,u^2] := by
  rw [residueDiagonal_eq_centralMatrix F j u hu]
  have h (i : b.support) : integralChevalleySimpleCorootParameter i (1 : Fˣ) = 1 := by
    funext k
    simp [integralChevalleySimpleCorootParameter]
  change integralChevalleyTorusElement (P := P) _ = integralChevalleyTorusElement (P := P) _
  apply congrArg (integralChevalleyTorusElement (P := P))
  simp [sixCorootParameter, Fin.prod_univ_succ, h, centralParameter, mul_assoc]

/-- Integers differing by a multiple of three have the same balanced representative. -/
theorem balancedResidue_eq_of_dvd_sub {a c : ℤ} (h : 3 ∣ a - c) :
    balancedResidue a = balancedResidue c := by
  obtain ⟨k, hk⟩ := h
  unfold balancedResidue
  omega

omit [CharZero R] [P.IsReduced] in
/-- A matrix homogeneous of central weight divisible by three commutes with the diagonal. -/
theorem residueDiagonal_commute_homogeneous (j : Fin 6 → b.support) (u : Fˣ)
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) (d : ι → ℤ)
    (hA : IsChevalleyHomogeneous (P := P) A d)
    (hd : 3 ∣ d (j 0) + 2 * d (j 1) + d (j 4) + 2 * d (j 5)) :
    Commute (residueDiagonal F j u).val (A.map (Int.castRingHom F)) := by
  change _ * _ = _ * _
  ext row col
  simp only [residueDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply]
  by_cases h : A row col = 0
  · simp [h]
  have he : centralExponent j row - centralExponent j col =
      -(d (j 0) + 2 * d (j 1) + d (j 4) + 2 * d (j 5)) := by
    have h0 := hA row col h (j 0)
    have h1 := hA row col h (j 1)
    have h4 := hA row col h (j 4)
    have h5 := hA row col h (j 5)
    unfold centralExponent
    linarith
  have hb : balancedResidue (centralExponent j row) =
      balancedResidue (centralExponent j col) :=
    balancedResidue_eq_of_dvd_sub (he ▸ dvd_neg.mpr hd)
  rw [hb, mul_comm]

omit [CharZero R] [P.IsReduced] [Fintype ι] [DecidableEq ι] in
private theorem e6_weight_dvd (j : Fin 6 → b.support)
    (hj : ∀ i k, P.pairingIn ℤ (j i) (j k) = typeE6CartanMatrix i k)
    (i : Fin 6) (n : ℤ) :
    3 ∣ n * P.pairingIn ℤ (j i) (j 0) +
      2 * (n * P.pairingIn ℤ (j i) (j 1)) +
      n * P.pairingIn ℤ (j i) (j 4) +
      2 * (n * P.pairingIn ℤ (j i) (j 5)) := by
  simp only [hj]
  fin_cases i <;> simp [typeE6CartanMatrix] <;> omega

/-- Every signed simple curve commutes with every residue diagonal. -/
theorem residueDiagonal_commute_simple (j : Fin 6 → b.support)
    (hj : ∀ i k, P.pairingIn ℤ (j i) (j k) = typeE6CartanMatrix i k)
    (u : Fˣ) (s : Bool) (i : Fin 6) (t : F) :
    Commute (residueDiagonal F j u)
      ((RootPairing.SimpleGeckGroup.simpleFamily (b := b)).unit (s, j i) t) := by
  let D := RootPairing.SimpleGeckGroup.simpleFamily (b := b)
  have hc (n : ℕ) : Commute (residueDiagonal F j u).val
      (D.coefficient (s, j i) n) := by
    cases s
    · exact residueDiagonal_commute_homogeneous F j u _ _
        (fDividedPower_isChevalleyHomogeneous (j i) n)
        (e6_weight_dvd j hj i (-n))
    · exact residueDiagonal_commute_homogeneous F j u _ _
        (eDividedPower_isChevalleyHomogeneous (j i) n)
        (e6_weight_dvd j hj i n)
  apply Units.ext
  change (residueDiagonal F j u).val * D.curve (s, j i) t =
    D.curve (s, j i) t * (residueDiagonal F j u).val
  simp only [RootPairing.SimpleGeckGroup.IntegralCubicFamily.curve,
    mul_add, add_mul, mul_one, one_mul, Matrix.mul_smul, Matrix.smul_mul,
    (hc 1).eq, (hc 2).eq, (hc 3).eq]

/-- Commutation with the generators extends to their literal free-word evaluation. -/
theorem residueDiagonal_commute_eval (j : Fin 6 → b.support)
    (hj : ∀ i k, P.pairingIn ℤ (j i) (j k) = typeE6CartanMatrix i k)
    (v : SixNodeWord F →* (Matrix (b.support ⊕ ι) (b.support ⊕ ι) F)ˣ)
    (hv : ∀ s i t, v (FreeGroup.of (s, i, t)) =
      (RootPairing.SimpleGeckGroup.simpleFamily (b := b)).unit (s, j i) t)
    (u : Fˣ) (w : SixNodeWord F) : Commute (residueDiagonal F j u) (v w) := by
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of x =>
    obtain ⟨s,i,t⟩ := x
    rw [hv]
    exact residueDiagonal_commute_simple F j hj u s i t
  | inv_of x hx => simpa using hx.inv_right
  | mul x y hx hy => simpa using hx.mul_right hy

end Generic

local instance : Fintype typeE7Roots := Fintype.ofFinite _
local instance : Fintype typeE8Roots := Fintype.ofFinite _
variable (F : Type*) [Field F]

private theorem e7_cartan (i k : Fin 6) :
    typeE7RootPairing.pairingIn ℤ (e7Node i) (e7Node k) = typeE6CartanMatrix i k :=
  (typeE7RootPairing_base_cartan_apply _ _).trans (e7_cartan_restrict i k)

private theorem e8_cartan (i k : Fin 6) :
    typeE8RootPairing.pairingIn ℤ (e8Node i) (e8Node k) = typeE6CartanMatrix i k :=
  (typeE8RootPairing_base_cartan_apply _ _).trans (e8_cartan_restrict i k)

/-- Every residue diagonal centralizes the actual E7 six-node word image. -/
theorem residueDiagonal_e7Six_commute (u : Fˣ) (w : SixNodeWord F) :
    Commute (residueDiagonal F e7Node u) (e7Six F w).val := by
  apply residueDiagonal_commute_eval F e7Node e7_cartan
    ((ExceptionalSplit.rootGenerated _ _ F).subtype.comp (e7Six F))
  intro s i t
  simp [e7Simple, e7Node]

/-- Every residue diagonal centralizes the actual E8 six-node word image. -/
theorem residueDiagonal_e8Six_commute (u : Fˣ) (w : SixNodeWord F) :
    Commute (residueDiagonal F e8Node u) (e8Six F w).val := by
  apply residueDiagonal_commute_eval F e8Node e8_cartan
    ((ExceptionalSplit.rootGenerated _ _ F).subtype.comp (e8Six F))
  intro s i t
  simp [e8Simple, e8Node]

/-- The seventh E7 simple-root entry recovers the inverse scalar parameter. -/
theorem residueDiagonal_e7_extra (u : Fˣ) :
    (residueDiagonal F e7Node u).val
      (Sum.inr (typeE7RootPairing_baseEquiv 6))
      (Sum.inr (typeE7RootPairing_baseEquiv 6)) = (u⁻¹ : Fˣ) := by
  have h (k : Fin 6) : typeE7RootPairing.pairingIn ℤ
      (typeE7RootPairing_baseEquiv 6) (e7Node k) =
      typeE7CartanMatrix 6 (k.castLE (by decide)) :=
    typeE7RootPairing_base_cartan_apply 6 (k.castLE (by decide))
  simp only [residueDiagonal, Matrix.diagonal_apply_eq, centralExponent,
    chevalleyBasisWeight, h]
  norm_num [typeE7CartanMatrix, balancedResidue, Fin.ext_iff]

/-- The seventh E8 simple-root entry recovers the inverse scalar parameter. -/
theorem residueDiagonal_e8_extra (u : Fˣ) :
    (residueDiagonal F e8Node u).val
      (Sum.inr (typeE8RootPairing_baseEquiv 6))
      (Sum.inr (typeE8RootPairing_baseEquiv 6)) = (u⁻¹ : Fˣ) := by
  have h (k : Fin 6) : typeE8RootPairing.pairingIn ℤ
      (typeE8RootPairing_baseEquiv 6) (e8Node k) =
      typeE8CartanMatrix 6 (k.castLE (by decide)) :=
    typeE8RootPairing_base_cartan_apply 6 (k.castLE (by decide))
  simp only [residueDiagonal, Matrix.diagonal_apply_eq, centralExponent,
    chevalleyBasisWeight, h]
  norm_num [typeE8CartanMatrix, balancedResidue, Fin.ext_iff]

/-- The E7 residue-diagonal parameter is unique. -/
theorem residueDiagonal_e7_injective : Function.Injective (residueDiagonal F e7Node) := by
  intro u v h
  have he := congrArg (fun g => g.val
    (Sum.inr (typeE7RootPairing_baseEquiv 6))
    (Sum.inr (typeE7RootPairing_baseEquiv 6))) h
  simpa only [residueDiagonal_e7_extra, Units.val_inv_eq_inv_val, inv_inj,
    Units.val_inj] using he

/-- The E8 residue-diagonal parameter is unique. -/
theorem residueDiagonal_e8_injective : Function.Injective (residueDiagonal F e8Node) := by
  intro u v h
  have he := congrArg (fun g => g.val
    (Sum.inr (typeE8RootPairing_baseEquiv 6))
    (Sum.inr (typeE8RootPairing_baseEquiv 6))) h
  simpa only [residueDiagonal_e8_extra, Units.val_inv_eq_inv_val, inv_inj,
    Units.val_inj] using he

end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement
