module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.Reduction
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CorootSquares

/-!
# The E6 central coroot word in the three literal representations

The central parameter has simple-coroot coordinates `(u,u²,1,1,u,u²)`.
We realize it by a word in the common six-node alphabet and compute its
matrix evaluation, cube, and pinned diagram transform. The parameter must
satisfy `u³ = 1`; no restriction on the characteristic is used.

These calculations identify the proposed central words. They do not assert
that every relation in the E6 adjoint representation is such a word in a
higher representation. That localization is a separate representation theorem.

Source: GLS3 §§1.12 and 2.5, particularly the E6 central diagram calculation
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open ExceptionalSplit.TheoremDRootNormalizer
namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters

attribute [local instance] Classical.decEq

variable (F : Type*) [Field F]

/-- The three-factor rank-one word. -/
def nWord (i : Fin 6) (t : F) : SixNodeWord F :=
  FreeGroup.of (true, i, t) * FreeGroup.of (false, i, -t⁻¹) *
    FreeGroup.of (true, i, t)

/-- The inverse input gives the positive torus parameter convention. -/
def hWord (i : Fin 6) (u : Fˣ) : SixNodeWord F :=
  nWord F i (↑u⁻¹) * nWord F i (-1)

/-- The central coroot word, with the two trivial coordinates omitted. -/
def centralWord (u : Fˣ) : SixNodeWord F :=
  hWord F 0 u * hWord F 1 (u ^ 2) * hWord F 4 u * hWord F 5 (u ^ 2)

@[simp] theorem diagramWord_nWord (i : Fin 6) (t : F) :
    diagramWord F (nWord F i t) = nWord F (typeE6DiagramPermutation i) t := by
  simp only [nWord, map_mul, diagramWord_of]

@[simp] theorem diagramWord_hWord (i : Fin 6) (u : Fˣ) :
    diagramWord F (hWord F i u) = hWord F (typeE6DiagramPermutation i) u := by
  simp only [hWord, map_mul, diagramWord_nWord]

section Matrices
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

/-- The ambient simple-coroot parameter of the central word. -/
def centralParameter (j : Fin 6 → b.support) (u : Fˣ) : b.support → Fˣ :=
  integralChevalleySimpleCorootParameter (j 0) u *
    integralChevalleySimpleCorootParameter (j 1) (u ^ 2) *
    integralChevalleySimpleCorootParameter (j 4) u *
    integralChevalleySimpleCorootParameter (j 5) (u ^ 2)

/-- The actual diagonal matrix, without an assumption about membership. -/
def centralMatrix (j : Fin 6 → b.support) (u : Fˣ) :
    (Matrix (b.support ⊕ ι) (b.support ⊕ ι) F)ˣ :=
  integralChevalleyTorusElement (P := P) (centralParameter F j u)

omit [CharZero R] [P.IsCrystallographic] [P.IsReduced] [Fintype ι] in
private theorem simpleParameter_cube (i : b.support) (u : Fˣ) (hu : u ^ 3 = 1) :
    integralChevalleySimpleCorootParameter i u ^ 3 = 1 := by
  funext k
  simp only [Pi.pow_apply, Pi.one_apply, integralChevalleySimpleCorootParameter]
  split_ifs <;> simp [hu]

omit [CharZero R] [P.IsCrystallographic] [P.IsReduced] [Fintype ι] in
private theorem simpleParameter_inv (i : b.support) (u : Fˣ) :
    integralChevalleySimpleCorootParameter i u⁻¹ =
      (integralChevalleySimpleCorootParameter i u)⁻¹ := by
  funext k
  simp only [Pi.inv_apply, integralChevalleySimpleCorootParameter]
  split_ifs <;> simp

private theorem cube_square (u : Fˣ) (hu : u ^ 3 = 1) : (u ^ 2) ^ 3 = 1 := by
  rw [← pow_mul, Nat.mul_comm 2 3, pow_mul, hu, one_pow]

/-- The diagonal central parameter has cube one. -/
theorem centralMatrix_cube (j : Fin 6 → b.support) (u : Fˣ) (hu : u ^ 3 = 1) :
    centralMatrix F j u ^ 3 = 1 := by
  let T : (b.support → Fˣ) →* (Matrix (b.support ⊕ ι) (b.support ⊕ ι) F)ˣ :=
    ⟨⟨integralChevalleyTorusElement (P := P), integralChevalleyTorusElement_one⟩,
      integralChevalleyTorusElement_mul⟩
  change T (centralParameter F j u) ^ 3 = 1
  rw [← map_pow]
  have hp : centralParameter F j u ^ 3 = 1 := by
    simp only [centralParameter, mul_pow, simpleParameter_cube F _ u hu,
      simpleParameter_cube F _ (u ^ 2) (cube_square F u hu), mul_one]
  rw [hp, map_one]

variable (v : SixNodeWord F →* (Matrix (b.support ⊕ ι) (b.support ⊕ ι) F)ˣ)
  (j : Fin 6 → b.support)
  (hv : ∀ s i t, v (FreeGroup.of (s, i, t)) =
    (RootPairing.SimpleGeckGroup.simpleFamily (b := b)).unit (s, j i) t)

include hv

private theorem eval_nWord (i : Fin 6) (t : F) :
    v (nWord F i t) = matrixN (b := b) (j i) t := by
  let := P.indexNeg
  simp only [nWord, map_mul, hv, matrixN, rootCurveUnit_simple, rootCurveUnit_neg_simple]
  rfl

/-- The cubic coroot word has precisely the chosen ambient diagonal. -/
theorem eval_hWord (i : Fin 6) (u : Fˣ) (hu : u ^ 3 = 1) :
    v (hWord F i u) = integralChevalleyTorusElement (P := P)
      (integralChevalleySimpleCorootParameter (j i) u) := by
  rw [hWord, map_mul, eval_nWord F v j hv, eval_nWord F v j hv]
  exact CorootMatrices.matrixH_inv_of_cube (j i) u hu

/-- The four coroot factors give the literal central diagonal. -/
theorem eval_centralWord (u : Fˣ) (hu : u ^ 3 = 1) :
    v (centralWord F u) = centralMatrix F j u := by
  simp only [centralWord, map_mul, eval_hWord F v j hv _ u hu,
    eval_hWord F v j hv _ (u ^ 2) (cube_square F u hu),
    ← integralChevalleyTorusElement_mul]
  rfl

/-- The pinned diagram word evaluates to the inverse central diagonal. -/
theorem eval_diagram_centralWord (u : Fˣ) (hu : u ^ 3 = 1) :
    v (diagramWord F (centralWord F u)) = (centralMatrix F j u)⁻¹ := by
  have hs : u ^ 2 = u⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa only [← pow_succ] using hu
  simp only [centralWord, map_mul, diagramWord_hWord]
  change v (hWord F 5 u) * v (hWord F 4 (u ^ 2)) *
    v (hWord F 1 u) * v (hWord F 0 (u ^ 2)) = _
  simp only [eval_hWord F v j hv _ u hu,
    eval_hWord F v j hv _ (u ^ 2) (cube_square F u hu),
    ← integralChevalleyTorusElement_mul, centralMatrix,
    ← integralChevalleyTorusElement_inv]
  congr 1
  rw [centralParameter, hs]
  simp only [simpleParameter_inv, mul_inv_rev, inv_inv]
  ac_rfl

end Matrices

local instance : Fintype typeE7Roots := Fintype.ofFinite _
local instance : Fintype typeE8Roots := Fintype.ofFinite _

/-- The six-node inclusion on E7 simple indices. -/
def e7Node (i : Fin 6) : typeE7RootPairing_base.support :=
  typeE7RootPairing_baseEquiv (i.castLE (by decide))

/-- The six-node inclusion on E8 simple indices. -/
def e8Node (i : Fin 6) : typeE8RootPairing_base.support :=
  typeE8RootPairing_baseEquiv (i.castLE (by decide))

private theorem e7Six_matrix_of (s : Bool) (i : Fin 6) (t : F) :
    ((ExceptionalSplit.rootGenerated _ _ F).subtype.comp (e7Six F))
      (FreeGroup.of (s, i, t)) =
    (RootPairing.SimpleGeckGroup.simpleFamily (b := typeE7RootPairing_base)).unit
      (s, e7Node i) t := by
  simp [e7Simple, e7Node]

private theorem e8Six_matrix_of (s : Bool) (i : Fin 6) (t : F) :
    ((ExceptionalSplit.rootGenerated _ _ F).subtype.comp (e8Six F))
      (FreeGroup.of (s, i, t)) =
    (RootPairing.SimpleGeckGroup.simpleFamily (b := typeE8RootPairing_base)).unit
      (s, e8Node i) t := by
  simp [e8Simple, e8Node]

/-- Actual E7 evaluation of the proposed central kernel word. -/
theorem e7Six_centralWord (u : Fˣ) (hu : u ^ 3 = 1) :
    (e7Six F (centralWord F u)).val = centralMatrix F e7Node u :=
  eval_centralWord F _ e7Node (e7Six_matrix_of F) u hu

/-- Actual E8 evaluation of the proposed central kernel word. -/
theorem e8Six_centralWord (u : Fˣ) (hu : u ^ 3 = 1) :
    (e8Six F (centralWord F u)).val = centralMatrix F e8Node u :=
  eval_centralWord F _ e8Node (e8Six_matrix_of F) u hu

/-- The E7 central word has cube one. -/
theorem e7Six_centralWord_cube (u : Fˣ) (hu : u ^ 3 = 1) :
    e7Six F (centralWord F u) ^ 3 = 1 := by
  apply Subtype.ext
  simpa only [Subgroup.coe_pow, OneMemClass.coe_one, e7Six_centralWord F u hu] using
    centralMatrix_cube F e7Node u hu

/-- The E8 central word has cube one. -/
theorem e8Six_centralWord_cube (u : Fˣ) (hu : u ^ 3 = 1) :
    e8Six F (centralWord F u) ^ 3 = 1 := by
  apply Subtype.ext
  simpa only [Subgroup.coe_pow, OneMemClass.coe_one, e8Six_centralWord F u hu] using
    centralMatrix_cube F e8Node u hu

/-- The literal E7 diagram action inverts the central word's value. -/
theorem e7Six_diagram_centralWord (u : Fˣ) (hu : u ^ 3 = 1) :
    e7Six F (diagramWord F (centralWord F u)) = (e7Six F (centralWord F u))⁻¹ := by
  apply Subtype.ext
  simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, Subgroup.coe_inv,
    e7Six_centralWord F u hu] using
      eval_diagram_centralWord F _ e7Node (e7Six_matrix_of F) u hu

/-- The literal E8 diagram action inverts the central word's value. -/
theorem e8Six_diagram_centralWord (u : Fˣ) (hu : u ^ 3 = 1) :
    e8Six F (diagramWord F (centralWord F u)) = (e8Six F (centralWord F u))⁻¹ := by
  apply Subtype.ext
  simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, Subgroup.coe_inv,
    e8Six_centralWord F u hu] using
      eval_diagram_centralWord F _ e8Node (e8Six_matrix_of F) u hu

end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters
