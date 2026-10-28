module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three.Model
public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions

/-!
# The faithful unitary graph in the two A₂ factors

Write γ for inverse transpose, φ for entrywise squaring, and τ = γφ on
SL₃ in characteristic two. The full identity-form SU₃(2^(2m + 1)) is fixed
by τ^(2m + 1). Its graph A ↦ (A, γτ^m(A)) is fixed by the two-factor action
(A,B) ↦ (τ^(m + 1)(γ(B)), γτ^m(A)). All maps act on actual matrices.

The essential central-kernel calculation holds on the entire SL₃ graph:
τ fixes cubic scalar matrices, so a graph element in the diagonal center
has A = A⁻¹ and A³ = 1, hence A = 1. Thus a map of the two factors whose
kernel lies in the diagonal center is faithful on the full unitary group.
No projective quotient or simplicity assumption is used.

`Descent` applies these results to a concrete F₄ subsystem construction.
The existence of that construction is a separate obligation. Source:
GLS3 Example 2.6.3 and the universal-unitary row of Table 4.7.3A,
`refs/KGroup/GLS3/chapter2.tex` and `chapter4.tex`. The source's
half-integer Ree parameter has square 2^(2m + 1).
-/

@[expose] public section

open Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups

namespace ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent
noncomputable section
variable {F : Type*} [Field F] [CharP F 2]
abbrev SL3 (F : Type*) [Field F] := Matrix.SpecialLinearGroup (Fin 3) F

def graph : Monoid.End (SL3 F) := (Matrix.PSL3.OuterSolvable.graphSL F).toMonoidHom

def field : Monoid.End (SL3 F) := SpecialLinearGroup.map (frobenius F 2)

def signedFrobenius : Monoid.End (SL3 F) := graph * field

omit [CharP F 2] in
@[simp] theorem graph_graph (A : SL3 F) : graph (graph A) = A :=
  (Matrix.PSL3.OuterSolvable.graphSL F).left_inv A

theorem graph_field : Commute (graph (F := F)) field := by
  apply MonoidHom.ext
  intro A
  change (SpecialLinearGroup.transpose (SpecialLinearGroup.map (frobenius F 2) A))⁻¹ =
    SpecialLinearGroup.map (frobenius F 2) (SpecialLinearGroup.transpose A)⁻¹
  rw [map_inv]
  congr 1

omit [CharP F 2] in
theorem graph_sq : (graph (F := F)) ^ 2 = 1 := by
  ext A : 1
  exact graph_graph A

theorem field_pow_entry (n : ℕ) (A : SL3 F) (i j : Fin 3) :
    ((field ^ n) A) i j = (A i j) ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (((field ^ n) A) i j) ^ 2 = _
    rw [ih, ← pow_mul, ← pow_succ]

theorem signedFrobenius_odd (m : ℕ) :
    signedFrobenius (F := F) ^ (2 * m + 1) = graph * field ^ (2 * m + 1) := by
  rw [signedFrobenius, graph_field.mul_pow, pow_succ, pow_mul, graph_sq, one_pow, one_mul]

def toSL (m : ℕ) : (Three.form m).specialSubgroup →* SL3 (Three.QuadraticField m) where
  toFun A := ⟨A.val.val, congrArg Units.val (((Three.form m).mem_specialSubgroup_iff A.val).mp A.property).2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem toSL_injective (m : ℕ) : Function.Injective (toSL m) := by
  intro A B h
  exact Subtype.ext (Units.ext (congrArg Subtype.val h))

theorem unitary_fixed (m : ℕ) (A : (Three.form m).specialSubgroup) :
    (signedFrobenius ^ (2 * m + 1)) (toSL m A) = toSL m A := by
  rw [signedFrobenius_odd]
  change (SpecialLinearGroup.transpose ((field ^ (2 * m + 1)) (toSL m A)))⁻¹ = toSL m A
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  have h := (((Three.form m).mem_specialSubgroup_iff A.val).mp A.property).1
  rw [Three.form_matrix, mul_one] at h
  change (SpecialLinearGroup.transpose ((field ^ (2 * m + 1)) (toSL m A))).val * (toSL m A).val = 1
  convert h using 2
  · ext i j
    exact field_pow_entry (2 * m + 1) (toSL m A) j i
  · rfl

omit [CharP F 2] in
theorem graph_of_central (A : SL3 F) (hA : A ∈ Subgroup.center (SL3 F)) :
    graph A = A⁻¹ := by
  obtain ⟨z, hz, he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  change (SpecialLinearGroup.transpose A)⁻¹ = A⁻¹
  congr 1
  apply Subtype.ext
  change (A.val).transpose = A.val
  rw [← he]
  ext i j
  by_cases h : i = j <;> simp [Matrix.transpose_apply, Matrix.scalar_apply, h, Ne.symm]

omit [CharP F 2] in
theorem central_cube (A : SL3 F) (hA : A ∈ Subgroup.center (SL3 F)) : A ^ 3 = 1 := by
  obtain ⟨z, hz, he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hz : z ^ 3 = 1 := by simpa using hz
  apply Subtype.ext
  change A.val ^ 3 = 1
  rw [← he, ← map_pow, hz, map_one]

theorem field_of_central (A : SL3 F) (hA : A ∈ Subgroup.center (SL3 F)) :
    field A = A ^ 2 := by
  obtain ⟨z, hz, he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  apply Subtype.ext
  change (A.val).map (frobenius F 2) = A.val ^ 2
  rw [← he, ← map_pow]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij, frobenius_def]

theorem signedFrobenius_central (A : SL3 F) (hA : A ∈ Subgroup.center (SL3 F)) :
    signedFrobenius A = A := by
  change graph (field A) = A
  rw [field_of_central A hA, map_pow, graph_of_central A hA]
  apply mul_right_cancel (b := A ^ 2)
  rw [inv_pow, inv_mul_cancel, ← pow_succ', central_cube A hA]

theorem signedFrobenius_pow_central (n : ℕ) (A : SL3 F)
    (hA : A ∈ Subgroup.center (SL3 F)) : (signedFrobenius ^ n) A = A := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    change signedFrobenius ((signedFrobenius ^ n) A) = A
    rw [ih, signedFrobenius_central A hA]

/-- The two-factor exceptional action with diagonal cubic kernel inverted. -/
def pairTwist (m : ℕ) : Monoid.End (SL3 F × SL3 F) :=
  (((signedFrobenius ^ (m + 1)).comp graph).comp (MonoidHom.snd _ _)).prod
    ((graph.comp (signedFrobenius ^ m)).comp (MonoidHom.fst _ _))

def graphPair (m : ℕ) : SL3 F →* SL3 F × SL3 F :=
  (MonoidHom.id _).prod (graph.comp (signedFrobenius ^ m))

theorem graphPair_fixed (m : ℕ) (A : SL3 F)
    (hA : (signedFrobenius ^ (2 * m + 1)) A = A) :
    pairTwist m (graphPair m A) = graphPair m A := by
  apply Prod.ext
  · change (signedFrobenius ^ (m + 1)) (graph (graph ((signedFrobenius ^ m) A))) = A
    rw [graph_graph]
    change (signedFrobenius (F := F) ^ (m + 1) * signedFrobenius ^ m : Monoid.End (SL3 F)) A = A
    rw [← pow_add, show m + 1 + m=2 * m + 1 by omega, hA]
  · rfl

/-- The unitary graph cannot lose the scalar three-center in the central product. -/
theorem graphPair_injective_mod_diagonalCenter {G : Type*} [Group G] (m : ℕ)
    (P : SL3 F × SL3 F →* G)
    (hker : ∀ A B, P (A,B) = 1 → A = B ∧ A ∈ Subgroup.center (SL3 F)) :
    Function.Injective (P.comp (graphPair m)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro A hA
  obtain ⟨he, hc⟩ := hker A (graph ((signedFrobenius ^ m) A)) hA
  rw [signedFrobenius_pow_central m A hc, graph_of_central A hc] at he
  have hs : A ^ 2 = 1 := by
    rw [pow_two]
    calc A * A = A⁻¹ * A := congrArg (fun x => x * A) he
         _ = 1 := inv_mul_cancel A
  have ht := central_cube A hc
  rw [pow_succ A 2, hs, one_mul] at ht
  exact ht

variable {E : Type*} [Field E] [CharP E 2]

omit [CharP F 2] [CharP E 2] in
theorem map_graph (f : E →+* F) (A : SL3 E) :
    SpecialLinearGroup.map f (graph A) = graph (SpecialLinearGroup.map f A) := by
  change SpecialLinearGroup.map f (SpecialLinearGroup.transpose A)⁻¹ =
    (SpecialLinearGroup.transpose (SpecialLinearGroup.map f A))⁻¹
  rw [map_inv]
  congr 1

theorem map_signedFrobenius (f : E →+* F) (A : SL3 E) :
    SpecialLinearGroup.map f (signedFrobenius A) =
      signedFrobenius (SpecialLinearGroup.map f A) := by
  change SpecialLinearGroup.map f (graph (field A)) = graph (field (SpecialLinearGroup.map f A))
  rw [map_graph]
  congr 1
  ext i j
  exact map_pow f (A i j) 2

theorem map_signedFrobenius_pow (f : E →+* F) (n : ℕ) (A : SL3 E) :
    SpecialLinearGroup.map f ((signedFrobenius ^ n) A) =
      (signedFrobenius ^ n) (SpecialLinearGroup.map f A) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ']
    change SpecialLinearGroup.map f (signedFrobenius ((signedFrobenius ^ n) A)) =
      signedFrobenius ((signedFrobenius ^ n) (SpecialLinearGroup.map f A))
    rw [map_signedFrobenius, ih]

/-- Literal coefficient extension of the identity-form special unitary matrices. -/
def unitarySL (m : ℕ) (f : Three.QuadraticField m →+* F) :
    (Three.form m).specialSubgroup →* SL3 F := (SpecialLinearGroup.map f).comp (toSL m)

omit [CharP F 2] in
theorem unitarySL_injective (m : ℕ) (f : Three.QuadraticField m →+* F) :
    Function.Injective (unitarySL m f) := by
  intro A B h
  apply toSL_injective m
  ext i j
  exact f.injective (congrArg (fun X : SL3 F => X i j) h)

theorem unitarySL_fixed (m : ℕ) (f : Three.QuadraticField m →+* F)
    (A : (Three.form m).specialSubgroup) :
    (signedFrobenius ^ (2 * m + 1)) (unitarySL m f A) = unitarySL m f A := by
  change (signedFrobenius ^ (2 * m + 1)) (SpecialLinearGroup.map f (toSL m A)) = _
  rw [← map_signedFrobenius_pow, unitary_fixed]
  rfl

def unitaryPair (m : ℕ) (f : Three.QuadraticField m →+* F) :
    (Three.form m).specialSubgroup →* SL3 F × SL3 F :=
  (graphPair m).comp (unitarySL m f)

theorem unitaryPair_fixed (m : ℕ) (f : Three.QuadraticField m →+* F)
    (A : (Three.form m).specialSubgroup) :
    pairTwist m (unitaryPair m f A) = unitaryPair m f A :=
  graphPair_fixed m _ (unitarySL_fixed m f A)


end
end ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent
