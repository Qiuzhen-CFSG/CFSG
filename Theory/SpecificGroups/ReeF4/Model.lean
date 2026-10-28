module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism

/-!
# The concrete Ree groups ²F₄(2^(2m+1))

Let `σ` be the exceptional endomorphism of the root-generated F4 matrix group
over `GF(2^(2*m+1))`. Its square is entrywise Frobenius `F`. The Ree twist is
`σ^(2*m+1) = σ * F^m`; it is an involution on this finite split group because
`F^(2*m+1) = 1`. Its fixed subgroup is the concrete Ree carrier `Model m`.
The construction inherits its group structure and finiteness from matrix
units, with a faithful matrix representation given by inclusion.

On long roots the twist changes the root by the positive exceptional duality
and raises the parameter to `2^m`; on short roots it raises the parameter to
`2^(m+1)`, the Tits field automorphism. Thus this is the exceptional twisted
construction, using the proved exceptional map on the actual root matrices.

The family interface `IsReeF4Model` requires `1 ≤ m` and an actual multiplicative
equivalence to `Model m`. At `m = 0` the same construction gives the full
fixed-point group ²F₄(2). The simple endpoint ²F₄(2)' remains represented by
`Tits.ParrottGroup` and is excluded from this family interface. Order, simplicity
and local subgroup calculations are separate results.

Sources: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2 (printed p.4) and Remark A.2.4 (printed p.33),
`refs/quasithin.pdf`; GLS3, Theorem 1.15.4(b), Theorem 2.2.3(b) and
Definition 2.2.4, `refs/KGroup/GLS3/Chapter1.tex` and `chapter2.tex`.
The latter source also uses the half-integer parameter `2^(m+1/2)` for
the same Ree group; here the parameter always denotes the field size.
-/

public section

namespace ReeF4

open Theory.AlgebraicGroup

noncomputable section

/-- The exceptional field twist whose fixed points form ²F₄(2^(2m+1)). -/
def reeTwist (m : ℕ) : Monoid.End (SplitGroup m) :=
  exceptionalEndomorphism m ^ (2 * m + 1)

theorem reeTwist_eq_pow (m : ℕ) :
    reeTwist m = exceptionalEndomorphism m ^ (2 * m + 1) := by rfl

/-- The odd exceptional power equals the exceptional map composed with `F^m`. -/
theorem reeTwist_apply (m : ℕ) (x : SplitGroup m) :
    reeTwist m x = exceptionalEndomorphism m ((splitFrobeniusEnd m ^ m) x) := by
  rw [reeTwist, exceptionalEndomorphism_odd_power]
  rfl

private theorem frobenius_pow_rootGenerator (m n : ℕ)
    (r : F4Chevalley.Root) (t : CoefficientField m) :
    (splitFrobeniusEnd m ^ n) (rootGeneratorInGroup m r t) =
      rootGeneratorInGroup m r (t ^ (2 ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change splitFrobenius m ((splitFrobeniusEnd m ^ n)
        (rootGeneratorInGroup m r t)) = _
      rw [ih, splitFrobenius_rootGenerator, ← pow_mul, ← pow_succ]

/-- The complete root formula for the Ree twist. -/
theorem reeTwist_rootGenerator (m : ℕ) (r : F4Chevalley.Root)
    (t : CoefficientField m) :
    reeTwist m (rootGeneratorInGroup m r t) =
      rootGeneratorInGroup m (exceptionalRootPermutation r)
        (exceptionalParameter r (t ^ (2 ^ m))) := by
  rw [reeTwist_apply, frobenius_pow_rootGenerator, exceptionalEndomorphism_rootGenerator]

theorem reeTwist_rootGenerator_long (m : ℕ) (r : F4Chevalley.Root)
    (hr : IsLongRoot r) (t : CoefficientField m) :
    reeTwist m (rootGeneratorInGroup m r t) =
      rootGeneratorInGroup m (exceptionalRootPermutation r) (t ^ (2 ^ m)) := by
  rw [reeTwist_rootGenerator, exceptionalParameter_of_long hr]

theorem reeTwist_rootGenerator_short (m : ℕ) (r : F4Chevalley.Root)
    (hr : IsShortRoot r) (t : CoefficientField m) :
    reeTwist m (rootGeneratorInGroup m r t) =
      rootGeneratorInGroup m (exceptionalRootPermutation r) (titsEnd m t) := by
  rw [reeTwist_rootGenerator, exceptionalParameter_of_short hr, titsEnd_apply,
    ← pow_mul, ← pow_succ]

/-- The coefficient-field degree makes the Ree twist square to the identity. -/
theorem reeTwist_sq (m : ℕ) : reeTwist m ^ 2 = 1 :=
  exceptionalEndomorphism_odd_power_sq m

theorem reeTwist_involutive (m : ℕ) : Function.Involutive (reeTwist m) := by
  intro x
  exact DFunLike.congr_fun (reeTwist_sq m) x

/-- The Ree twist as an automorphism, with itself as inverse. -/
def reeAutomorphism (m : ℕ) : MulAut (SplitGroup m) :=
  { reeTwist m with
    invFun := reeTwist m
    left_inv := reeTwist_involutive m
    right_inv := reeTwist_involutive m }

@[simp] theorem reeAutomorphism_apply (m : ℕ) (x : SplitGroup m) :
    reeAutomorphism m x = reeTwist m x := by rfl

/-- The fixed subgroup of the concrete exceptional field twist. -/
def fixedSubgroup (m : ℕ) : Subgroup (SplitGroup m) :=
  MonoidHom.eqLocus (reeTwist m) (MonoidHom.id _)

@[simp] theorem mem_fixedSubgroup (m : ℕ) (x : SplitGroup m) :
    x ∈ fixedSubgroup m ↔ reeTwist m x = x := Iff.rfl

theorem mem_fixedSubgroup_iff (m : ℕ) (x : SplitGroup m) :
    x ∈ fixedSubgroup m ↔
      exceptionalEndomorphism m ((splitFrobeniusEnd m ^ m) x) = x := by
  rw [mem_fixedSubgroup, reeTwist_apply]

/-- The Ree group ²F₄(2^(2m+1)). The simple-family parameter range is `1 ≤ m`. -/
abbrev Model (m : ℕ) : Type := fixedSubgroup m

instance modelGroup (m : ℕ) : Group (Model m) :=
  inferInstanceAs (Group (fixedSubgroup m))

instance modelFinite (m : ℕ) : Finite (Model m) :=
  inferInstanceAs (Finite (fixedSubgroup m))

instance modelFintype (m : ℕ) : Fintype (Model m) := Fintype.ofFinite _

/-- Inclusion of the Ree group in its split F4 matrix group. -/
def toSplitGroup (m : ℕ) : Model m →* SplitGroup m := (fixedSubgroup m).subtype

@[simp] theorem toSplitGroup_apply (m : ℕ) (x : Model m) :
    toSplitGroup m x = x.val := by rfl

theorem toSplitGroup_injective (m : ℕ) : Function.Injective (toSplitGroup m) :=
  Subtype.val_injective

@[simp] theorem reeTwist_toSplitGroup (m : ℕ) (x : Model m) :
    reeTwist m (toSplitGroup m x) = toSplitGroup m x := x.property

/-- The defining representation on the 52-dimensional Cartan-plus-root lattice. -/
def matrixRepresentation (m : ℕ) : Model m →* MatrixUnits m :=
  (SplitGroup m).subtype.comp (toSplitGroup m)

@[simp] theorem matrixRepresentation_apply (m : ℕ) (x : Model m) :
    matrixRepresentation m x = x.val.val := by rfl

theorem matrixRepresentation_injective (m : ℕ) :
    Function.Injective (matrixRepresentation m) :=
  Subtype.val_injective.comp (toSplitGroup_injective m)

/-- Isomorphism to a member of the Ree family with field size at least eight.
The separate Tits simple endpoint is not included. -/
@[expose] def IsReeF4Model (G : Type*) [Group G] : Prop :=
  ∃ m : ℕ, 1 ≤ m ∧ Nonempty (G ≃* Model m)

theorem isReeF4Model_self (m : ℕ) (hm : 1 ≤ m) : IsReeF4Model (Model m) :=
  ⟨m, hm, ⟨MulEquiv.refl _⟩⟩

theorem IsReeF4Model.of_mulEquiv {G H : Type*} [Group G] [Group H]
    (h : IsReeF4Model G) (e : H ≃* G) : IsReeF4Model H := by
  obtain ⟨m, hm, ⟨f⟩⟩ := h
  exact ⟨m, hm, ⟨e.trans f⟩⟩

theorem isReeF4Model_mulEquiv_iff {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) : IsReeF4Model G ↔ IsReeF4Model H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

end

end ReeF4
