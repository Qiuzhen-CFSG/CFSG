module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Pi

/-!
# Coordinates for the proper adjacent flag presentation

Write a point in a binary plane as `F(a,b)`, where the plane is spanned by
`a,b`. Linearity in `b` reduces the formal generators to 64 coordinates.
We impose `F(0,b)=0`, `F(a,a)=0`, and the three-point plane relation
`F(a,b)+F(b,a)+F(a+b,b)=0`. The resulting quotient is auxiliary: its comparison
with the actual regular quotient requires a geometric construction.

`evaluate` sends these coordinates to any family linear in its second argument.
`relationSpace_le_ker` proves that this evaluation descends when the geometric
relations hold. UniversalBound applies this exact map to the actual regular
quotient, retaining its geometric construction as an explicit premise.

Source application: Aschbacher–Smith, K.3.2, printed pp.451,454–455;
Guralnick–Malle, Classification of 2F-modules II, author manuscript,
Proposition 4.8(3), pp.27–28. This is a finite binary highest-vector calculation,
not an invocation of an absolute highest-weight classification.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.SupportSeparation.KernelControl.FlagPresentation
/-- The actual four-dimensional binary natural space. -/
abbrev Point := Fin 4 → ZMod 2
/-- Four second-coordinate coefficients at each of the sixteen first vectors. -/
abbrev Coordinates := (Fin 16 × Fin 4) → ZMod 2

/-- Binary enumeration of the natural space, least significant coordinate first. -/
def point (a : Fin 16) : Point := fun i => if a.val.testBit i.val then 1 else 0

/-- Addition of binary vector codes. -/
def xor (a b : Fin 16) : Fin 16 := ⟨(a.val ^^^ b.val) % 16, Nat.mod_lt _ (by decide)⟩

theorem point_zero : point 0 = 0 := by decide

theorem point_xor : ∀ a b, point (xor a b) = point a + point b := by decide

theorem point_surjective : Function.Surjective point := by decide

/-- The formal symbol `F(a,b)`, already linear in the second coordinate. -/
def pairVector (a b : Fin 16) : Coordinates :=
  fun p => if p.1 = a then point b p.2 else 0

/-- Zero-point, diagonal, and three-point-plane relation indices. -/
abbrev Relation := Fin 4 ⊕ (Fin 16 ⊕ (Fin 16 × Fin 16))

/-- The three literal families of flag relations in coordinates. -/
def relator : Relation → Coordinates
  | .inl i => Pi.single (0, i) 1
  | .inr (.inl a) => pairVector a a
  | .inr (.inr (a, b)) => pairVector a b + pairVector b a + pairVector (xor a b) b

/-- The linear span of the displayed geometric relations. -/
def relationSpace : Submodule (ZMod 2) Coordinates :=
  Submodule.span (ZMod 2) (Set.range relator)

/-- The auxiliary coordinate presentation of binary flags. -/
abbrev FlagQuotient := Coordinates ⧸ relationSpace

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
/-- Evaluate coordinates in a family linear in the second flag coordinate. -/
noncomputable def evaluate (f : Point → Point →ₗ[ZMod 2] V) : Coordinates →ₗ[ZMod 2] V :=
  ∑ a, (f (point a)).comp (LinearMap.pi fun i => LinearMap.proj (a, i))

theorem evaluate_pairVector (f : Point → Point →ₗ[ZMod 2] V) (a b : Fin 16) :
    evaluate f (pairVector a b) = f (point a) (point b) := by
  change (∑ x, f (point x) (fun i => if x = a then point b i else 0)) = _
  have h (x : Fin 16) : (fun i => if x = a then point b i else 0) =
      if x = a then point b else 0 := by split_ifs <;> rfl
  simp_rw [h]
  simp [apply_ite]

private theorem evaluate_zero_relator (f : Point → Point →ₗ[ZMod 2] V) (hz : f 0 = 0)
    (i : Fin 4) : evaluate f (relator (.inl i)) = 0 := by
  change (∑ a, f (point a) (fun j => (Pi.single (0, i) 1 : Coordinates) (a, j))) = 0
  have h (a : Fin 16) : (fun j => (Pi.single (0, i) 1 : Coordinates) (a, j)) =
      if a = 0 then Pi.single i 1 else 0 := by
    ext j
    by_cases ha : a = 0 <;> by_cases hj : j = i <;> simp [ha, hj]
  simp_rw [h]
  simp [apply_ite, point_zero, hz]

theorem relationSpace_le_ker (f : Point → Point →ₗ[ZMod 2] V)
    (hz : f 0 = 0) (hd : ∀ a, f a a = 0)
    (hp : ∀ a b, f a b + f b a + f (a + b) b = 0) :
    relationSpace ≤ (evaluate f).ker := by
  rw [relationSpace, Submodule.span_le]
  rintro _ ⟨i | a | ⟨a, b⟩, rfl⟩
  · exact evaluate_zero_relator f hz i
  · change evaluate f (pairVector a a) = 0
    rw [evaluate_pairVector, hd]
  · change evaluate f (pairVector a b + pairVector b a + pairVector (xor a b) b) = 0
    simp only [map_add, evaluate_pairVector, point_xor, hp]
end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.SupportSeparation.KernelControl.FlagPresentation
