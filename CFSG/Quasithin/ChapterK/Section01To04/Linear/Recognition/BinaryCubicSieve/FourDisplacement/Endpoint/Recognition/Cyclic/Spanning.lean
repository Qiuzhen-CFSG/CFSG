module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Recognition.Cyclic.Flags
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Rank-one generators of the literal trace kernel

Twelve off-diagonal flags and three flags of the form (eᵢ+e₃,eᵢ*+e₃*)
give fifteen rank-one matrices. Explicit entry functionals recover their
coefficients. Their independence and the known trace-kernel dimension show
that realization is surjective. The coordinate definitions are exposed for
the separate proof that the elementary additive relations generate its kernel.

Source: Aschbacher–Smith, K.3.2, printed pp.451,454–455;
Guralnick–Malle, Classification of 2F-modules II, author manuscript,
Lemma 4.5 step 2 and Proposition 4.8 step 3A.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Representation
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Cyclic

/-- A standard basis vector of the natural four-space. -/
def standard (i : Fin 4) : Natural := Pi.single i 1
/-- The twelve off-diagonal and three diagonal-pair generators. -/
def basisPairs : Fin 15 → Natural × Natural :=
  ![(standard 0, standard 1), (standard 0, standard 2), (standard 0, standard 3),
    (standard 1, standard 0), (standard 1, standard 2), (standard 1, standard 3),
    (standard 2, standard 0), (standard 2, standard 1), (standard 2, standard 3),
    (standard 3, standard 0), (standard 3, standard 1), (standard 3, standard 2),
    (standard 0 + standard 3, standard 0 + standard 3),
    (standard 1 + standard 3, standard 1 + standard 3),
    (standard 2 + standard 3, standard 2 + standard 3)]

/-- Twelve off-diagonal flags and three diagonal-pair flags. -/
def spanningFlag (i : Fin 15) : Flag := ⟨basisPairs i, by revert i; decide⟩

/-- A matrix coefficient in the standard natural basis. -/
def entry (i j : Fin 4) : TraceZero →ₗ[ZMod 2] ZMod 2 where
  toFun f := f.val (standard j) i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Matrix entry of the flag's rank-one endomorphism. -/
theorem entry_rankOne (a : Flag) (i j : Fin 4) :
    entry i j (rankOne a) = covector a j * point a i := by
  change dotProduct (covector a) (Pi.single j 1) * point a i = _
  simp [dotProduct, Pi.single_apply]

/-- Coefficients relative to the fifteen rank-one flags. -/
def coordinates : TraceZero →ₗ[ZMod 2] (Fin 15 → ZMod 2) :=
  LinearMap.pi ![entry 0 1, entry 0 2, entry 0 3 + entry 0 0,
    entry 1 0, entry 1 2, entry 1 3 + entry 1 1,
    entry 2 0, entry 2 1, entry 2 3 + entry 2 2,
    entry 3 0 + entry 0 0, entry 3 1 + entry 1 1, entry 3 2 + entry 2 2,
    entry 0 0, entry 1 1, entry 2 2]

/-- Each selected flag has its expected standard coordinate. -/
theorem coordinates_spanningFlag (i : Fin 15) :
    coordinates (rankOne (spanningFlag i)) = Pi.single i 1 := by
  ext j
  revert i j
  decide

/-- The fifteen explicit trace-zero rank-one matrices are independent. -/
theorem spanningFlag_independent : LinearIndependent (ZMod 2) (rankOne ∘ spanningFlag) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have he := congrArg (fun f => coordinates f i) hc
  simpa [map_sum, map_smul, coordinates_spanningFlag, Function.comp_def,
    Pi.single_apply, ite_mul, mul_ite] using he

/-- The literal trace kernel is spanned by incident rank-one endomorphisms. -/
theorem realization_surjective : Function.Surjective realization := by
  apply LinearMap.range_eq_top.mp
  apply top_le_iff.mp
  have hspan := spanningFlag_independent.span_eq_top_of_card_eq_finrank
    (by simpa using finrank_traceZero.symm)
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact ⟨Finsupp.single (spanningFlag i) 1, realization_single _⟩

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Cyclic
