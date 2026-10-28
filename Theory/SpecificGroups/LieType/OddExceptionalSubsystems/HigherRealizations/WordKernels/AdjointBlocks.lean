module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.SixNodes
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.AdjointBlocks.Coordinates
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.AdjointBlocks.DividedPowers

/-!
# The E6 integral adjoint block in the literal E7 and E8 representations

The coordinate inclusions in `Coordinates` identify the E6 Cartan-plus-root
basis with a subset of each larger Geck basis. The integral simple operators
preserve that block, and `DividedPowers` proves equivariance of every integral
divided power before scalar extension. Thus both signed simple curves preserve
the block over any field, including characteristic three.

Multiplication and inversion propagate the comparison to every six-node word.
Reading the included coordinates proves injectivity over the coefficient field
itself, so a word trivial in either larger matrix carrier is trivial in the
source E6 carrier. The final two theorems supply exactly the backward kernel
inclusions needed by `WordKernels.Reduction`; the converse comparison and marked
folded-map assembly belong to that consumer.

Source: GLS3 §2.6.2–3, the common integral lattice for a subsystem
(`refs/KGroup/GLS3/chapter2.tex`), used for the exceptional inclusions in
Aschbacher–Smith A.2.17, printed p.39 (`refs/quasithin.pdf`).
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.HigherRealizations.AdjointBlocks
open Theory.AlgebraicGroup.StandardRootSystem Matrix
open RootPairing.SimpleGeckGroup
attribute [local instance] Classical.decEq
local instance : Fintype typeE7Roots := Fintype.ofFinite _
local instance : Fintype typeE8Roots := Fintype.ofFinite _

section Words
variable {m n α S : Type*} [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n] [CommRing S]

private theorem inverse_intertwines (A : (Matrix m m S)ˣ) (B : (Matrix n n S)ˣ)
    (J : Matrix n m S) (h : B.val * J = J * A.val) :
    B⁻¹.val * J = J * A⁻¹.val := by
  calc
    B⁻¹.val * J = B⁻¹.val * (J * A.val) * A⁻¹.val := by simp [Matrix.mul_assoc]
    _ = B⁻¹.val * (B.val * J) * A⁻¹.val := by rw [h]
    _ = J * A⁻¹.val := by simp [← Matrix.mul_assoc]

/-- The literal generator comparison propagates through multiplication and inversion. -/
theorem word_intertwines
    (a : FreeGroup α →* (Matrix m m S)ˣ) (b : FreeGroup α →* (Matrix n n S)ˣ)
    (J : Matrix n m S)
    (h : ∀ x, (b (FreeGroup.of x)).val * J = J * (a (FreeGroup.of x)).val)
    (w : FreeGroup α) : (b w).val * J = J * (a w).val := by
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of x => exact h x
  | inv_of x ih => simpa only [map_inv] using inverse_intertwines _ _ J ih
  | mul x y hx hy =>
    simp only [map_mul, Units.val_mul]
    rw [Matrix.mul_assoc, hy, ← Matrix.mul_assoc, hx, Matrix.mul_assoc]

/-- Reading the included coordinates proves faithfulness over the coefficient ring itself. -/
theorem eq_one_of_word_intertwines (e : m ↪ n)
    (A : (Matrix m m S)ˣ) (B : (Matrix n n S)ˣ)
    (h : B.val * inclusionOver e S = inclusionOver e S * A.val) (hb : B = 1) : A = 1 := by
  rw [hb] at h
  simp only [Units.val_one, Matrix.one_mul] at h
  apply Units.ext
  apply Matrix.mulVec_injective
  funext x
  apply inclusion_mulVec_injective e S
  rw [Matrix.mulVec_mulVec, ← h, Units.val_one, Matrix.one_mulVec]
end Words

/-- Integral divided-power restriction with the literal six-node numbering in E7. -/
theorem e7_dividedPower_intertwines (s : Bool) (i : Fin 6) (a : ℕ) :
    (simpleFamily (b := typeE7RootPairing_base)).dividedPower
      (s, typeE7RootPairing_baseEquiv (i.castLE (by decide))) a * e7Lattice =
    e7Lattice * (simpleFamily (b := Base)).dividedPower (s, simpleIndex i) a := by
  cases s
  · simpa only [simpleFamily, e7Lattice, e7Embedding_base_numbered] using
      e7Embedding.fDividedPower_intertwines (simpleIndex i) a
  · simpa only [simpleFamily, e7Lattice, e7Embedding_base_numbered] using
      e7Embedding.eDividedPower_intertwines (simpleIndex i) a

/-- Integral divided-power restriction with the literal six-node numbering in E8. -/
theorem e8_dividedPower_intertwines (s : Bool) (i : Fin 6) (a : ℕ) :
    (simpleFamily (b := typeE8RootPairing_base)).dividedPower
      (s, typeE8RootPairing_baseEquiv (i.castLE (by decide))) a * e8Lattice =
    e8Lattice * (simpleFamily (b := Base)).dividedPower (s, simpleIndex i) a := by
  cases s
  · simpa only [simpleFamily, e8Lattice, e8Embedding_base_numbered] using
      e8Embedding.fDividedPower_intertwines (simpleIndex i) a
  · simpa only [simpleFamily, e8Lattice, e8Embedding_base_numbered] using
      e8Embedding.eDividedPower_intertwines (simpleIndex i) a

/-- The basis inclusion stays injective under arbitrary scalar extension. -/
theorem e7_lattice_injective (S : Type*) [CommRing S] :
    Function.Injective (Matrix.mulVec (e7Lattice.map (Int.castRingHom S))) :=
  inclusion_mulVec_injective e7Embedding.indexMap S

theorem e8_lattice_injective (S : Type*) [CommRing S] :
    Function.Injective (Matrix.mulVec (e8Lattice.map (Int.castRingHom S))) :=
  inclusion_mulVec_injective e8Embedding.indexMap S

variable (F : Type*) [Field F]

/-- The E7 signed simple curves preserve the integral E6 block after any field specialization. -/
theorem e7_simple_intertwines (s : Bool) (i : Fin 6) (t : F) :
    (e7Simple F s (i.castLE (by decide)) t).val.val * inclusionOver e7Embedding.indexMap F =
      inclusionOver e7Embedding.indexMap F * (simpleRoot F s i t).val.val := by
  rw [signedSimple_val, simpleRoot_val]
  simp only [IntegralCubicFamily.unit_val]
  have h := e7Embedding.curve_intertwines F s (simpleIndex i) t
  rw [e7Embedding_base_numbered] at h
  exact h

/-- The E8 signed simple curves preserve the same block, including in characteristic three. -/
theorem e8_simple_intertwines (s : Bool) (i : Fin 6) (t : F) :
    (e8Simple F s (i.castLE (by decide)) t).val.val * inclusionOver e8Embedding.indexMap F =
      inclusionOver e8Embedding.indexMap F * (simpleRoot F s i t).val.val := by
  rw [signedSimple_val, simpleRoot_val]
  simp only [IntegralCubicFamily.unit_val]
  have h := e8Embedding.curve_intertwines F s (simpleIndex i) t
  rw [e8Embedding_base_numbered] at h
  exact h

theorem e7_word_intertwines (w : SixNodeWord F) :
    (e7Six F w).val.val * inclusionOver e7Embedding.indexMap F =
      inclusionOver e7Embedding.indexMap F * (sourceSix F w).val.val := by
  apply word_intertwines ((Subgroup.subtype _).comp (sourceSix F))
    ((Subgroup.subtype _).comp (e7Six F)) (inclusionOver e7Embedding.indexMap F)
  rintro ⟨s, i, t⟩
  simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, sourceSix_of, e7Six_of] using
    e7_simple_intertwines F s i t

theorem e8_word_intertwines (w : SixNodeWord F) :
    (e8Six F w).val.val * inclusionOver e8Embedding.indexMap F =
      inclusionOver e8Embedding.indexMap F * (sourceSix F w).val.val := by
  apply word_intertwines ((Subgroup.subtype _).comp (sourceSix F))
    ((Subgroup.subtype _).comp (e8Six F)) (inclusionOver e8Embedding.indexMap F)
  rintro ⟨s, i, t⟩
  simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, sourceSix_of, e8Six_of] using
    e8_simple_intertwines F s i t

/-- Every relation in the literal E7 six-node matrices holds in the source E6 matrices. -/
theorem e7Six_ker_le_sourceSix : (e7Six F).ker ≤ (sourceSix F).ker := by
  intro w hw
  change sourceSix F w = 1
  apply Subtype.ext
  exact eq_one_of_word_intertwines e7Embedding.indexMap (sourceSix F w).val
    (e7Six F w).val (e7_word_intertwines F w) (congrArg Subtype.val hw)

/-- Every relation in the literal E8 six-node matrices holds in the source E6 matrices. -/
theorem e8Six_ker_le_sourceSix : (e8Six F).ker ≤ (sourceSix F).ker := by
  intro w hw
  change sourceSix F w = 1
  apply Subtype.ext
  exact eq_one_of_word_intertwines e8Embedding.indexMap (sourceSix F w).val
    (e8Six F w).val (e8_word_intertwines F w) (congrArg Subtype.val hw)

end TwistedE6.FoldedSubsystem.HigherRealizations.AdjointBlocks
