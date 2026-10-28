module

public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.LeviProjection.SplitRepresentation.Generation
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.LeviProjection.SplitRepresentation.FourSpace

/-!
# Restricting the full split B₂ Levi to its four-space

Every signed simple curve intertwines its ambient matrix with the specified
four-by-four matrix. The full-Levi generation theorem extends this relation
by products and inverses. Injectivity of the four-space inclusion makes the
restricted matrix unique, hence defines an actual group homomorphism.

Pairing this homomorphism with its composite with the actual restricted twist
has exactly the prescribed generated range. This argument does not infer
faithfulness on the whole Levi from injectivity of the four-space inclusion;
the whole-Levi kernel calculation is proved separately in `Kernel`.

Source: GLS3 §§2.3–2.4, for the B₂ Levi underlying Aschbacher–Smith
F.1.12(I)(5), printed p.263.
-/

@[expose] public noncomputable section
namespace ReeF4.LargeLocalSeeds.SuzukiLeviProjection.SplitRepresentation
open Subgroup LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
variable {m : ℕ}

/-- The ambient representation forgets only the two subgroup proofs. -/
def ambientLeviHom (m : ℕ) : splitLevi m .suzuki →* MatrixUnits m :=
  (SplitGroup m).subtype.comp (splitLevi m .suzuki).subtype

/-- Intertwining with the literal ambient action. -/
def FourIntertwines (x : splitLevi m .suzuki) (M : MatrixGroup m) : Prop :=
  (ambientLeviHom m x).val * fourEmbedding m = fourEmbedding m * M.val

theorem fourIntertwines_one : FourIntertwines (1 : splitLevi m .suzuki) 1 := by
  simp [FourIntertwines]

theorem fourIntertwines_mul {x y : splitLevi m .suzuki} {M N : MatrixGroup m}
    (hx : FourIntertwines x M) (hy : FourIntertwines y N) :
    FourIntertwines (x * y) (M * N) := by
  unfold FourIntertwines at *
  simp only [map_mul, Units.val_mul]
  rw [Matrix.mul_assoc, hy, ← Matrix.mul_assoc, hx, Matrix.mul_assoc]

theorem fourIntertwines_inv {x : splitLevi m .suzuki} {M : MatrixGroup m}
    (hx : FourIntertwines x M) : FourIntertwines x⁻¹ M⁻¹ := by
  unfold FourIntertwines at *
  rw [map_inv]
  calc
    (ambientLeviHom m x)⁻¹.val * fourEmbedding m =
        (ambientLeviHom m x)⁻¹.val * ((fourEmbedding m * M.val) * M⁻¹.val) := by
      rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    _ = (ambientLeviHom m x)⁻¹.val *
        (((ambientLeviHom m x).val * fourEmbedding m) * M⁻¹.val) := by rw [hx]
    _ = ((ambientLeviHom m x)⁻¹.val * (ambientLeviHom m x).val) *
        fourEmbedding m * M⁻¹.val := by simp only [Matrix.mul_assoc]
    _ = fourEmbedding m * M⁻¹.val := by rw [Units.inv_mul, Matrix.one_mul]

/-- Every element of the whole Levi preserves the four half-root lines. -/
theorem fourIntertwines_exists (x : splitLevi m .suzuki) : ∃ M, FourIntertwines x M := by
  have hx : x ∈ closure (Set.range (splitGenerator m)) := by
    rw [splitGenerator_closure]
    exact mem_top x
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨i,t⟩,rfl⟩ := hx
    exact ⟨matrixGenerator m i t, signedRoot_intertwines i t⟩
  | one => exact ⟨1, fourIntertwines_one⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨M,hM⟩ := ihx
    obtain ⟨N,hN⟩ := ihy
    exact ⟨M * N, fourIntertwines_mul hM hN⟩
  | inv x hx ih =>
    obtain ⟨M,hM⟩ := ih
    exact ⟨M⁻¹, fourIntertwines_inv hM⟩

theorem fourIntertwines_unique {x : splitLevi m .suzuki} {M N : MatrixGroup m}
    (hM : FourIntertwines x M) (hN : FourIntertwines x N) : M = N := by
  apply Units.ext
  exact fourEmbedding_mul_injective (hM.symm.trans hN)

/-- The actual restricted representation, with no assumed kernel property. -/
def splitLeviRepresentation (m : ℕ) : splitLevi m .suzuki →* MatrixGroup m where
  toFun x := (fourIntertwines_exists x).choose
  map_one' := fourIntertwines_unique (fourIntertwines_exists 1).choose_spec
    fourIntertwines_one
  map_mul' x y := fourIntertwines_unique (fourIntertwines_exists (x * y)).choose_spec
    (fourIntertwines_mul (fourIntertwines_exists x).choose_spec
      (fourIntertwines_exists y).choose_spec)

theorem splitLeviRepresentation_intertwines (x : splitLevi m .suzuki) :
    FourIntertwines x (splitLeviRepresentation m x) :=
  (fourIntertwines_exists x).choose_spec

/-- Literal matrices for nodes 1, 2, −1, −2, at every field parameter. -/
@[simp] theorem splitLeviRepresentation_generator (a : Fin 4 × CoefficientField m) :
    splitLeviRepresentation m (splitGenerator m a) = matrixGenerator m a.1 a.2 :=
  fourIntertwines_unique (splitLeviRepresentation_intertwines (splitGenerator m a))
    (signedRoot_intertwines a.1 a.2)

/-- The represented entries are the actual ambient submatrix entries. -/
theorem splitLeviRepresentation_entry (x : splitLevi m .suzuki) (i j : Fin 4) :
    (splitLeviRepresentation m x).val i j =
      (ambientLeviHom m x).val (fourIndex i) (fourIndex j) := by
  have h := congrArg (fun A => A (fourIndex i) j) (splitLeviRepresentation_intertwines x)
  simpa only [FourIntertwines, mul_fourEmbedding, fourEmbedding_mul] using h.symm

/-- The kernel is precisely the subgroup fixing all four embedded columns. -/
theorem splitLeviRepresentation_eq_one_iff (x : splitLevi m .suzuki) :
    splitLeviRepresentation m x = 1 ↔
      (ambientLeviHom m x).val * fourEmbedding m = fourEmbedding m := by
  constructor
  · intro hx
    have h := splitLeviRepresentation_intertwines x
    simpa only [FourIntertwines, hx, Units.val_one, Matrix.mul_one] using h
  · intro hx
    apply fourIntertwines_unique (splitLeviRepresentation_intertwines x)
    simpa only [FourIntertwines, Units.val_one, Matrix.mul_one] using hx

/-- Pairing uses the actual restricted exceptional field twist. -/
theorem pairedMap_generator (d : LocalBlockInput m) (a : Fin 4 × CoefficientField m) :
    pairedMap d (splitLeviRepresentation m) (splitGenerator m a) = pairedGenerator m a := by
  change (splitLeviRepresentation m (splitGenerator m a),
    splitLeviRepresentation m (splitTwist d (splitGenerator m a))) = _
  rw [splitTwist_generator, splitLeviRepresentation_generator,
    splitLeviRepresentation_generator]
  rfl

/-- Full-Levi generation proves equality with the prescribed matrix graph. -/
theorem pairedMap_range (d : LocalBlockInput m) :
    (pairedMap d (splitLeviRepresentation m)).range = pairedSubgroup m := by
  rw [MonoidHom.range_eq_map, ← splitGenerator_closure,
    MonoidHom.map_closure, ← Set.range_comp]
  unfold pairedSubgroup
  congr 2
  funext a
  exact pairedMap_generator d a

end ReeF4.LargeLocalSeeds.SuzukiLeviProjection.SplitRepresentation
