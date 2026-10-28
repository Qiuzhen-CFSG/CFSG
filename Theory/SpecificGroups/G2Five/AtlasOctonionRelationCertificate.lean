module

public import Theory.SpecificGroups.G2Five.AtlasPresentation
public import Theory.SpecificGroups.G2Five.AtlasOctonionPair

/-!
# Matrix certificates for words in the octonion pair

Word evaluation is mapped through the faithful eight-coordinate representation.
The append lemma assembles a word from certified subwords, while `ProductEntries`
checks an eight-term dot product in each entry by kernel reduction. An explicit
right inverse for the second generator interprets uppercase letters without
computing matrix inversion.

Sources: the pair and matrix conventions in `AtlasOctonionPair.lean`, and the
literal words in `AtlasPresentation.lean`; see `AtlasOctonionSource/README.md`.
-/

@[expose] public section

namespace G2Five.AtlasPresentation.RelationCertificate
abbrev Mat := Matrix (Fin 8) (Fin 8) (ZMod 5)

def ProductEntries (a b c : Mat) : Prop :=
  ∀ i j, a i 0 * b 0 j + a i 1 * b 1 j + a i 2 * b 2 j +
    a i 3 * b 3 j + a i 4 * b 4 j + a i 5 * b 5 j +
    a i 6 * b 6 j + a i 7 * b 7 j = c i j

instance (a b c : Mat) : Decidable (ProductEntries a b c) :=
  @Nat.decidableForallFin 8 _ (fun _i =>
    @Nat.decidableForallFin 8 _ (fun _j => inferInstance))

theorem mul_of_entries (a b c : Mat) (h : ProductEntries a b c) : a * b = c := by
  ext i j
  simpa [Matrix.mul_apply, Fin.sum_univ_succ, Fin.succ, add_assoc] using h i j

def inverseB : Mat := !![0,0,4,1,4,4,1,1;
0,0,1,4,1,1,0,3;
1,1,0,1,4,0,1,0;
1,1,0,1,0,1,1,4;
4,4,0,0,1,4,4,1;
1,1,0,0,0,2,1,4;
0,1,2,3,2,3,3,2;
0,1,2,3,2,2,0,0]

set_option maxRecDepth 10000 in
theorem b_inverse : octonionMatrixB * inverseB = 1 := by
  apply mul_of_entries
  decide +kernel

def letter (c : Char) : Atlas.G2.Model (ZMod 5) :=
  if c = 'a' then octonionGenerator false else
  if c = 'A' then (octonionGenerator false)⁻¹ else
  if c = 'b' then octonionGenerator true else (octonionGenerator true)⁻¹

def eval (w : List Char) : Mat := octonionMatrix ((w.map letter).prod)

theorem eval_append (u v : List Char) : eval (u ++ v) = eval u * eval v := by
  simp only [eval, List.map_append, List.prod_append, map_mul]

theorem append_certificate {u v w : List Char} {a b c : Mat}
    (hw : w = u ++ v) (hu : eval u = a) (hv : eval v = b)
    (hm : a * b = c) : eval w = c := by
  rw [hw, eval_append, hu, hv, hm]

theorem eval_a : eval "a".toList = octonionMatrixA := by
  simpa [eval, letter] using octonionMatrix_false

theorem eval_b : eval "b".toList = octonionMatrixB := by
  simpa [eval, letter] using octonionMatrix_true

theorem eval_B : eval "B".toList = inverseB := by
  have h : octonionMatrix (octonionGenerator true) * inverseB = 1 := by
    rw [octonionMatrix_true, b_inverse]
  have hh := congrArg (octonionMatrix (octonionGenerator true)⁻¹ * ·) h
  simp only [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul, mul_one] at hh
  simpa [eval, letter] using hh.symm

theorem eval_relator (i : Fin 22) :
    octonionMatrix (FreeGroup.lift octonionGenerator (relator i)) = eval (word i).toList := by
  rw [relator, FreeGroup.lift_mk]
  congr 1
  rw [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro c _
  simp only [Function.comp_apply, letter]
  by_cases ha : c = 'a' <;> by_cases hA : c = 'A' <;>
    by_cases hb : c = 'b' <;> simp [ha, hA, hb]
end G2Five.AtlasPresentation.RelationCertificate
