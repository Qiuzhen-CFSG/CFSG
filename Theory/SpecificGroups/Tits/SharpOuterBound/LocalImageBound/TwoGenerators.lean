module
public import Theory.SpecificGroups.Tits.SharpOuterBound.LocalRestrictions
public import Theory.SpecificGroups.Tits.OuterOddSubgroups.OverlapCentralizers.Packed

/-!
# Two generators for the marked Tits Sylow subgroup

Explicit positive words express all eight Parrott Sylow generators in `s3`
and `s8`. The equalities are checked on every point of the certified Atlas
permutations. The existing normal-form cover then proves that homomorphisms,
and in particular automorphisms, are determined by these two images.

Source: Parrott (1972), §5, p.683. The words were found by breadth-first
search in the certified permutations; the search is not trusted by the proof.
-/

@[expose] public section
namespace Tits.SharpOuterBound.LocalImageBound
open Subgroup ExceptionalParabolics
open OuterOddSubgroups.OverlapCentralizers

/-- The eight marked Sylow generators, in increasing subscript order. -/
def sylowGenerator (i : Fin 8) : S :=
  ⟨atlas1600ParrottAssignment (![.s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8] i), by
    rw [S, atlas1600SylowTwoSubgroup_eq]
    apply subset_closure
    fin_cases i <;> simp⟩

/-- Explicit words expressing the eight generators in `s3` and `s8`. -/
def generatorWord {G : Type*} [Monoid G] (x y : G) : Fin 8 → G :=
  ![x * x * y * x * x * y * x * x * y * x ^ 3 * y * x * x * y * x ^ 3 * y,
    x * y * x * y * x * y * x ^ 3 * y * x ^ 3 * y * x * y * x ^ 3 * y * x ^ 3 * y,
    x,
    x * x * y * x * x * y * x * x * y * x * x * y,
    x * x * y * x ^ 3 * y * x ^ 3 * y * x * y,
    x * y * x ^ 3 * y * x * y * x * x * y * x * y * x ^ 3 * y * x,
    y * x * y * x * x * y * x * y * x * y * x * y * x,
    y]

theorem map_generatorWord {G H : Type*} [Monoid G] [Monoid H]
    (f : G →* H) (x y : G) (i : Fin 8) :
    f (generatorWord x y i) = generatorWord (f x) (f y) i := by
  fin_cases i <;> simp [generatorWord]

private def sylowPerm : S →* Equiv.Perm (Fin 1600) where
  toFun x := x.val.val
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem sylowPerm_injective : Function.Injective sylowPerm := by
  intro x y h
  exact Subtype.ext (Subtype.ext h)

private theorem sylowPerm_generator (i : Fin 8) :
    sylowPerm (sylowGenerator i) = Packed.generator (⟨i.val + 2, by omega⟩ : Fin 10) := by
  change (atlas1600ParrottAssignment _).val = _
  fin_cases i <;> simp [atlas1600ParrottAssignment_val,
    Atlas1600ParrottData.permutation, Packed.generator]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem words_perm (i : Fin 8) :
    generatorWord (Packed.perm 4) (Packed.perm 9) i = Packed.perm (⟨i.val + 2, by omega⟩ : Fin 10) := by
  have h : ∀ (i : Fin 8) (p : Fin 1600),
      generatorWord (Packed.perm 4) (Packed.perm 9) i p = Packed.perm (⟨i.val + 2, by omega⟩ : Fin 10) p := by
    apply Atlas1600OrderCertificate.allFin₂
    decide +kernel
  exact Equiv.ext (h i)

theorem generatorWord_eq (i : Fin 8) :
    generatorWord (sylowGenerator 2) (sylowGenerator 7) i = sylowGenerator i := by
  apply sylowPerm_injective
  rw [map_generatorWord, sylowPerm_generator, sylowPerm_generator, sylowPerm_generator]
  simpa [Packed.perm_eq] using words_perm i

private theorem normal_form (n : Fin 2048) :
    atlas1600SylowTwoEquiv n =
    sylowGenerator 0 ^ (n.val % 2) * sylowGenerator 1 ^ (n.val / 2 % 2) *
    sylowGenerator 2 ^ (n.val / 4 % 4) * sylowGenerator 3 ^ (n.val / 16 % 2) *
    sylowGenerator 4 ^ (n.val / 32 % 4) * sylowGenerator 5 ^ (n.val / 128 % 2) *
    sylowGenerator 6 ^ (n.val / 256 % 4) * sylowGenerator 7 ^ (n.val / 1024 % 2) := by
  apply Subtype.ext
  rw [atlas1600SylowTwoEquiv_apply]
  exact atlas1600SylowTwoNormalForm_eq n

/-- Homomorphisms on the actual Sylow subgroup are determined by `s3` and `s8`. -/
theorem sylowHom_ext {G : Type*} [Monoid G] (f g : S →* G)
    (h3 : f (sylowGenerator 2) = g (sylowGenerator 2))
    (h8 : f (sylowGenerator 7) = g (sylowGenerator 7)) : f = g := by
  have hgen (i : Fin 8) : f (sylowGenerator i) = g (sylowGenerator i) := by
    rw [← generatorWord_eq i, map_generatorWord, map_generatorWord, h3, h8]
  apply MonoidHom.ext
  intro s
  obtain ⟨n, rfl⟩ := atlas1600SylowTwoEquiv.surjective s
  rw [normal_form]
  simp only [map_mul, map_pow, hgen]

/-- Normal-form indices of the images of the two generators. -/
noncomputable def generatorPair (f : MulAut S) : Fin 2048 × Fin 2048 :=
  (atlas1600SylowTwoEquiv.symm (f (sylowGenerator 2)),
    atlas1600SylowTwoEquiv.symm (f (sylowGenerator 7)))

theorem generatorPair_injective : Function.Injective generatorPair := by
  intro f g h
  have h3 := atlas1600SylowTwoEquiv.symm.injective (congrArg Prod.fst h)
  have h8 := atlas1600SylowTwoEquiv.symm.injective (congrArg Prod.snd h)
  have hh := sylowHom_ext f.toMonoidHom g.toMonoidHom h3 h8
  exact MulEquiv.toMonoidHom_injective hh

/-- Substitute a pair of group elements into the fixed Sylow normal-form words. -/
def normalFormWord {G : Type*} [Monoid G] (x y : G) (n : Fin 2048) : G :=
  generatorWord x y 0 ^ (n.val % 2) * generatorWord x y 1 ^ (n.val / 2 % 2) *
  generatorWord x y 2 ^ (n.val / 4 % 4) * generatorWord x y 3 ^ (n.val / 16 % 2) *
  generatorWord x y 4 ^ (n.val / 32 % 4) * generatorWord x y 5 ^ (n.val / 128 % 2) *
  generatorWord x y 6 ^ (n.val / 256 % 4) * generatorWord x y 7 ^ (n.val / 1024 % 2)

theorem map_normalFormWord {G H : Type*} [Monoid G] [Monoid H]
    (f : G →* H) (x y : G) (n : Fin 2048) :
    f (normalFormWord x y n) = normalFormWord (f x) (f y) n := by
  simp only [normalFormWord, map_mul, map_pow, map_generatorWord]

theorem normalFormWord_eq (n : Fin 2048) :
    normalFormWord (sylowGenerator 2) (sylowGenerator 7) n = atlas1600SylowTwoEquiv n := by
  simp only [normalFormWord, generatorWord_eq]
  exact (normal_form n).symm

/-- Evaluate a Sylow word after substituting the two proposed image indices. -/
noncomputable def pairEvaluation (p : Fin 2048 × Fin 2048) (n : Fin 2048) : S :=
  normalFormWord (atlas1600SylowTwoEquiv p.1) (atlas1600SylowTwoEquiv p.2) n

theorem pairEvaluation_generatorPair (f : MulAut S) (n : Fin 2048) :
    pairEvaluation (generatorPair f) n = f (atlas1600SylowTwoEquiv n) := by
  unfold pairEvaluation generatorPair
  simp only [Equiv.apply_symm_apply]
  simpa only [MulEquiv.coe_toMonoidHom, normalFormWord_eq] using
    (map_normalFormWord f.toMonoidHom (sylowGenerator 2) (sylowGenerator 7) n).symm

end Tits.SharpOuterBound.LocalImageBound
end
