module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.LocalCentralizers
public import Theory.SpecificGroups.Janko1.Model.Presentation
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SourceMatrices

/-!
# Constructing the full ATLAS pair from normalized source matrices

An injective seven-dimensional representation containing Janko's original
matrices supplies a nontrivial pair satisfying all five ATLAS relators.
The words and their matrix calculations are certified in `SourceMatrices`;
this module proves the transfer through the literal representation and any
change of basis. It uses no generation or presentation-bound premise.

This is a conditional step toward Aschbacher–Smith I.4.9, printed p.418.
The original local hypotheses have not yet been used to construct the
representation or its normalization, so the unconditional source-side pair
existence theorem remains unproved. Gorenstein, *Finite Groups*, §16.6,
pp.482–483, describes the two preceding parts of Janko's argument: the
characteristic-eleven representation and the local configuration used to
normalize its matrices. See `RelatorPair/Source/README.md` for the precise
remaining mathematical contracts and source-access limitations.
-/

namespace CFSG.Quasithin.Janko1RelatorPair
variable {G : Type*} [Group G]

private theorem pair_of_mapped_relations {M : Type*} [Monoid M]
    (f : G →* M) (hf : Function.Injective f) (a b : G) (hne : f a ≠ 1)
    (hrel : (f a) ^ 2 = 1 ∧ (f b) ^ 3 = 1 ∧ (f a * f b) ^ 7 = 1 ∧
      (f a * f b * (f a * f b * f a * (f b) ^ 2) ^ 3) ^ 5 = 1 ∧
      (f a * f b * (f a * f b * f a * (f b) ^ 2) ^ 6 * f a * f b *
        f a * f b * (f a * (f b) ^ 2) ^ 2) ^ 2 = 1) :
    a ≠ 1 ∧ ∀ i : Fin 5, Janko1.atlasWord a b i = 1 := by
  obtain ⟨h2, h3, h7, h4, h5⟩ := hrel
  have hb3 : b ^ 3 = 1 := by
    apply hf
    simpa only [map_pow, map_one] using h3
  have hbi : b⁻¹ = b ^ 2 :=
    inv_eq_of_mul_eq_one_left (by simpa only [← pow_succ] using hb3)
  constructor
  · intro heq
    exact hne (by rw [heq, map_one])
  · intro i
    fin_cases i
    · change a ^ 2 = 1
      apply hf
      simpa only [map_pow, map_one] using h2
    · change b ^ 3 = 1
      exact hb3
    · change (a * b) ^ 7 = 1
      apply hf
      simpa only [map_mul, map_pow, map_one] using h7
    · change (a * b * (a * b * a * b⁻¹) ^ 3) ^ 5 = 1
      apply hf
      simpa only [hbi, map_mul, map_pow, map_one] using h4
    · change (a * b * (a * b * a * b⁻¹) ^ 6 * a * b * a * b * (a * b⁻¹) ^ 2) ^ 2 = 1
      apply hf
      simpa only [hbi, map_mul, map_pow, map_one] using h5

/-- The certified source words give the full ATLAS pair in every group
with an injective representation containing the two original matrices. -/
public theorem exists_atlas_pair_of_source_matrix_images
    (ρ : G →* Janko1.Ambient) (hρ : Function.Injective ρ) (y v : G)
    (hy : (ρ y : Matrix (Fin 7) (Fin 7) (ZMod 11)) = sourceY)
    (hv : (ρ v : Matrix (Fin 7) (Fin 7) (ZMod 11)) = sourceV) :
    ∃ a b : G, a ≠ 1 ∧ ∀ i : Fin 5, Janko1.atlasWord a b i = 1 := by
  let f : G →* Matrix (Fin 7) (Fin 7) (ZMod 11) := (Units.coeHom _).comp ρ
  have hf : Function.Injective f := fun _ _ h => hρ (Units.ext h)
  have hfy : f y = sourceY := hy
  have hfv : f v = sourceV := hv
  let a := firstWord y v
  let b := secondWord y v
  have ha : f a = firstWord sourceY sourceV := by
    simp only [a, firstWord, map_mul, map_pow, hfy, hfv]
  have hb : f b = secondWord sourceY sourceV := by
    simp only [b, secondWord, map_mul, map_pow, hfy, hfv]
  refine ⟨a, b, pair_of_mapped_relations f hf a b ?_ ?_⟩
  · rw [ha]
    exact source_firstWord_ne_one
  · rw [ha, hb]
    exact source_matrix_relations


/-- A change of basis in the supplied representation preserves the construction.
This is the consumer of the source matrix-normalization statement. -/
public theorem exists_atlas_pair_of_conjugated_source_matrix_images
    (ρ : G →* Janko1.Ambient) (hρ : Function.Injective ρ)
    (c : Janko1.Ambient) (y v : G)
    (hy : (c * ρ y * c⁻¹ : Matrix (Fin 7) (Fin 7) (ZMod 11)) = sourceY)
    (hv : (c * ρ v * c⁻¹ : Matrix (Fin 7) (Fin 7) (ZMod 11)) = sourceV) :
    ∃ a b : G, a ≠ 1 ∧ ∀ i : Fin 5, Janko1.atlasWord a b i = 1 := by
  let f : G →* Janko1.Ambient := (MulAut.conj c).toMonoidHom.comp ρ
  apply exists_atlas_pair_of_source_matrix_images f ((MulAut.conj c).injective.comp hρ) y v
  · exact hy
  · exact hv
end CFSG.Quasithin.Janko1RelatorPair
