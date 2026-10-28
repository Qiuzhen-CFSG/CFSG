module
public import Theory.SpecificGroups.SymplecticFour.RootPresentation.Chambers
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group

/-!
# Weyl conjugation from the explicit C₂ relations

The simple root groups normalize the subgroup on the remaining three
positive roots. Matrix evaluation is faithful on that chamber, so the
concrete Weyl formulas imply their abstract counterparts there. Reindexing
by the orthogonal reflection treats the negative half of the root system.
Finally the crossing equation expresses each simple root using nonopposite
roots; its conjugate lies in another faithful chamber. Thus both opposite
root formulas follow without imposing any rank-one relation.

The result holds for every group with the stated eight-root relations over
a finite characteristic-two field, including fields of orders two and four.
The parameter-one Weyl identities are proved here; global presentation
faithfulness still requires the parameter, torus, and Bruhat arguments.

Source: Steinberg, Lectures on Chevalley Groups, §6, Lemmas 36–37,
printed pp.69–70 (`refs/KGroup/GLS3/Chapter2St1.tex`).
-/

@[expose] public noncomputable section
open Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.RootPresentation
open PositiveRelations
variable {F E : Type*} [Field F] [Group E]

def rootSpan (x : Fin 8 → F → E) (s : Set (Fin 8)) : Subgroup E :=
  closure {g | ∃ r ∈ s, ∃ t, x r t = g}

omit [Field F] in
theorem root_mem_span (x : Fin 8 → F → E) {s : Set (Fin 8)} {r : Fin 8}
    (hr : r ∈ s) (t : F) : x r t ∈ rootSpan x s := subset_closure ⟨r,hr,t,rfl⟩

variable [CharP F 2]

theorem PositiveRelations.inv {x : Fin 8 → F → E} (h : PositiveRelations x)
    (r : Fin 8) (t : F) : (x r t)⁻¹ = x r t := by
  apply inv_eq_of_mul_eq_one_left
  rw [h.add, CharTwo.add_self_eq_zero, h.zero]

private theorem mem_normalizer_of_involution {H : Subgroup E} {a : E}
    (ha : a⁻¹ = a) (h : ∀ g ∈ H, a * g * a⁻¹ ∈ H) : a ∈ normalizer H := by
  rw [mem_normalizer_iff]
  intro g
  refine ⟨h g, fun hg => ?_⟩
  have hs : a * a = 1 := by simpa only [ha] using inv_mul_cancel a
  simpa only [ha, mul_assoc, ← mul_assoc a a, hs, one_mul, mul_one] using h _ hg

private theorem root_normalizes_span {x : Fin 8 → F → E} (h : PositiveRelations x)
    (s : Set (Fin 8)) (r : Fin 8) (t : F)
    (hc : ∀ j ∈ s, ∀ u, x r t * x j u * (x r t)⁻¹ ∈ rootSpan x s) :
    x r t ∈ normalizer (rootSpan x s) := by
  apply mem_normalizer_of_involution (h.inv r t)
  have hh : rootSpan x s ≤ (rootSpan x s).comap (MulAut.conj (x r t)).toMonoidHom := by
    apply (closure_le _).mpr
    rintro _ ⟨j,hj,u,rfl⟩
    exact hc j hj u
  exact fun _ hg => hh hg

private theorem commute_conj {a b : E} (h : Commute a b) : a * b * a⁻¹ = b := by
  rw [h.eq, mul_inv_cancel_right]

/-- Each simple positive root normalizes the other three positive roots. -/
theorem PositiveRelations.long_normalizes {x : Fin 8 → F → E}
    (h : PositiveRelations x) (v : F) :
    x 2 v ∈ normalizer (rootSpan x {6,0,4}) := by
  apply root_normalizes_span h
  intro j hj c
  rcases hj with rfl | rfl | rfl
  · rw [h.crossing, mul_inv_cancel_right]
    exact mul_mem (mul_mem (root_mem_span x (by simp) c)
      (root_mem_span x (by simp) (c^2*v))) (root_mem_span x (by simp) (c*v))
  · rw [commute_conj (show Commute (x 2 v) (x 0 c) from (h.commuting 3 c v).symm)]
    exact root_mem_span x (by simp) c
  · rw [commute_conj (show Commute (x 2 v) (x 4 c) from (h.commuting 4 c v).symm)]
    exact root_mem_span x (by simp) c

theorem PositiveRelations.short_normalizes {x : Fin 8 → F → E}
    (h : PositiveRelations x) (c : F) :
    x 6 c ∈ normalizer (rootSpan x {0,4,2}) := by
  apply root_normalizes_span h
  intro j hj v
  rcases hj with rfl | rfl | rfl
  · rw [commute_conj (show Commute (x 6 c) (x 0 v) from h.commuting 0 c v)]
    exact root_mem_span x (by simp) v
  · rw [commute_conj (show Commute (x 6 c) (x 4 v) from h.commuting 1 c v)]
    exact root_mem_span x (by simp) v
  · have he : x 6 c * x 2 v * (x 6 c)⁻¹ = x 0 (c^2*v) * x 4 (c*v) * x 2 v := by
      calc
        _ = (x 6 c)⁻¹ * (x 2 v * x 6 c) := by rw [h.inv]; simp only [mul_assoc]
        _ = _ := by rw [h.crossing, ← mul_assoc, ← mul_assoc, inv_mul_cancel_left]
    rw [he]
    exact mul_mem (mul_mem (root_mem_span x (by simp) (c^2*v))
      (root_mem_span x (by simp) (c*v))) (root_mem_span x (by simp) v)


omit [CharP F 2] in
theorem Relations.reindex {x : Fin 8 → F → E} (h : Relations x)
    (σ : Equiv.Perm (Fin 8)) (hσ : σ ∈ weyl) : Relations (fun r t => x (σ r) t) :=
  fun τ hτ => h (σ * τ) (weyl.mul_mem hσ hτ)

omit [Field F] [CharP F 2] in
theorem rootSpan_reindex (x : Fin 8 → F → E) (σ : Equiv.Perm (Fin 8))
    (s : Set (Fin 8)) : rootSpan (fun r t => x (σ r) t) s = rootSpan x (σ '' s) := by
  unfold rootSpan
  congr 1
  ext g
  constructor
  · rintro ⟨r,hr,t,ht⟩
    exact ⟨σ r,⟨r,hr,rfl⟩,t,ht⟩
  · rintro ⟨_,⟨r,hr,rfl⟩,t,ht⟩
    exact ⟨r,hr,t,ht⟩

theorem shortReflection_mem : shortReflection ∈ weyl := subset_closure (by simp)
theorem longReflection_mem : longReflection ∈ weyl := subset_closure (by simp)

/-- The word implementing the short simple reflection; its parameter is arbitrary. -/
def shortWord (x : Fin 8 → F → E) (t : F) := x 6 t * x 7 t⁻¹ * x 6 t

/-- The word implementing the long simple reflection. -/
def longWord (x : Fin 8 → F → E) (t : F) := x 2 t * x 3 t⁻¹ * x 2 t

theorem Relations.shortWord_normalizes {x : Fin 8 → F → E} (h : Relations x) (t : F) :
    shortWord x t ∈ normalizer (rootSpan x {0,4,2}) := by
  have hn := (h shortReflection shortReflection_mem).short_normalizes t⁻¹
  rw [rootSpan_reindex] at hn
  have he : shortReflection '' ({0,4,2} : Set (Fin 8)) = {0,4,2} := by
    ext r
    fin_cases r <;> simp [Set.image_insert_eq, Set.image_singleton, shortReflection, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  rw [he] at hn
  change x 7 t⁻¹ ∈ normalizer (rootSpan x {0,4,2}) at hn
  exact mul_mem (mul_mem (h.positive.short_normalizes t) hn) (h.positive.short_normalizes t)

theorem Relations.longWord_normalizes {x : Fin 8 → F → E} (h : Relations x) (t : F) :
    longWord x t ∈ normalizer (rootSpan x {6,0,4}) := by
  have hn := (h longReflection longReflection_mem).long_normalizes t⁻¹
  rw [rootSpan_reindex] at hn
  have he : longReflection '' ({6,0,4} : Set (Fin 8)) = {6,0,4} := by
    ext r
    fin_cases r <;> simp [Set.image_insert_eq, Set.image_singleton, longReflection, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  rw [he] at hn
  change x 3 t⁻¹ ∈ normalizer (rootSpan x {6,0,4}) at hn
  exact mul_mem (mul_mem (h.positive.long_normalizes t) hn) (h.positive.long_normalizes t)


omit [Field F] [CharP F 2] in
theorem rootSpan_mono (x : Fin 8 → F → E) {s t : Set (Fin 8)} (hst : s ⊆ t) :
    rootSpan x s ≤ rootSpan x t := by
  apply closure_mono
  rintro _ ⟨r,hr,u,rfl⟩
  exact ⟨r,hst hr,u,rfl⟩

variable [Finite F]

private theorem generator_shortWord_positive (r : Fin 8) (hr : r ∈ ({0,4,2} : Set (Fin 8))) (u : F) :
    shortWord generator (1 : F) * generator r u * (shortWord generator (1 : F))⁻¹ =
      generator (shortReflection r) u := by
  have hs : rootSpan (generator (F := F)) {0,4,2} ≤ positiveSubgroup generator :=
    rootSpan_mono _ (by intro j hj; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj ⊢; tauto)
  apply matrixMap_injective_on_positive
  · exact hs ((mem_normalizer_iff.mp (generator_relations.shortWord_normalizes 1) _).mp
      (root_mem_span _ hr u))
  · apply hs
    apply root_mem_span
    rcases hr with rfl | rfl | rfl <;> decide
  · simp only [map_mul, map_inv, shortWord, matrixMap_generator, inv_one]
    exact mul_inv_eq_iff_eq_mul.mpr (shortWeyl_root r u)

private theorem generator_longWord_positive (r : Fin 8) (hr : r ∈ ({6,0,4} : Set (Fin 8))) (u : F) :
    longWord generator (1 : F) * generator r u * (longWord generator (1 : F))⁻¹ =
      generator (longReflection r) u := by
  have hs : rootSpan (generator (F := F)) {6,0,4} ≤ positiveSubgroup generator :=
    rootSpan_mono _ (by intro j hj; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj ⊢; tauto)
  apply matrixMap_injective_on_positive
  · exact hs ((mem_normalizer_iff.mp (generator_relations.longWord_normalizes 1) _).mp
      (root_mem_span _ hr u))
  · apply hs
    apply root_mem_span
    rcases hr with rfl | rfl | rfl <;> decide
  · simp only [map_mul, map_inv, longWord, matrixMap_generator, inv_one]
    exact mul_inv_eq_iff_eq_mul.mpr (longWeyl_root r u)

theorem Relations.shortWord_positive {x : Fin 8 → F → E} (h : Relations x)
    (r : Fin 8) (hr : r ∈ ({0,4,2} : Set (Fin 8))) (u : F) :
    shortWord x 1 * x r u * (shortWord x 1)⁻¹ = x (shortReflection r) u := by
  simpa only [shortWord, map_mul, map_inv, lift_generator]
    using congrArg (lift h) (generator_shortWord_positive r hr u)

theorem Relations.longWord_positive {x : Fin 8 → F → E} (h : Relations x)
    (r : Fin 8) (hr : r ∈ ({6,0,4} : Set (Fin 8))) (u : F) :
    longWord x 1 * x r u * (longWord x 1)⁻¹ = x (longReflection r) u := by
  simpa only [longWord, map_mul, map_inv, lift_generator]
    using congrArg (lift h) (generator_longWord_positive r hr u)


private theorem bab_mem : longReflection * shortReflection * longReflection ∈ weyl :=
  weyl.mul_mem (weyl.mul_mem longReflection_mem shortReflection_mem) longReflection_mem

private theorem aba_mem : shortReflection * longReflection * shortReflection ∈ weyl :=
  weyl.mul_mem (weyl.mul_mem shortReflection_mem longReflection_mem) shortReflection_mem

theorem Relations.shortWord_nonopposite {x : Fin 8 → F → E} (h : Relations x)
    (r : Fin 8) (hr : r ≠ 6) (hr' : r ≠ 7) (u : F) :
    shortWord x 1 * x r u * (shortWord x 1)⁻¹ = x (shortReflection r) u := by
  have hn := (h.reindex _ bab_mem).shortWord_positive
  fin_cases r
  · exact h.shortWord_positive 0 (by simp) u
  · simpa [shortWord, shortReflection, longReflection, Equiv.Perm.mul_apply, Equiv.swap_apply_def] using hn 2 (by simp) u
  · exact h.shortWord_positive 2 (by simp) u
  · simpa [shortWord, longWord, shortReflection, longReflection, Equiv.Perm.mul_apply, Equiv.swap_apply_def] using hn 0 (by simp) u
  · exact h.shortWord_positive 4 (by simp) u
  · simpa [shortWord, longWord, shortReflection, longReflection, Equiv.Perm.mul_apply, Equiv.swap_apply_def] using hn 4 (by simp) u
  · exact (hr rfl).elim
  · exact (hr' rfl).elim

theorem Relations.longWord_nonopposite {x : Fin 8 → F → E} (h : Relations x)
    (r : Fin 8) (hr : r ≠ 2) (hr' : r ≠ 3) (u : F) :
    longWord x 1 * x r u * (longWord x 1)⁻¹ = x (longReflection r) u := by
  have hn := (h.reindex _ aba_mem).longWord_positive
  fin_cases r
  · exact h.longWord_positive 0 (by simp) u
  · simpa [shortWord, longWord, shortReflection, longReflection, Equiv.Perm.mul_apply, Equiv.swap_apply_def] using hn 0 (by simp) u
  · exact (hr rfl).elim
  · exact (hr' rfl).elim
  · exact h.longWord_positive 4 (by simp) u
  · simpa [longWord, shortReflection, longReflection, Equiv.Perm.mul_apply, Equiv.swap_apply_def] using hn 6 (by simp) u
  · exact h.longWord_positive 6 (by simp) u
  · simpa [shortWord, longWord, shortReflection, longReflection, Equiv.Perm.mul_apply, Equiv.swap_apply_def] using hn 4 (by simp) u

omit [Finite F] [CharP F 2] in
theorem PositiveRelations.isolate_long {x : Fin 8 → F → E} (h : PositiveRelations x)
    (v c : F) : x 0 (c^2*v) =
      (x 6 c)⁻¹ * x 2 v * x 6 c * (x 2 v)⁻¹ * (x 4 (c*v))⁻¹ := by
  symm
  calc
    _ = (x 6 c)⁻¹ * (x 2 v * x 6 c) * (x 2 v)⁻¹ * (x 4 (c*v))⁻¹ := by group
    _ = _ := by rw [h.crossing]; group

omit [Finite F] [CharP F 2] in
theorem PositiveRelations.isolate_short {x : Fin 8 → F → E} (h : PositiveRelations x)
    (v c : F) : x 4 (c*v) =
      (x 0 (c^2*v))⁻¹ * (x 6 c)⁻¹ * x 2 v * x 6 c * (x 2 v)⁻¹ := by
  symm
  calc
    _ = (x 0 (c^2*v))⁻¹ * (x 6 c)⁻¹ * (x 2 v * x 6 c) * (x 2 v)⁻¹ := by group
    _ = _ := by rw [h.crossing]; group

private theorem generator_shortWord_simple (u : F) :
    shortWord generator (1 : F) * generator 6 u * (shortWord generator (1 : F))⁻¹ =
      generator 7 u := by
  let σ := shortReflection * longReflection
  have hσ : σ ∈ weyl := weyl.mul_mem shortReflection_mem longReflection_mem
  let H := positiveSubgroup (fun r t => generator (F := F) (σ r) t)
  have hmem (r : Fin 8) (hr : r ∈ ({6,0,4,2} : Set (Fin 8))) (t : F) :
      generator (σ r) t ∈ H := root_mem_span _ hr t
  have hfactor : generator 6 u = (generator 0 u)⁻¹ * (generator 4 1)⁻¹ *
      generator 3 u * generator 4 1 * (generator 3 u)⁻¹ := by
    simpa [shortReflection, longReflection, Equiv.Perm.mul_apply, Equiv.swap_apply_def] using
      (generator_relations longReflection longReflection_mem).isolate_short u (1 : F)
  let a := MulAut.conj (shortWord generator (1 : F))
  have hc (r : Fin 8) (hr : r ≠ 6) (hr' : r ≠ 7) (t : F) :
      a (generator r t) = generator (shortReflection r) t :=
    generator_relations.shortWord_nonopposite r hr hr' t
  apply matrixMap_injective_on_chamber σ hσ
  · change a (generator 6 u) ∈ H
    rw [hfactor]
    simp only [map_mul, map_inv, hc 0 (by decide) (by decide), hc 4 (by decide) (by decide),
      hc 3 (by decide) (by decide)]
    exact mul_mem (mul_mem (mul_mem (mul_mem (inv_mem (hmem 0 (by simp) u))
      (inv_mem (hmem 6 (by simp) 1))) (hmem 2 (by simp) u)) (hmem 6 (by simp) 1))
      (inv_mem (hmem 2 (by simp) u))
  · exact hmem 4 (by simp) u
  · simp only [map_mul, map_inv, shortWord, matrixMap_generator, inv_one]
    exact mul_inv_eq_iff_eq_mul.mpr (shortWeyl_root 6 u)

private theorem generator_longWord_simple (u : F) :
    longWord generator (1 : F) * generator 2 u * (longWord generator (1 : F))⁻¹ =
      generator 3 u := by
  let σ := longReflection * shortReflection
  have hσ : σ ∈ weyl := weyl.mul_mem longReflection_mem shortReflection_mem
  let H := positiveSubgroup (fun r t => generator (F := F) (σ r) t)
  have hmem (r : Fin 8) (hr : r ∈ ({6,0,4,2} : Set (Fin 8))) (t : F) :
      generator (σ r) t ∈ H := root_mem_span _ hr t
  have hfactor : generator 2 u = (generator 7 1)⁻¹ * generator 0 u *
      generator 7 1 * (generator 0 u)⁻¹ * (generator 4 u)⁻¹ := by
    simpa [shortReflection, longReflection, Equiv.Perm.mul_apply, Equiv.swap_apply_def] using
      (generator_relations shortReflection shortReflection_mem).isolate_long u (1 : F)
  let a := MulAut.conj (longWord generator (1 : F))
  have hc (r : Fin 8) (hr : r ≠ 2) (hr' : r ≠ 3) (t : F) :
      a (generator r t) = generator (longReflection r) t :=
    generator_relations.longWord_nonopposite r hr hr' t
  apply matrixMap_injective_on_chamber σ hσ
  · change a (generator 2 u) ∈ H
    rw [hfactor]
    simp only [map_mul, map_inv, hc 7 (by decide) (by decide), hc 0 (by decide) (by decide),
      hc 4 (by decide) (by decide)]
    exact mul_mem (mul_mem (mul_mem (mul_mem (inv_mem (hmem 6 (by simp) 1))
      (hmem 2 (by simp) u)) (hmem 6 (by simp) 1)) (inv_mem (hmem 2 (by simp) u)))
      (inv_mem (hmem 4 (by simp) u))
  · exact hmem 0 (by simp) u
  · simp only [map_mul, map_inv, longWord, matrixMap_generator, inv_one]
    exact mul_inv_eq_iff_eq_mul.mpr (longWeyl_root 2 u)


omit [Finite F] in
theorem PositiveRelations.shortWord_inv {x : Fin 8 → F → E} (h : PositiveRelations x)
    (t : F) : (shortWord x t)⁻¹ = shortWord x t := by
  simp only [shortWord, mul_inv_rev, h.inv, mul_assoc]

omit [Finite F] in
theorem PositiveRelations.longWord_inv {x : Fin 8 → F → E} (h : PositiveRelations x)
    (t : F) : (longWord x t)⁻¹ = longWord x t := by
  simp only [longWord, mul_inv_rev, h.inv, mul_assoc]

private theorem conjugate_involution {a b c : E} (ha : a⁻¹ = a)
    (h : a * b * a⁻¹ = c) : a * c * a⁻¹ = b := by
  have hs : a * a = 1 := by simpa only [ha] using inv_mul_cancel a
  rw [← h]
  simp only [ha, mul_assoc, ← mul_assoc a a, hs, one_mul, mul_one]

/-- Both opposite-root formulas follow from the actual crossing relation and
faithfulness of its chamber; no rank-one relation is added to the presentation. -/
theorem Relations.shortWord_one_conj {x : Fin 8 → F → E} (h : Relations x)
    (r : Fin 8) (u : F) :
    shortWord x 1 * x r u * (shortWord x 1)⁻¹ = x (shortReflection r) u := by
  have h6 : shortWord x 1 * x 6 u * (shortWord x 1)⁻¹ = x 7 u := by
    simpa only [shortWord, map_mul, map_inv, lift_generator]
      using congrArg (lift h) (generator_shortWord_simple u)
  have h7 := conjugate_involution (h.positive.shortWord_inv 1) h6
  by_cases h6' : r = 6
  · subst r
    exact h6
  by_cases h7' : r = 7
  · subst r
    exact h7
  exact h.shortWord_nonopposite r h6' h7' u

theorem Relations.longWord_one_conj {x : Fin 8 → F → E} (h : Relations x)
    (r : Fin 8) (u : F) :
    longWord x 1 * x r u * (longWord x 1)⁻¹ = x (longReflection r) u := by
  have h2 : longWord x 1 * x 2 u * (longWord x 1)⁻¹ = x 3 u := by
    simpa only [longWord, map_mul, map_inv, lift_generator]
      using congrArg (lift h) (generator_longWord_simple u)
  have h3 := conjugate_involution (h.positive.longWord_inv 1) h2
  by_cases h2' : r = 2
  · subst r
    exact h2
  by_cases h3' : r = 3
  · subst r
    exact h3
  exact h.longWord_nonopposite r h2' h3' u

end Theory.SpecificGroups.SymplecticFour.RootPresentation
