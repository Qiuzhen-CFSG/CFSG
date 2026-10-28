module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.Relations
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.FixedRootFactorization
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.RootCurve
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Normal generation of the fixed Suzuki-side Ree radical

The normal closure is taken inside the fixed Suzuki seed. The middle Weyl
word conjugates the eighth curve to the second. In the quotient by that
normal closure, `rootImages_eq_one` kills all seven radical curves. Actual
fixed-root factorization then kills the whole radical.

For the canonical local input and `m ≥ 1`, `radical_le_normalClosure`
discharges every premise using the proved split-coordinate bijection,
fixed-root factorization and literal matrix identities. In particular, the
fixed-factorization theorem uses uniqueness of split coordinates to make
each radical block fixed separately, then expresses its central parameters
using the main curves. The normal-generation argument also kills the fifth
curve, which belongs to the nonsplit first radical layer. The restriction
`m ≥ 1` supplies a scalar different from zero and one. No Suzuki projection,
perfectness or radical commutator inclusion is required.

Source: GLS3, 2.3.7, Table 2.4, 2.4.5(d), and the final Ree example in §3.2;
Aschbacher–Smith F.1.12(II)(i), printed pp.263–264 of `refs/quasithin.pdf`.
-/

public section

noncomputable section
namespace ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open LargeLocalSeeds Subgroup

private theorem exists_scalar {m : ℕ} (hm : 1 ≤ m) :
    ∃ c : CoefficientField m, c ≠ 0 ∧ c ≠ 1 := by
  classical
  by_contra! h
  have hsub : (Finset.univ : Finset (CoefficientField m)) ⊆ {0, 1} := by
    intro t _
    by_cases ht : t = 0
    · simp [ht]
    · simp [h t ht]
  have hcard := Finset.card_le_card hsub
  have hlarge : 2 ^ 3 ≤ 2 ^ (2 * m + 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  simp only [Finset.card_univ, Finset.card_insert_of_notMem (by simp :
    (0 : CoefficientField m) ∉ ({1} : Finset (CoefficientField m))),
    Finset.card_singleton, ← Nat.card_eq_fintype_card, field_card] at hcard
  omega

private theorem of_lifted_relations {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m)
    (x y : Fin 8 → CoefficientField m → standardSeed d .suzuki)
    (hrel : RootRelations m x y)
    (hgen : seedRadical d .suzuki ≤ closure {z | ∃ i : Fin 8, i ≠ 0 ∧
      ∃ t : CoefficientField m, z = x i t})
    (hend : ∀ t, x 7 t = endRootElement d t)
    (w : standardSeed d .suzuki)
    (hw : ∀ t, w * x 7 t * w⁻¹ = x 1 t) :
    seedRadical d .suzuki ≤ normalClosure (Set.range (endRootElement d)) := by
  let N := normalClosure (Set.range (endRootElement d))
  let q := QuotientGroup.mk' N
  have h8 (t) : q (x 7 t) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [hend]
    exact subset_normalClosure (Set.mem_range_self t)
  have h2 (t) : q (x 1 t) = 1 := by
    have hx : x 7 t ∈ N := (QuotientGroup.eq_one_iff _).mp (h8 t)
    have hh := (inferInstance : N.Normal).conj_mem (x 7 t) hx w
    rw [hw] at hh
    exact (QuotientGroup.eq_one_iff _).mpr hh
  obtain ⟨c, hc0, hc1⟩ := exists_scalar hm
  have hkill := rootImages_eq_one m c hc0 hc1 _ _ (hrel.map q) h2 h8
  apply hgen.trans
  apply (closure_le _).mpr
  rintro z ⟨i, hi, t, rfl⟩
  exact (QuotientGroup.eq_one_iff _).mp (hkill i hi t)

private def ofWord {m : ℕ} (d : LocalBlockInput m) (z : SplitGroup m)
    (hz : d.twist z = z ∧ z ∈ splitSeed m .suzuki) : standardSeed d .suzuki :=
  ⟨⟨z, hz.1⟩, hz.2⟩

/-- Conditional assembly for the actual matrix words. Fixed factorization and
the literal root identities must be supplied before this proves the requested
normal generation theorem for the canonical seed. -/
theorem radical_le_normalClosure_of_root_words {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m)
    (hroot : ∀ i t, d.twist (rootWord m i t) = rootWord m i t ∧
      rootWord m i t ∈ splitSeed m .suzuki)
    (hcentral : ∀ i t, d.twist (centralWord m i t) = centralWord m i t ∧
      centralWord m i t ∈ splitSeed m .suzuki)
    (hgen : ∀ z : SplitGroup m, z ∈ splitRadical m .suzuki → d.twist z = z →
      z ∈ closure {z | ∃ i : Fin 8, i ≠ 0 ∧ ∃ t : CoefficientField m,
        z = rootWord m i t})
    (hrel : RootRelations m (rootWord m) (centralWord m))
    (hwmem : d.twist (middleWeylWord m) = middleWeylWord m ∧
      middleWeylWord m ∈ splitSeed m .suzuki)
    (hw : ∀ t, middleWeylWord m * rootWord m 7 t * (middleWeylWord m)⁻¹ =
      rootWord m 1 t) :
    seedRadical d .suzuki ≤ normalClosure (Set.range (endRootElement d)) := by
  let x := fun i t => ofWord d (rootWord m i t) (hroot i t)
  let y := fun i t => ofWord d (centralWord m i t) (hcentral i t)
  let j : standardSeed d .suzuki →* SplitGroup m :=
    d.fixedGroup.subtype.comp (standardSeed d .suzuki).subtype
  have hj : Function.Injective j := Subtype.val_injective.comp Subtype.val_injective
  have hr : RootRelations m x y := RootRelations.of_injective j hj hrel
  refine of_lifted_relations hm d x y hr ?_ ?_ (ofWord d (middleWeylWord m) hwmem) ?_
  · let C := closure {z | ∃ i : Fin 8, i ≠ 0 ∧ ∃ t : CoefficientField m, z = x i t}
    have hC : closure {z | ∃ i : Fin 8, i ≠ 0 ∧ ∃ t : CoefficientField m,
        z = rootWord m i t} ≤ C.map j := by
      apply (closure_le _).mpr
      rintro z ⟨i, hi, t, rfl⟩
      exact ⟨x i t, subset_closure ⟨i, hi, t, rfl⟩, rfl⟩
    intro z hz
    obtain ⟨u, hu, he⟩ := hC (hgen (j z) hz z.val.property)
    exact hj he ▸ hu
  · intro t
    apply hj
    exact rootWord_end m t
  · intro t
    apply hj
    exact hw t

/-- Every element of the canonical fixed Suzuki radical lies in the normal
closure of the fixed end-root curve, taken inside the fixed Suzuki seed.
All fixed-factorization and matrix-relation premises are discharged. -/
theorem radical_le_normalClosure {m : ℕ} (hm : 1 ≤ m) :
    seedRadical (canonicalLocalBlockInput m) .suzuki ≤
      normalClosure (Set.range (endRootElement (canonicalLocalBlockInput m))) :=
  radical_le_normalClosure_of_root_words hm (canonicalLocalBlockInput m)
    (rootWord_fixed_mem_seed (canonicalLocalBlockInput m))
    (centralWord_fixed_mem_seed (canonicalLocalBlockInput m))
    (fixed_radical_mem_closure (canonicalLocalBlockInput m)
      (RadicalCoordinates.wordInSubgroup_bijective m))
    (rootWord_relations m)
    ⟨middleWeylWord_fixed m, middleWeylWord_mem_splitSeed m⟩
    (middleWeylWord_conjugate_end m)

end ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
