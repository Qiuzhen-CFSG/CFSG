module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.Conjugation
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.Geometry

/-!
# Stabilizers of the two actual source pairs

For an action on two distinct factors, fixing either factor fixes both.
Thus their relative normalizers in T agree. The original swapping element
gives index two for each pair, so their common stabilizer T₀ has index at
most four. The actual Baumann subgroup lies in both stabilizers.

These deductions supply the complete factor-action and index hypotheses
of the maximal contrary Sylow choice in 15.4.20, on the same raw Geometry
used by 15.4.19. No overgroup Sylow conclusion is an input.

Source: Aschbacher–Smith, printed pp.1162–1164, 15.4.18–20.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
open FamilySource FamilySource.ModuleStructure
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M M₁ M₂ X Y : Subgroup G}

private theorem perm_bool_fixes_all (σ : Equiv.Perm Bool) (i : Bool) :
    σ i = i ↔ ∀ j, σ j = j := by
  revert σ i
  decide

/-- The same subgroup of T stabilizes either member of the actual pair. -/
theorem Pair.normalizer_eq (p : Pair T M X) (hTM : (T : Subgroup G) ≤ M) (i : Bool) :
    (T : Subgroup G) ⊓ normalizer (p.quotient.factor i : Set G) =
      (T : Subgroup G) ⊓ normalizer (p.quotient.factor false : Set G) := by
  ext t
  constructor <;> intro ht
  · refine ⟨ht.1, ?_⟩
    let m : M := ⟨t, hTM ht.1⟩
    have hi : p.quotient.action.permutation m i = i :=
      p.quotient.action.distinct ((p.quotient.action.conjugation m i).symm.trans
        (mem_normalizer_iff_map_conj_eq.mp ht.2))
    exact mem_normalizer_iff_map_conj_eq.mpr
      ((p.quotient.action.conjugation m false).trans
        (congrArg p.quotient.factor ((perm_bool_fixes_all _ i).mp hi false)))
  · refine ⟨ht.1, ?_⟩
    let m : M := ⟨t, hTM ht.1⟩
    have hi : p.quotient.action.permutation m false = false :=
      p.quotient.action.distinct ((p.quotient.action.conjugation m false).symm.trans
        (mem_normalizer_iff_map_conj_eq.mp ht.2))
    exact mem_normalizer_iff_map_conj_eq.mpr
      ((p.quotient.action.conjugation m i).trans
        (congrArg p.quotient.factor ((perm_bool_fixes_all _ false).mp hi i)))

/-- Any subgroup of the first relative stabilizer normalizes both factors. -/
theorem Pair.normalizes (p : Pair T M X) (hTM : (T : Subgroup G) ≤ M)
    {U : Subgroup G} (hUT : U ≤ (T : Subgroup G))
    (hU : U ≤ normalizer (p.quotient.factor false : Set G)) (i : Bool) :
    U ≤ normalizer (p.quotient.factor i : Set G) := by
  have hle := le_inf hUT hU
  rw [← p.normalizer_eq hTM i] at hle
  exact hle.trans inf_le_right

/-- The original T-interchange has stabilizer of index two. -/
theorem Pair.stabilizer_index (p : Pair T M X) (h : Input K T M X 2) :
    ((T : Subgroup G) ⊓ normalizer (p.quotient.factor false : Set G)).relIndex T = 2 := by
  obtain ⟨t, ht, _, _, hn⟩ := p.quotient.interchange
  exact (p.quotient.action.restrict h.sylow_le).stabilizer_index ht hn

/-- The source Baumann subgroup is contained in the common stabilizer. -/
theorem baumann_le_geometry_T₀ (pX : Pair T M₁ X) (pY : Pair T M₂ Y) :
    ChapterB.baumann (T : Subgroup G) ≤ (geometry pX pY).T₀ :=
  le_inf (le_inf inf_le_left (pX.baumann false)) (pY.baumann false)

/-- The common stabilizer has index at most four in the original T. -/
theorem geometry_T₀_index (hX : Input K T M₁ X 2) (hY : Input K T M₂ Y 2)
    (pX : Pair T M₁ X) (pY : Pair T M₂ Y) :
    (geometry pX pY).T₀.relIndex T ≤ 4 :=
  T₀_relIndex_le_four (geometry pX pY) (pX.stabilizer_index hX) (pY.stabilizer_index hY)

/-- The maximal contrary Sylow choice follows on the exact source geometry.
Only the earlier Baumann-normalizer controls and maximal-local uniqueness
remain explicit; all permutation, stabilizer and index inputs are derived. -/
theorem exists_source_maximal_sylow_counterexample
    (hX : Input K T M₁ X 2) (hY : Input K T M₂ Y 2)
    (pX : Pair T M₁ X) (pY : Pair T M₂ Y)
    (hM₁ : normalizer (X : Set G) = M₁) (hM₂ : normalizer (Y : Set G) = M₂)
    (hS₁ : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M₁)
    (hS₂ : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M₂)
    (huniqueX : ∀ M : Subgroup G, IsMaximalTwoLocal M → X ⊔ (T : Subgroup G) ≤ M → M = M₁)
    (huniqueY : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y ⊔ (T : Subgroup G) ≤ M → M = M₂)
    (hne : M₁ ≠ M₂)
    (hfail : ∃ i j, ∃ H ∈ Chapter1.HOver G ((geometry pX pY).I i j : Set G),
      ¬ ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = (geometry pX pY).T₀) :
    let d := geometry pX pY
    ∃ i j, ∃ H ∈ Chapter1.HOver G (d.I i j : Set G), ∃ U : Subgroup G,
      d.T₀ < U ∧ U < (T : Subgroup G) ∧ U ≤ H ∧ IsPGroup 2 U ∧
      (∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = U) ∧
      (∀ A ∈ Chapter1.HOver G (d.I i j : Set G), ∀ P : Sylow 2 A,
        Nat.card ((P : Subgroup A).map A.subtype) ≤ Nat.card U) ∧
      (∀ A ∈ Chapter1.HOver G (H : Set G),
        ∃ P : Sylow 2 A, (P : Subgroup A).map A.subtype = U) ∧
      (∃ P : Sylow 2 (normalizer (H.pCoreIn 2 : Set G)),
        (P : Subgroup (normalizer (H.pCoreIn 2 : Set G))).map
          (normalizer (H.pCoreIn 2 : Set G)).subtype = U) ∧
      U.relIndex (T : Subgroup G) = 2 ∧ d.T₀.relIndex U = 2 ∧
      (¬ U ≤ normalizer (d.X i : Set G) ∨ ¬ U ≤ normalizer (d.Y j : Set G)) := by
  let d := geometry pX pY
  have ht : d.T = T := rfl
  have hx : d.wholeX = X := pX.quotient.factor_generate hX
  have hy : d.wholeY = Y := pY.quotient.factor_generate hY
  have hm₁ : d.M₁ = M₁ := by change normalizer (d.wholeX : Set G) = M₁; rw [hx, hM₁]
  have hm₂ : d.M₂ = M₂ := by change normalizer (d.wholeY : Set G) = M₂; rw [hy, hM₂]
  apply exists_placed_maximal_sylow_counterexample d (baumann_le_geometry_T₀ pX pY)
    (hm₁.symm ▸ hS₁) (hm₂.symm ▸ hS₂)
  · exact pX.normalizes hX.sylow_le d.T₀_le_T (inf_le_left.trans inf_le_right)
  · exact pY.normalizes hY.sylow_le d.T₀_le_T inf_le_right
  · intro g hg
    have hgM : g ∈ M₁ := hm₁ ▸ hg
    exact ⟨pX.quotient.action.permutation ⟨g, hgM⟩, pX.quotient.action.conjugation ⟨g, hgM⟩⟩
  · intro g hg
    have hgM : g ∈ M₂ := hm₂ ▸ hg
    exact ⟨pY.quotient.action.permutation ⟨g, hgM⟩, pY.quotient.action.conjugation ⟨g, hgM⟩⟩
  · exact pX.normalizer_eq hX.sylow_le
  · exact pY.normalizer_eq hY.sylow_le
  · exact geometry_T₀_index hX hY pX pY
  · intro i
    rw [hx]
    exact pX.factor_join_sylow hX i
  · intro i
    rw [hy]
    exact pY.factor_join_sylow hY i
  · simpa only [hx, hm₁, ht] using huniqueX
  · simpa only [hy, hm₂, ht] using huniqueY
  · simpa only [hm₁, hm₂] using hne
  · exact hfail

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
