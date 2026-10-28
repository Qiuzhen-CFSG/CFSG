module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.FieldSubgroups
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.FixedGeometryTransport
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.LocalActions
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.SeedGeneration

/-!
# Innerness of two-power automorphisms of the large Ree groups

A two-power automorphism fixes a Sylow two-subgroup, since the number of those
subgroups is odd. Sylow conjugacy then conjugates the automorphism to one
preserving the specified fixed positive subgroup, once its odd index is known.
Conjugation in the automorphism group preserves the given two-power equation.

Agreement on the two root-defined local seeds extends to the whole Ree group
once fixed-seed generation is supplied. If the two restrictions have one common
inner-times-field expression, the odd field period makes the resulting
two-power automorphism inner. Innerness then transports back through the
normalizing conjugation.

The final theorems discharge odd index by fixed Bruhat geometry, generation
by the two subsystem tori and fixed Bruhat factorization, and compatible local
actions by the signed root-block calculation. Thus every automorphism of
`Model m` satisfying a two-power equation is inner when `m ≥ 1`, with no
simplicity premise. The conditional reductions remain available separately.

This is the automorphism input for Aschbacher–Smith F.1.12, printed
pp.263–264 of refs/quasithin.pdf, using the inner/field convention of GLS3
Section 2.5 (refs/KGroup/GLS3/chapter2.tex). The full binary endpoint is not
covered by this automorphism statement.
-/

public section
noncomputable section

namespace ReeF4.Parabolics.OuterLocal.LargeAutomorphisms

open LargeLocalSeeds
open scoped Pointwise

private theorem normalize_sylow_two {G : Type*} [Group G] [Finite G] (U : Sylow 2 G)
    (a : MulAut G) (n : ℕ) (ha : a ^ (2 ^ n) = 1) :
    ∃ g : G, (MulAut.conj g⁻¹ * a * MulAut.conj g) • U = U := by
  have hA : IsPGroup 2 (Subgroup.zpowers a) := by
    apply IsPGroup.of_card_dvd_pow (n := n)
    rw [Nat.card_zpowers]
    exact orderOf_dvd_iff_pow_eq_one.mpr ha
  obtain ⟨P, hP⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card
    (Sylow 2 G) (not_dvd_card_sylow 2 G)
  have hfixed : a • P = P :=
    (MulAction.mem_fixedPoints.mp hP) ⟨a, Subgroup.mem_zpowers a⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G U P
  refine ⟨g, ?_⟩
  rw [mul_smul, mul_smul]
  change (MulAut.conj g⁻¹) • (a • (g • U)) = U
  rw [hg, hfixed, ← hg]
  change g⁻¹ • (g • U) = U
  exact inv_smul_smul g U

/-- Conjugation of an automorphism by the inner automorphism belonging to g⁻¹. -/
@[expose] def innerConjugate (m : ℕ) (g : Model m) (a : MulAut (Model m)) :
    MulAut (Model m) := MulAut.conj g⁻¹ * a * MulAut.conj g

/-- The conjugated automorphism satisfies the same two-power equation. -/
theorem innerConjugate_pow (m : ℕ) (g : Model m) (a : MulAut (Model m))
    (n : ℕ) (ha : a ^ (2 ^ n) = 1) : innerConjugate m g a ^ (2 ^ n) = 1 := by
  simpa [innerConjugate, MulAut.conj_apply, ha] using
    (map_pow (MulAut.conj ((MulAut.conj g)⁻¹)) a (2 ^ n)).symm

/-- Odd index suffices to normalize the actual positive fixed subgroup while
preserving the automorphism's two-power order. -/
theorem normalize_unipotent (m : ℕ) (hindex : Odd (unipotent m).index)
    (a : MulAut (Model m)) (n : ℕ) (ha : a ^ (2 ^ n) = 1) :
    ∃ g : Model m, innerConjugate m g a ^ (2 ^ n) = 1 ∧
      (unipotent m).map (innerConjugate m g a).toMonoidHom = unipotent m := by
  let U := sylowOfOddIndex m hindex
  obtain ⟨g, hg⟩ := normalize_sylow_two U a n ha
  refine ⟨g, innerConjugate_pow m g a n ha, ?_⟩
  exact congrArg (fun P : Sylow 2 (Model m) => (P : Subgroup (Model m))) hg

/-- Removing the normalizing conjugation gives an explicit inner witness. -/
theorem inner_of_innerConjugate (m : ℕ) (g : Model m) (a : MulAut (Model m))
    (h : ∃ x : Model m, MulAut.conj x = innerConjugate m g a) :
    ∃ x : Model m, MulAut.conj x = a := by
  obtain ⟨x, hx⟩ := h
  refine ⟨g * x * g⁻¹, ?_⟩
  rw [map_mul, map_mul, hx]
  simp [innerConjugate, mul_assoc]

/-- Generation by the two fixed seeds makes their restrictions faithful. -/
theorem eq_of_eqOn_seeds (m : ℕ)
    (hgen : seed m .suzuki ⊔ seed m .linear = ⊤)
    {a b : MulAut (Model m)}
    (h : ∀ s, Set.EqOn a b (seed m s)) : a = b := by
  have hle : seed m .suzuki ⊔ seed m .linear ≤
      a.toMonoidHom.eqLocus b.toMonoidHom :=
    sup_le (h .suzuki) (h .linear)
  apply MulEquiv.ext
  intro x
  exact hle (hgen ▸ Subgroup.mem_top x)

/-- A common expression on the two generating local factors extends globally.
The same g and k must work on both factors. -/
theorem form_of_local_actions (m : ℕ) (a : MulAut (Model m))
    (hgen : seed m .suzuki ⊔ seed m .linear = ⊤)
    (g : Model m) (k : ℕ)
    (h : ∀ s, Set.EqOn a (MulAut.conj g * fieldAutomorphism m ^ k : MulAut (Model m))
      (seed m s)) : a = MulAut.conj g * fieldAutomorphism m ^ k :=
  eq_of_eqOn_seeds m hgen h

/-- Conditional assembly of innerness from the fixed geometry and compatible
actions of automorphisms preserving the positive subgroup. -/
theorem inner_of_normalized_local_actions (m : ℕ)
    (hindex : Odd (unipotent m).index)
    (hgen : seed m .suzuki ⊔ seed m .linear = ⊤)
    (hlocal : ∀ (b : MulAut (Model m)) (r : ℕ), b ^ (2 ^ r) = 1 →
      (unipotent m).map b.toMonoidHom = unipotent m →
      ∃ (x : Model m) (k : ℕ), ∀ s,
        Set.EqOn b (MulAut.conj x * fieldAutomorphism m ^ k : MulAut (Model m))
          (seed m s))
    (a : MulAut (Model m)) (n : ℕ) (ha : a ^ (2 ^ n) = 1) :
    ∃ x : Model m, MulAut.conj x = a := by
  obtain ⟨g, hgpow, hgU⟩ := normalize_unipotent m hindex a n ha
  obtain ⟨x, k, hx⟩ := hlocal (innerConjugate m g a) n hgpow hgU
  have hform := form_of_local_actions m (innerConjugate m g a) hgen x k hx
  exact inner_of_innerConjugate m g a
    (inner_of_twoPower_of_inner_field m (innerConjugate m g a) x k n hform hgpow)

/-- The requested inner-times-field shape, conditional on the same three
undischarged local inputs. The recovered field exponent may be zero. -/
theorem inner_field_of_normalized_local_actions (m : ℕ)
    (hindex : Odd (unipotent m).index)
    (hgen : seed m .suzuki ⊔ seed m .linear = ⊤)
    (hlocal : ∀ (b : MulAut (Model m)) (r : ℕ), b ^ (2 ^ r) = 1 →
      (unipotent m).map b.toMonoidHom = unipotent m →
      ∃ (x : Model m) (k : ℕ), ∀ s,
        Set.EqOn b (MulAut.conj x * fieldAutomorphism m ^ k : MulAut (Model m))
          (seed m s))
    (a : MulAut (Model m)) (n : ℕ) (ha : a ^ (2 ^ n) = 1) :
    ∃ (x : Model m) (k : ℕ), a = MulAut.conj x * fieldAutomorphism m ^ k := by
  obtain ⟨x, hx⟩ := inner_of_normalized_local_actions m hindex hgen hlocal a n ha
  exact ⟨x, 0, by simpa only [pow_zero, mul_one] using hx.symm⟩

/-- Every two-power automorphism of the actual large Ree carrier is inner.
Odd index, fixed-seed generation, and compatible normalized local actions
are all discharged; no simplicity or perfectness hypothesis is required. -/
theorem inner_of_twoPower {m : ℕ} (hm : 1 ≤ m)
    (a : MulAut (Model m)) (n : ℕ) (ha : a ^ (2 ^ n) = 1) :
    ∃ g : Model m, MulAut.conj g = a := by
  have hindex : Odd (unipotent m).index :=
    unipotent_index_odd_of_standard (canonicalLocalBlockInput m)
      (FixedBruhat.standardUnipotent_index_odd (canonicalLocalBlockInput m))
  have hgen := seed_sup_eq_top m
  exact inner_of_normalized_local_actions m hindex hgen
    (LocalActions.exists_local_actions_of_normalized_twoPower m hm hindex hgen) a n ha

/-- Inner-times-field coverage for every two-power automorphism of the large
Ree carrier. Innerness permits the field exponent to be zero. -/
theorem inner_field_of_twoPower {m : ℕ} (hm : 1 ≤ m)
    (a : MulAut (Model m)) (n : ℕ) (ha : a ^ (2 ^ n) = 1) :
    ∃ (g : Model m) (k : ℕ), a = MulAut.conj g * fieldAutomorphism m ^ k := by
  obtain ⟨g, hg⟩ := inner_of_twoPower hm a n ha
  exact ⟨g, 0, by simpa only [pow_zero, mul_one] using hg.symm⟩

/-- The square-one form consumed by the outer two-group and rank arguments. -/
theorem inner_of_sq_eq_one {m : ℕ} (hm : 1 ≤ m)
    (a : MulAut (Model m)) (ha : a ^ 2 = 1) :
    ∃ g : Model m, MulAut.conj g = a :=
  inner_of_twoPower hm a 1 (by simpa only [pow_one] using ha)

end ReeF4.Parabolics.OuterLocal.LargeAutomorphisms
