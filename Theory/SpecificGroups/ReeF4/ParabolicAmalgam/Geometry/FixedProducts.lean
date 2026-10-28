module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RootData
public import Theory.GroupAction.HallProductFixedPoints

/-!
# Fixed products in the Ree parabolics

A twist-fixed element in a product of invariant subgroups has a fixed
factorization when their intersection has odd order. The involution acts on
the set of factorizations, an odd set, so one factorization is fixed. Applying
this to a root seed and its normalizing odd torus gives the required fixed
parabolic decomposition; the positive subgroup gives the Borel decomposition.

Oddness and normalization of the coroot-word torus remain explicit inputs.
Twist stability alone would not justify these decompositions. At the binary
endpoint the torus is trivial, so the decomposition and Borel normalization
are unconditional. The ambient fixed group is the full ²F₄(2).

Source: the root parabolic construction underlying Aschbacher–Smith,
F.1.4–5 and F.1.12(I)(5), printed pp.260,263–264 of `refs/quasithin.pdf`.
-/

@[expose] public section

open scoped Pointwise
open Subgroup


private theorem exists_fixed_factors_of_odd_inf {G : Type*} [Group G] [Finite G] (φ : MulAut G)
    (hφ : φ ^ 2 = 1) (A B : Subgroup G)
    (hA : A.map φ.toMonoidHom = A) (hB : B.map φ.toMonoidHom = B)
    (hodd : Odd (Nat.card (A ⊓ B : Subgroup G)))
    (x : G) (hx : φ x = x) (hprod : x ∈ (A : Set G) * (B : Set G)) :
    ∃ a ∈ A, ∃ b ∈ B, φ a = a ∧ φ b = b ∧ a * b = x := by
  let S := Subgroup.zpowers φ
  have hS : IsPGroup 2 S := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    simpa only [S, Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one hφ
  have hinv (H : Subgroup G) (hH : H.map φ.toMonoidHom = H) : IsInvariant S G H := by
    have hφH : φ • H = H := hH
    refine ⟨fun s g => ?_⟩
    have hsH : (s : MulAut G) • H = H := smul_eq_self_of_mem_zpowers s.property hφH
    change g ∈ H ↔ (s : MulAut G) • g ∈ H
    simpa only [hsH] using
      (Subgroup.smul_mem_pointwise_smul_iff (a := (s : MulAut G)) (x := g) (S := H)).symm
  let := hinv A hA
  let := hinv B hB
  have hfixed : x ∈ fixedPointSubgroup S G :=
    fun s => smul_eq_self_of_mem_zpowers s.property hx
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp
    (fixed_mem_mul_of_odd_inf hS A B hodd hfixed hprod)
  exact ⟨a, ha.1, b, hb.1, ha.2 ⟨φ, mem_zpowers φ⟩,
    hb.2 ⟨φ, mem_zpowers φ⟩, hab⟩

namespace ReeF4.Parabolics
open LargeLocalSeeds
noncomputable section

/-- The twist-fixed part of the specified coroot-word torus. -/
def fixedTorus (m : ℕ) : Subgroup (Model m) :=
  (splitTorus m).comap (toSplitGroup m)

theorem fixedTorus_le_borel (m : ℕ) : fixedTorus m ≤ borel m :=
  comap_mono le_sup_right

theorem fixedTorus_odd_card (m : ℕ) (hodd : Odd (Nat.card (splitTorus m))) :
    Odd (Nat.card (fixedTorus m)) := by
  let f : fixedTorus m →* splitTorus m :=
    { toFun := fun x => ⟨toSplitGroup m x.val, x.property⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ _ _) }
  apply hodd.of_dvd_nat (card_dvd_of_injective f ?_)
  intro x y h
  have he : toSplitGroup m x.val = toSplitGroup m y.val :=
    congrArg (fun z : splitTorus m => (z : SplitGroup m)) h
  exact Subtype.ext (toSplitGroup_injective m he)

private theorem exists_fixed_factors_of_splitTorus (m : ℕ)
    (H : Subgroup (SplitGroup m))
    (hH : H.map (reeAutomorphism m).toMonoidHom = H)
    (hn : splitTorus m ≤ normalizer (H : Set (SplitGroup m)))
    (hodd : Odd (Nat.card (splitTorus m)))
    (x : Model m) (hx : toSplitGroup m x ∈ H ⊔ splitTorus m) :
    ∃ a ∈ H.comap (toSplitGroup m), ∃ t ∈ fixedTorus m, a * t = x := by
  have hφ : reeAutomorphism m ^ 2 = 1 := by
    apply MulEquiv.ext
    intro z
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply, reeAutomorphism_apply] using
      reeTwist_involutive m z
  have hprod : toSplitGroup m x ∈ (H : Set (SplitGroup m)) *
      (splitTorus m : Set (SplitGroup m)) := by
    rwa [← coe_mul_of_right_le_normalizer_left H (splitTorus m) hn]
  obtain ⟨a, ha, t, ht, hfa, hft, he⟩ :=
    exists_fixed_factors_of_odd_inf (reeAutomorphism m) hφ H (splitTorus m)
      hH (splitTorus_invariant m)
      (hodd.of_dvd_nat (card_dvd_of_le (inf_le_right : H ⊓ splitTorus m ≤ splitTorus m)))
      (toSplitGroup m x)
      (by simpa only [reeAutomorphism_apply] using reeTwist_toSplitGroup m x) hprod
  let a' : Model m := ⟨a, (mem_fixedSubgroup m a).mpr
    (by simpa only [reeAutomorphism_apply] using hfa)⟩
  let t' : Model m := ⟨t, (mem_fixedSubgroup m t).mpr
    (by simpa only [reeAutomorphism_apply] using hft)⟩
  refine ⟨a', ?_, t', ?_, ?_⟩
  · simpa only [mem_comap, toSplitGroup_apply] using ha
  · simpa only [fixedTorus, mem_comap, toSplitGroup_apply] using ht
  · exact Subtype.ext (he.trans (toSplitGroup_apply m x))

/-- Oddness of the split torus makes a fixed seed–torus factorization possible. -/
theorem parabolic_eq_seed_sup_fixedTorus_of_splitTorus (m : ℕ) (s : Side)
    (hn : splitTorus m ≤ normalizer (splitSeed m s : Set (SplitGroup m)))
    (hodd : Odd (Nat.card (splitTorus m))) :
    parabolic m s = seed m s ⊔ fixedTorus m := by
  apply le_antisymm
  · intro x hx
    have hstable : (splitSeed m s).map (reeAutomorphism m).toMonoidHom = splitSeed m s := by
      rw [← (canonicalLocalBlockInput m).twist_eq_reeAutomorphism]
      exact splitSeed_twist _ _
    obtain ⟨a, ha, t, ht, rfl⟩ :=
      exists_fixed_factors_of_splitTorus m (splitSeed m s) hstable hn hodd x hx
    exact mul_mem_sup ha ht
  · exact sup_le (seed_le_parabolic m s)
      ((fixedTorus_le_borel m).trans (borel_le_parabolic m s))

/-- The full fixed parabolic is generated by its fixed seed and root Borel.
The split-torus hypotheses still require the coroot-word calculation. -/
theorem parabolic_eq_seed_sup_borel_of_splitTorus (m : ℕ) (s : Side)
    (hn : splitTorus m ≤ normalizer (splitSeed m s : Set (SplitGroup m)))
    (hodd : Odd (Nat.card (splitTorus m))) :
    parabolic m s = seed m s ⊔ borel m := by
  apply le_antisymm
  · rw [parabolic_eq_seed_sup_fixedTorus_of_splitTorus m s hn hodd]
    exact sup_le_sup_left (fixedTorus_le_borel m) _
  · exact sup_le (seed_le_parabolic m s) (borel_le_parabolic m s)

/-- The same fixed-factor argument separates the positive part of the Borel. -/
theorem borel_eq_unipotent_sup_fixedTorus_of_splitTorus (m : ℕ)
    (hn : splitTorus m ≤ normalizer (splitUnipotent m : Set (SplitGroup m)))
    (hodd : Odd (Nat.card (splitTorus m))) :
    borel m = unipotent m ⊔ fixedTorus m := by
  apply le_antisymm
  · intro x hx
    have hstable : (splitUnipotent m).map (reeAutomorphism m).toMonoidHom = splitUnipotent m := by
      rw [← (canonicalLocalBlockInput m).twist_eq_reeAutomorphism]
      exact splitUnipotent_twist _
    obtain ⟨a, ha, t, ht, rfl⟩ :=
      exists_fixed_factors_of_splitTorus m (splitUnipotent m) hstable hn hodd x hx
    exact mul_mem_sup ha ht
  · exact sup_le (unipotent_le_borel m) (fixedTorus_le_borel m)

theorem borel_le_unipotent_normalizer_of_splitTorus (m : ℕ)
    (hn : splitTorus m ≤ normalizer (splitUnipotent m : Set (SplitGroup m))) :
    borel m ≤ normalizer (unipotent m : Set (Model m)) :=
  (comap_mono (sup_le (splitUnipotent m).le_normalizer hn)).trans (le_normalizer_comap _)

@[simp] theorem fixedTorus_zero : fixedTorus 0 = ⊥ := by
  simp only [fixedTorus, splitTorus_zero]
  exact (toSplitGroup 0).ker_eq_bot_iff.mpr (toSplitGroup_injective 0)

theorem parabolic_zero_eq_seed_sup_borel (s : Side) :
    parabolic 0 s = seed 0 s ⊔ borel 0 := by
  rw [parabolic_zero, borel_zero, sup_eq_left.mpr (unipotent_le_seed 0 s)]

theorem borel_zero_le_unipotent_normalizer :
    borel 0 ≤ normalizer (unipotent 0 : Set (Model 0)) := by
  rw [borel_zero]
  exact le_normalizer

end
end ReeF4.Parabolics
