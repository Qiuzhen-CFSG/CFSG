module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.Coordinates
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.Extension
public import Theory.Representation.QuadraticFourGroup.Recognition.FactorSylows.Linear
public import Theory.PrimeRank
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Odd-prime ranks of the full symplectic four-space parabolics

Both full stabilizers have odd-prime rank at most two over a finite field of
characteristic two. For a p-subgroup of either stabilizer, restrict its actual
determinant character. The character kernel embeds in the corresponding
determinant-one local factor. The existing matrix map from that factor to SL₂
has a kernel of exponent two, so its restriction to the odd p-subgroup is
injective. Such a subgroup of SL₂ is cyclic. The character image is a finite
subgroup of the field units and is cyclic as well. A generator of the kernel
and a lift of an image generator therefore generate the original p-subgroup.

This accounts for the torus in the full parabolics, in addition to their
determinant-one local factors. The proof also covers the binary field, so the
cardinality formulation does not need the restriction `2 ≤ f`.

Source: the Sp₄(2^f) generic case of Aschbacher--Smith, Theorem 0.1.2(1),
printed p.4, using the concrete local structure underlying F.1.12(I)(2),
printed pp.262--264 of `refs/quasithin.pdf` (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F]

private theorem rank_le_two_of_cyclic_kernel
    {A : Type*} [Group A] [Finite A] (χ : A →* Fˣ) (hχ : IsCyclic χ.ker) :
    Group.rank A ≤ 2 := by
  classical
  let : IsCyclic χ.ker := hχ
  let : Finite χ.range := Finite.of_surjective χ.rangeRestrict χ.rangeRestrict_surjective
  let : IsCyclic χ.range := isCyclic_subgroup_units χ.range
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := χ.ker)
  obtain ⟨r, hr⟩ := IsCyclic.exists_generator (α := χ.range)
  obtain ⟨b, hb⟩ := χ.rangeRestrict_surjective r
  let S : Subgroup A := closure ({a.val, b} : Finset A)
  have haS : a.val ∈ S := subset_closure (by simp)
  have hbS : b ∈ S := subset_closure (by simp)
  have hS : S = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (hr (χ.rangeRestrict x))
    have hn' : χ (b ^ n) = χ x := by
      rw [map_zpow]
      change (χ.rangeRestrict b : Fˣ) ^ n = (χ.rangeRestrict x : Fˣ)
      rw [hb]
      exact congrArg Subtype.val hn
    let c : χ.ker := ⟨x * (b ^ n)⁻¹, by simp [MonoidHom.mem_ker, hn']⟩
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (ha c)
    have hcS : c.val ∈ S := by
      have hm' : a.val ^ m = c.val := congrArg Subtype.val hm
      rw [← hm']
      exact S.zpow_mem haS m
    have h := S.mul_mem hcS (S.zpow_mem hbS n)
    simpa only [c, inv_mul_cancel_right] using h
  calc
    Group.rank A ≤ ({a.val, b} : Finset A).card := Group.rank_le hS
    _ ≤ 2 := by simpa only [Finset.card_singleton] using Finset.card_insert_le a.val {b}

private theorem stabilizer_odd_primeRank_le_two [Finite F] [CharP F 2]
    (W : Submodule F (Vector F)) {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (ρ : determinantKernel W →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hρ : ∀ x ∈ ρ.ker, x ^ 2 = 1) : primeRank p (stabilizer W) ≤ 2 := by
  apply csSup_le'
  rintro n ⟨A, hA, _, _, hn⟩
  let χ : A →* Fˣ := (determinantCharacter W).comp A.subtype
  -- Embed the restricted character kernel in the actual local matrix subgroup.
  let i : χ.ker →* determinantKernel W := {
    toFun x := ⟨x.val.val.val, ⟨x.val.val, x.property, rfl⟩⟩
    map_one' := rfl
    map_mul' _ _ := rfl
  }
  have hi : Function.Injective i := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : determinantKernel W => (z : Sp F)) h
  have hP := hA.to_subgroup χ.ker
  have hρi : Function.Injective (ρ.comp i) := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    have hs : i x ^ 2 = 1 := hρ (i x) hx
    have hx2 : x ^ 2 = 1 := hi (by simpa only [map_pow, map_one] using hs)
    exact (hP.powEquiv ho.coprime_two_right).injective
      (by simpa only [IsPGroup.powEquiv_apply, one_pow] using hx2)
  have hχ : IsCyclic χ.ker := Matrix.SL2.odd_pGroup_isCyclic_of_injective
    hP (fun hp2 => (by decide : ¬Odd (2 : ℕ)) (hp2 ▸ ho)) (ρ.comp i) hρi
  exact hn.trans (rank_le_two_of_cyclic_kernel χ hχ)

/-- The full point stabilizer has odd-prime rank at most two. -/
theorem pointParabolic_odd_primeRank_le_two [Finite F] [CharP F 2]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    primeRank p (pointParabolic (F := F)) ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  apply stabilizer_odd_primeRank_le_two (point F) ho pointQuotient
  intro x hx
  exact congrArg Subtype.val (pointRadical_pow_two ⟨x, hx⟩)

/-- The full plane stabilizer has odd-prime rank at most two. -/
theorem planeParabolic_odd_primeRank_le_two [Finite F] [CharP F 2]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    primeRank p (planeParabolic (F := F)) ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  apply stabilizer_odd_primeRank_le_two (plane F) ho Plane.quotientMap
  intro x hx
  exact congrArg Subtype.val (Plane.radical_sq ⟨x, hx⟩)

/-- Two-power field order supplies characteristic two and both full-parabolic
rank bounds, in particular for the nonbinary family `2 ≤ f`. -/
theorem parabolics_odd_primeRank_le_two_of_card [Finite F]
    {f : ℕ} (hF : Nat.card F = 2 ^ f) :
    ∀ p : ℕ, p.Prime → Odd p →
      primeRank p (pointParabolic (F := F)) ≤ 2 ∧
      primeRank p (planeParabolic (F := F)) ≤ 2 := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  intro p hp ho
  exact ⟨pointParabolic_odd_primeRank_le_two hp ho,
    planeParabolic_odd_primeRank_le_two hp ho⟩

end Theory.SpecificGroups.SymplecticFour
