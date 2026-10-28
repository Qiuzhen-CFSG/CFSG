module

public import Theory.SpecificGroups.ReeF4.ConverseParabolics
public import Theory.SpecificGroups.Suzuki.OddSubgroups
public import Theory.Representation.QuadraticFourGroup.Recognition.FactorSylows.Linear
public import Theory.GroupTheory.QuasithinBasic

/-!
# Odd ranks from the full Ree parabolic projections

The full Levi quotients consist of a Suzuki or SL₂ factor and a multiplicative
field torus. A homomorphism to that product with two-group kernel is injective
on each odd-primary subgroup. Its torus character has cyclic image, and the
character kernel embeds into the rank-one factor, where odd-primary subgroups
are cyclic. Lifting a generator of the character image and adjoining a kernel
generator proves a rank bound of two.

The two-generator argument is the same elementary lifting argument used in
`SymplecticFour.LocalStructure.ParabolicRanks`. Suzuki cyclicity and SL₂
cyclicity are established results about the actual matrix groups. The Ree
projection maps remain explicit inputs; this module does not construct them
or assert the unconditional Ree rank bounds.

Source: Aschbacher–Smith, Theorem 0.1.2(1), printed p.4, and F.1.12(I)(5),
printed p.263 (`refs/quasithin.pdf`), with the full parabolic torus retained.
-/

public noncomputable section
namespace ReeF4.ConverseParabolics
open Subgroup BenderSuzuki.MatrixGroups

private theorem rank_le_two_of_cyclic_kernel
    {F A : Type*} [Field F] [Group A] [Finite A]
    (χ : A →* Fˣ) (hχ : IsCyclic χ.ker) : Group.rank A ≤ 2 := by
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

private theorem primeRank_le_two_of_two_kernel
    {G H F : Type*} [Group G] [Finite G] [Group H] [Finite H] [Field F]
    {p : ℕ} (ho : Odd p)
    (hH : ∀ A : Subgroup H, IsPGroup p A → IsCyclic A)
    (π : G →* H × Fˣ) (hker : IsPGroup 2 π.ker) : primeRank p G ≤ 2 := by
  apply csSup_le'
  rintro n ⟨A, hA, _, _, hn⟩
  let j := π.comp A.subtype
  have hj : Function.Injective j := by
    apply (injective_iff_map_eq_one j).mpr
    intro a ha
    exact Subtype.ext (Subgroup.disjoint_def.mp
      (hA.disjoint_of_coprime hker ho.coprime_two_right) a.property ha)
  let χ : A →* Fˣ := (MonoidHom.snd H Fˣ).comp j
  let f : χ.ker →* H := ((MonoidHom.fst H Fˣ).comp j).comp χ.ker.subtype
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply hj
    apply Prod.ext h
    exact x.property.trans y.property.symm
  let : IsCyclic f.range := hH f.range
    ((hA.to_subgroup χ.ker).of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  have hχ : IsCyclic χ.ker := isCyclic_of_injective f.rangeRestrict
    (by intro x y h; exact hf (congrArg Subtype.val h))
  exact hn.trans (rank_le_two_of_cyclic_kernel χ hχ)

/-- A two-group kernel in the actual Suzuki-times-torus representation gives
the odd-rank bound for the full Suzuki-side Ree parabolic. -/
theorem suzuki_primeRank_le_two_of_projection {m : ℕ} (hm : 1 ≤ m)
    (π : parabolic m .suzuki →* SuzukiMatrixGroup m × (CoefficientField m)ˣ)
    (hker : IsPGroup 2 π.ker) {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    primeRank p (parabolic m .suzuki) ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  apply primeRank_le_two_of_two_kernel ho (π := π) (hker := hker)
  intro A hA
  obtain ⟨P, hAP⟩ := hA.exists_le_sylow
  have hp2 : p ≠ 2 := by rintro rfl; exact ho.not_two_dvd_nat (dvd_refl 2)
  let : IsCyclic P := suzukiSylow_isCyclic_of_ne_two (by omega) hp2 P
  exact Subgroup.isCyclic_of_le hAP

/-- A two-group kernel in the actual SL₂-times-torus representation gives
the odd-rank bound for the full linear-side Ree parabolic. -/
theorem linear_primeRank_le_two_of_projection {m : ℕ}
    (π : parabolic m .linear →*
      Matrix.SpecialLinearGroup (Fin 2) (CoefficientField m) × (CoefficientField m)ˣ)
    (hker : IsPGroup 2 π.ker) {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    primeRank p (parabolic m .linear) ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  apply primeRank_le_two_of_two_kernel ho (π := π) (hker := hker)
  intro A hA
  exact Matrix.SL2.odd_pGroup_isCyclic_of_injective hA
    (by rintro rfl; exact ho.not_two_dvd_nat (dvd_refl 2)) A.subtype A.subtype_injective

end ReeF4.ConverseParabolics
