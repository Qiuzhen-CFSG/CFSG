module

public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation

/-!
# Normal two-subgroups of the literal product S2 × S4

Projection to S4 is either trivial or the Klein four core. In the latter
case conjugation differences force the entire Klein four into the subgroup,
so only the central S2 factor remains to be selected. The calculation uses
the existing core and its conjugation action, without enumerating subgroups.

Source: Aschbacher--Smith, 12.7.15(2), printed p.843.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymmetricSix.DuadCalculation

private theorem two_cases (a b : Two) (ha : a ≠ 1) : b = 1 ∨ b = a := by
  revert a b ha
  decide +kernel

private theorem core_moved (x : Four) (hx : x ∈ core) (hne : x ≠ 1) :
    ∃ g : Four, g * x * g⁻¹ ≠ x := by
  revert x hx hne
  decide +kernel

/-- The complete normal two-subgroup list retains the actual two product
factors and the literal Klein four in S4. -/
theorem normal_two_subgroup_cases (N : Subgroup (Two × Four)) [N.Normal]
    (hN : IsPGroup 2 N) :
    N = ⊥ ∨ N = (⊥ : Subgroup Two).prod core ∨
      N = centralFactor ∨ N = productCore := by
  have hNC : N ≤ productCore := by
    rw [productCore_eq]
    exact le_sSup ⟨inferInstance, hN⟩
  let f := MonoidHom.snd Two Four
  let B := N.map f
  let : B.Normal := (inferInstance : N.Normal).map f (fun x => ⟨(1, x), rfl⟩)
  have hBC : B ≤ core := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hNC hx).2
  rcases normal_subgroup_core B hBC with hB | hB
  · have hNZ : N ≤ centralFactor := by
      intro x hx
      have hh : f x ∈ B := mem_map_of_mem f hx
      rw [hB] at hh
      exact ⟨mem_top _, hh⟩
    by_cases hbot : N = ⊥
    · exact Or.inl hbot
    · right; right; left
      obtain ⟨a, ha, hane⟩ := N.bot_or_exists_ne_one.resolve_left hbot
      have ha2 : a.2 = 1 := (hNZ ha).2
      have ha1 : a.1 ≠ 1 := fun hh => hane (Prod.ext hh ha2)
      apply le_antisymm hNZ
      intro x hx
      have hx2 : x.2 = 1 := hx.2
      rcases two_cases a.1 x.1 ha1 with he | he
      · have hx1 : x = 1 := Prod.ext he hx2
        exact hx1.symm ▸ N.one_mem
      · have hxa : x = a := Prod.ext he (hx2.trans ha2.symm)
        exact hxa.symm ▸ ha
  · let M := N.comap (MonoidHom.inr Two Four)
    let : M.Normal := (inferInstance : N.Normal).comap _
    have hMC : M ≤ core := fun x hx => (hNC hx).2
    have hM : M = core := by
      rcases normal_subgroup_core M hMC with hbot | hfull
      · have hxC : ∃ x ∈ core, x ≠ 1 := by
          apply core.bot_or_exists_ne_one.resolve_left
          intro hh
          have hc := core_card
          simp [hh] at hc
        obtain ⟨x, hx, hxn⟩ := hxC
        obtain ⟨a, ha, hax⟩ := show x ∈ B by rw [hB]; exact hx
        have ha2 : a.2 = x := hax
        obtain ⟨g, hg⟩ := core_moved x hx hxn
        have hh := N.mul_mem ((inferInstance : N.Normal).conj_mem a ha (1, g))
          (N.inv_mem ha)
        have hm : g * x * g⁻¹ * x⁻¹ ∈ M := by
          change (1, g * x * g⁻¹ * x⁻¹) ∈ N
          convert hh using 1
          apply Prod.ext
          · simp
          · simp only [Prod.snd_mul, Prod.snd_inv, ha2]
        rw [hbot] at hm
        exact (hg (mul_inv_eq_one.mp hm)).elim
      · exact hfull
    have hRN : (⊥ : Subgroup Two).prod core ≤ N := by
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      change a = 1 at ha
      subst a
      change b ∈ M
      rw [hM]
      exact hb
    by_cases hNR : N ≤ (⊥ : Subgroup Two).prod core
    · exact Or.inr (Or.inl (le_antisymm hNR hRN))
    · right; right; right
      obtain ⟨a, ha, hnot⟩ := SetLike.not_le_iff_exists.mp hNR
      have ha1 : a.1 ≠ 1 := fun hh => hnot ⟨hh, (hNC ha).2⟩
      have hcentral : (a.1, 1) ∈ N := by
        have hR : (1, a.2) ∈ N := hRN ⟨one_mem _, (hNC ha).2⟩
        have hh := N.mul_mem ha (N.inv_mem hR)
        have he : a * (1, a.2)⁻¹ = (a.1, 1) := by apply Prod.ext <;> simp
        exact he ▸ hh
      apply le_antisymm hNC
      rintro ⟨x, y⟩ hx
      have hxR : (1, y) ∈ N := hRN ⟨one_mem _, hx.2⟩
      rcases two_cases a.1 x ha1 with he | he
      · simpa only [he] using hxR
      · have hh := N.mul_mem hcentral hxR
        simpa only [Prod.mk_mul_mk, mul_one, one_mul, he] using hh

end Theory.SpecificGroups.SymmetricSix.DuadCalculation
