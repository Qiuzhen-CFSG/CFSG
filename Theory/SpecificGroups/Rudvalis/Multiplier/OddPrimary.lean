module

public import Theory.SpecificGroups.Rudvalis.Multiplier.PrimaryBounds
public import Theory.SpecificGroups.Rudvalis.Multiplier.OddLocal
public import Theory.GroupTheory.Covering

/-!
# Odd-primary exclusion for Rudvalis central coverings

Simultaneous inversion of the marked Sylow subgroups excludes 3 and 5
from a finite perfect central kernel. Cyclic-Sylow transfer excludes every
remaining odd prime. Thus the whole kernel is a two-group, without any
assumption on its two-part and without constructing a double cover.

The literal source application composes the quotient map L → L/Z(L) with
the supplied equivalence to the actual Rudvalis model. It supplies precisely
`IsPGroup 2 (center L)` to the A.2.19 and direct K.4 Rudvalis consumers.
Their final source assemblies remain with `qt-a02-sporadic` and
`qt-k04-sporadic-ru-cubic-window`. The exact I.1.3 multiplier calculation
still requires a two-primary upper bound and a nontrivial perfect cover.
Source: Aschbacher–Smith I.1.1–I.1.3(1), printed p.407; A.2.19 and K.4.
-/

namespace Rudvalis.Multiplier
open PerfectCentralCovering Subgroup Theory.GroupTheory

variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]

/-- No finite perfect central cover of the actual model has three in its kernel. -/
public theorem not_three_dvd_card_kernel (f : E →* Model)
    (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    ¬ 3 ∣ Nat.card f.ker := by
  obtain ⟨Q, x, y, r, hQ, hx, hy, hz, hxz, hyz, hrx, hry, hrz⟩ :=
    OddLocal.exists_three_configuration
  exact not_dvd_card_kernel_of_simultaneous_inversion_of_ne_two f hf hk
    (by decide : 3 ≠ 2) Q x y r hQ hx hy hz hxz hyz hrx hry hrz

/-- No finite perfect central cover of the actual model has five in its kernel. -/
public theorem not_five_dvd_card_kernel (f : E →* Model)
    (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    ¬ 5 ∣ Nat.card f.ker := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨Q, x, y, r, hQ, hx, hy, hz, hxz, hyz, hrx, hry, hrz⟩ :=
    OddLocal.exists_five_configuration
  exact not_dvd_card_kernel_of_simultaneous_inversion_of_ne_two f hf hk
    (by decide : 5 ≠ 2) Q x y r hQ hx hy hz hxz hyz hrx hry hrz

/-- The early upper bound: every finite perfect central kernel over Ru is a two-group. -/
public theorem kernel_isPGroup (f : E →* Model)
    (hf : Function.Surjective f) (hk : f.ker ≤ center E) : IsPGroup 2 f.ker := by
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  have hp' := Nat.mem_primeFactors.mp hp
  have heq : p = 2 := by
    by_contra h2
    by_cases h3 : p = 3
    · subst p
      exact not_three_dvd_card_kernel f hf hk hp'.2.1
    by_cases h5 : p = 5
    · subst p
      exact not_five_dvd_card_kernel f hf hk hp'.2.1
    exact not_dvd_card_kernel_of_ne_two_three_five f hf hk hp'.1 h2 h3 h5 hp'.2.1
  norm_num [heq]

/-- A nontrivial odd prime-power central kernel cannot occur over the actual Ru carrier. -/
public theorem kernel_eq_bot_of_odd_pGroup (f : E →* Model)
    (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hkp : IsPGroup p f.ker) : f.ker = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  have hk2 := kernel_isPGroup f hf hk
  obtain ⟨n, hn⟩ := hk2.exists_card_eq
  rcases hkp.card_eq_or_dvd with h | h
  · exact Subgroup.card_eq_one.mp h
  · rw [hn] at h
    exact (hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow h))).elim

/-- The literal source-cover application: compose L → L/Z(L) with its actual model equivalence. -/
public theorem center_isPGroup_of_quotient_equiv
    {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    (e : L ⧸ center L ≃* Model) : IsPGroup 2 (center L) := by
  let f : L →* Model := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center L := by
    dsimp [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  exact (kernel_isPGroup f hf (le_of_eq hk)).of_equiv (MulEquiv.subgroupCongr hk)

/-- Exact premise consumed by the direct K.4 Rudvalis exclusion and A.2.19 assembly. -/
public theorem source_center_isPGroup
    {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    (h : Nonempty (L ⧸ center L ≃* Model)) : IsPGroup 2 (center L) := by
  obtain ⟨e⟩ := h
  exact center_isPGroup_of_quotient_equiv e

end Rudvalis.Multiplier
