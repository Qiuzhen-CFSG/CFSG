module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic

/-!
# Irreducibility from two fixed lines

For two binary actors with fixed lines ⟨z⟩ and ⟨i⟩, every nonzero invariant
subgroup contains both lines by the p-group fixed-point theorem. If the
module is [U,i]⟨i,z⟩, invariance under U then supplies the whole module.
This does not require a separate indecomposability or chief-series premise.

Source application: the symmetric U and U^x actions in Aschbacher–Smith,
Lemma 14.4.9, printed p.1010 of `refs/quasithin.pdf`.
-/

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A nontrivial invariant p-subgroup has a nontrivial centralizer of a p-group of actors. -/
public theorem inf_centralizer_ne_bot_of_pGroups {p : ℕ} [Fact p.Prime]
    (P E : Subgroup G) (hP : IsPGroup p P) (hE : IsPGroup p E)
    (hPE : P ≤ normalizer (E : Set G)) (hne : E ≠ ⊥) :
    E ⊓ centralizer (P : Set G) ≠ ⊥ := by
  let : Nontrivial E := (nontrivial_iff_ne_bot E).mpr hne
  let ρ : P →* MulAut E := E.normalizerMonoidHom.comp (inclusion hPE)
  let : MulDistribMulAction P E := MulDistribMulAction.compHom E ρ
  have hdiv : p ∣ Nat.card E := by
    obtain ⟨n, hn, he⟩ := hE.nontrivial_iff_card.mp inferInstance
    rw [he]
    exact dvd_pow_self _ (by omega)
  have hfixed : (1 : E) ∈ MulAction.fixedPoints P E := fun g => smul_one g
  obtain ⟨e, he, hne⟩ :=
    hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point E hdiv hfixed
  intro hbot
  have heC : (e : G) ∈ E ⊓ centralizer (P : Set G) := by
    refine ⟨e.property, ?_⟩
    intro g hg
    have hh := congrArg Subtype.val (he ⟨g, hg⟩)
    change g * (e : G) * g⁻¹ = (e : G) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have he1 : (e : G) = 1 := by simpa [hbot] using heC
  exact hne (Subtype.ext he1.symm)

/-- Every nontrivial invariant binary subgroup contains the unique fixed involution. -/
public theorem involution_mem_of_invariant_of_fixed_line (P E D : Subgroup G) (z : G)
    (hz : orderOf z = 2) (hP : IsPGroup 2 P) (hE : IsPGroup 2 E)
    (hPE : P ≤ normalizer (E : Set G)) (hne : E ≠ ⊥) (hED : E ≤ D)
    (hfix : D ⊓ centralizer (P : Set G) = zpowers z) : z ∈ E := by
  classical
  have hn := inf_centralizer_ne_bot_of_pGroups P E hP hE hPE hne
  obtain ⟨e, he⟩ := ne_bot_iff_exists_ne_one.mp hn
  have heZ : (e : G) ∈ zpowers z := hfix ▸ ⟨hED e.property.1, e.property.2⟩
  have hene : (e : G) ≠ 1 := fun h => he (Subtype.ext h)
  rw [mem_zpowers_iff_mem_range_orderOf, hz] at heZ
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp heZ
  have hk2 : k < 2 := Finset.mem_range.mp hk
  interval_cases k
  · exact (hene (by simpa using heq.symm)).elim
  · have hez : (e : G) = z := by simpa using heq.symm
    exact hez ▸ e.property.1

/-- Two fixed lines force irreducibility on the actual commutator-generated lift. -/
public theorem commutator_join_irreducible_of_two_fixed_lines (U Ux Y : Subgroup G) (z i : G)
    (hz : orderOf z = 2) (hi : orderOf i = 2)
    (hU : IsPGroup 2 U) (hUx : IsPGroup 2 Ux)
    (hUY : U ≤ Y) (hUxY : Ux ≤ Y)
    (hD : IsPGroup 2 (⁅U, zpowers i⁆ ⊔ zpowers i ⊔ zpowers z : Subgroup G))
    (hfixU : (⁅U, zpowers i⁆ ⊔ zpowers i ⊔ zpowers z : Subgroup G) ⊓
      centralizer (U : Set G) = zpowers z)
    (hfixUx : (⁅U, zpowers i⁆ ⊔ zpowers i ⊔ zpowers z : Subgroup G) ⊓
      centralizer (Ux : Set G) = zpowers i)
    (E : Subgroup G) (hED : E ≤ ⁅U, zpowers i⁆ ⊔ zpowers i ⊔ zpowers z)
    (hYE : Y ≤ normalizer (E : Set G)) :
    E = ⊥ ∨ E = ⁅U, zpowers i⁆ ⊔ zpowers i ⊔ zpowers z := by
  by_cases hne : E = ⊥
  · exact Or.inl hne
  have hUE := hUY.trans hYE
  have hzE := involution_mem_of_invariant_of_fixed_line U E _ z hz hU (hD.to_le hED) hUE hne hED hfixU
  have hiE := involution_mem_of_invariant_of_fixed_line Ux E _ i hi hUx (hD.to_le hED)
    (hUxY.trans hYE) hne hED hfixUx
  refine Or.inr (le_antisymm hED (sup_le (sup_le ?_ (zpowers_le.mpr hiE)) (zpowers_le.mpr hzE)))
  apply commutator_le.mpr
  intro u hu v hv
  have hvE := (zpowers_le.mpr hiE : zpowers i ≤ E) hv
  exact E.mul_mem ((mem_normalizer_iff.mp (hUE hu) v).mp hvE) (E.inv_mem hvE)
end Subgroup
