module

public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.Representatives
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.Locality
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.RepresentativeGeneration

/-!
# Exhaustive Tits Sylow-local coverage

An exhaustive list of Sylow double cosets reduces proper overgroups to
the representatives which do not generate the whole group together with
the Sylow subgroup. For the explicit eighteen candidates, the three
remaining representatives lie in the two marked parabolics. A subgroup
contained in the union of two subgroups lies in one of them. Finally,
genuine two-local maximality makes that containment an equality.

The imported kernel-checked double-coset and generation certificates discharge
both premises of the reductions below. Thus every proper overgroup of the
marked Sylow subgroup lies in one of the two parabolics, and every maximal
two-local containing it equals one of them.
Source: Parrott (1972), §5, p.683, and the local convention in
Aschbacher–Smith, Theorem 0.1.2(1), printed pp.3–4 and 481–482.
-/

namespace Tits.ConverseLocalCoverage
open Subgroup ExceptionalParabolics

private theorem small_rep_mem (i : Fin 18) (hi : i.val < 3) :
    doubleCosetRep i ∈ first ∨ doubleCosetRep i ∈ second := by
  have he : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases he with rfl | rfl | rfl
  · exact Or.inl (by simp)
  · exact Or.inl (by simpa using reflection_mem_first)
  · exact Or.inr (by simpa using reflection_mem_second)

/-- The explicit double-coset and generation certificates imply placement
of every proper Sylow overgroup in a marked parabolic. -/
public theorem le_first_or_second_of_certificates
    (hcover : ∀ x : Atlas1600Group, ∃ (a b : S) (i : Fin 18),
      x = a.val * doubleCosetRep i * b.val)
    (hgenerate : ∀ i : Fin 18, 3 ≤ i.val →
      S ⊔ closure {doubleCosetRep i} = ⊤)
    (H : Subgroup Atlas1600Group) (hproper : H ≠ ⊤) (hS : S ≤ H) :
    H ≤ first ∨ H ≤ second := by
  have hmem (x : Atlas1600Group) (hx : x ∈ H) : x ∈ first ∨ x ∈ second := by
    obtain ⟨a, b, i, he⟩ := hcover x
    have hiH : doubleCosetRep i ∈ H := by
      have hm := H.mul_mem (H.mul_mem (H.inv_mem (hS a.property)) hx)
        (H.inv_mem (hS b.property))
      have hc : a.val⁻¹ * x * b.val⁻¹ = doubleCosetRep i := by rw [he]; group
      rwa [hc] at hm
    have hi : i.val < 3 := by
      by_contra hn
      have hle : S ⊔ closure {doubleCosetRep i} ≤ H :=
        sup_le hS ((closure_le _).mpr (by
          rintro y (rfl : y = doubleCosetRep i)
          exact hiH))
      rw [hgenerate i (by omega)] at hle
      exact hproper (top_unique hle)
    rcases small_rep_mem i hi with hf | hs
    · exact Or.inl (he.symm ▸ first.mul_mem
        (first.mul_mem (sylow_le_first a.property) hf) (sylow_le_first b.property))
    · exact Or.inr (he.symm ▸ second.mul_mem
        (second.mul_mem (sylow_le_second a.property) hs) (sylow_le_second b.property))
  classical
  by_cases hf : H ≤ first
  · exact Or.inl hf
  · right
    obtain ⟨a, ha, haf⟩ := SetLike.not_le_iff_exists.mp hf
    have has : a ∈ second := (hmem a ha).resolve_left haf
    intro b hb
    by_contra hbs
    have hbf : b ∈ first := (hmem b hb).resolve_right hbs
    rcases hmem (a * b) (H.mul_mem ha hb) with hab | hab
    · exact haf (by simpa only [mul_inv_cancel_right] using
        first.mul_mem hab (first.inv_mem hbf))
    · exact hbs (by simpa only [inv_mul_cancel_left] using
        second.mul_mem (second.inv_mem has) hab)

/-- Maximality among actual two-locals converts the finite certificates
into the exact parabolic alternatives. -/
public theorem maximalTwoLocal_eq_first_or_second_of_certificates
    (hcover : ∀ x : Atlas1600Group, ∃ (a b : S) (i : Fin 18),
      x = a.val * doubleCosetRep i * b.val)
    (hgenerate : ∀ i : Fin 18, 3 ≤ i.val →
      S ⊔ closure {doubleCosetRep i} = ⊤)
    (M : Subgroup Atlas1600Group) (hM : IsMaximalTwoLocal M)
    (hS : atlas1600SylowTwoSubgroup ≤ M) : M = first ∨ M = second := by
  rcases le_first_or_second_of_certificates hcover hgenerate M
      (twoLocal_ne_top M hM.1) hS with hf | hs
  · exact Or.inl (le_antisymm hf (hM.2 first_isTwoLocal hf))
  · exact Or.inr (le_antisymm hs (hM.2 second_isTwoLocal hs))

/-- Every proper overgroup of the marked Sylow subgroup lies in one of the
two concrete parabolics. Both finite certificates are discharged. -/
public theorem le_first_or_second
    (H : Subgroup Atlas1600Group) (hproper : H ≠ ⊤)
    (hS : atlas1600SylowTwoSubgroup ≤ H) : H ≤ first ∨ H ≤ second :=
  le_first_or_second_of_certificates doubleCoset_cover representative_generates H hproper hS

/-- Every maximal two-local containing the marked Sylow subgroup is one of
the two concrete parabolics, with no additional coverage or generation premises. -/
public theorem maximalTwoLocal_eq_first_or_second
    (M : Subgroup Atlas1600Group) (hM : IsMaximalTwoLocal M)
    (hS : atlas1600SylowTwoSubgroup ≤ M) : M = first ∨ M = second :=
  maximalTwoLocal_eq_first_or_second_of_certificates
    doubleCoset_cover representative_generates M hM hS

end Tits.ConverseLocalCoverage
