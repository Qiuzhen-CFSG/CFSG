module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Normal subgroups and Frobenius kernels

A normal subgroup F whose nonidentity elements have centralizers contained
in F is comparable with every normal subgroup N of a finite group. If n is
in N outside F, the map a ↦ a n a⁻¹ n⁻¹ is an injection of F into itself,
and hence a surjection. Its image lies in N, proving F ≤ N.

For a proper normal Sylow p-subgroup with this centralizer property,
comparability implies containment in every normal subgroup with p-group
quotient. Such a normal subgroup supplements the Sylow subgroup and so
cannot lie inside it.

This is the elementary argument of Glauberman, *A Characterization of the
Suzuki Groups* (1968), Lemma 2.3(ii) and Proposition 2.1(ii), pp. 79–80.
-/

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Normal subgroups are comparable with a normal subgroup whose nonidentity
  elements have no centralizer outside that subgroup. -/
public theorem normal_le_or_le_of_centralizer_le (F N : Subgroup G) [F.Normal] [N.Normal]
    (hcent : ∀ x ∈ F, x ≠ 1 → centralizer ({x} : Set G) ≤ F) :
    N ≤ F ∨ F ≤ N := by
  classical
  by_cases hNF : N ≤ F
  · exact Or.inl hNF
  right
  obtain ⟨n, hnN, hnnotF⟩ := SetLike.not_le_iff_exists.mp hNF
  let delta : F → F := fun a =>
    ⟨(a : G) * n * (a : G)⁻¹ * n⁻¹, by
      have hconj : n * (a : G)⁻¹ * n⁻¹ ∈ F :=
        (inferInstance : F.Normal).conj_mem _ (F.inv_mem a.property) n
      simpa only [mul_assoc] using F.mul_mem a.property hconj⟩
  have hinj : Function.Injective delta := by
    intro a b hab
    have habG : (a : G) * n * (a : G)⁻¹ * n⁻¹ =
        (b : G) * n * (b : G)⁻¹ * n⁻¹ := congrArg Subtype.val hab
    have hcomm : (b : G)⁻¹ * (a : G) * n = n * ((b : G)⁻¹ * (a : G)) := by
      have h1 : (a : G) * n * (a : G)⁻¹ = (b : G) * n * (b : G)⁻¹ := by
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using
          congrArg (fun t : G => t * n) habG
      have h2 := congrArg (fun t : G => (b : G)⁻¹ * t * (a : G)) h1
      simpa only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using h2
    have he : (b : G)⁻¹ * (a : G) = 1 := by
      by_contra hne
      exact hnnotF (hcent _ (F.mul_mem (F.inv_mem b.property) a.property) hne
        (mem_centralizer_singleton_iff.mpr hcomm.symm))
    exact Subtype.ext (inv_mul_eq_one.mp he).symm
  have hsurj := Finite.surjective_of_injective hinj
  intro k hk
  obtain ⟨a, ha⟩ := hsurj ⟨k, hk⟩
  have haG : (a : G) * n * (a : G)⁻¹ * n⁻¹ = k := congrArg Subtype.val ha
  rw [← haG]
  exact N.mul_mem ((inferInstance : N.Normal).conj_mem n hnN a) (N.inv_mem hnN)

end Subgroup

namespace Sylow
open Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A normal subgroup with prime-group quotient supplements every Sylow subgroup
for that prime. -/
public theorem sup_eq_top_of_quotient_isPGroup (S : Sylow p G)
    (N : Subgroup G) [N.Normal] (hquot : IsPGroup p (G ⧸ N)) :
    (S : Subgroup G) ⊔ N = ⊤ := by
  have ht : ((S.mapSurjective (QuotientGroup.mk'_surjective N)) :
      Subgroup (G ⧸ N)) = ⊤ :=
    (Sylow.is_maximal' _ (hquot.to_subgroup ⊤) le_top).symm
  have hc := congrArg (Subgroup.comap (QuotientGroup.mk' N)) ht
  rw [Sylow.coe_mapSurjective, QuotientGroup.comap_map_mk', comap_top] at hc
  simpa only [sup_comm] using hc

/-- A proper normal Sylow subgroup with the Frobenius centralizer property lies
in every normal subgroup with prime-group quotient. -/
public theorem le_normal_of_quotient_isPGroup_of_centralizer_le (S : Sylow p G)
    [(S : Subgroup G).Normal] (hproper : (S : Subgroup G) ≠ ⊤)
    (hcent : ∀ x ∈ (S : Subgroup G), x ≠ 1 → centralizer ({x} : Set G) ≤ (S : Subgroup G))
    (N : Subgroup G) [N.Normal] (hquot : IsPGroup p (G ⧸ N)) :
    (S : Subgroup G) ≤ N := by
  rcases normal_le_or_le_of_centralizer_le (S : Subgroup G) N hcent with h | h
  · exact False.elim (hproper (by
      simpa only [sup_of_le_left h] using S.sup_eq_top_of_quotient_isPGroup N hquot))
  · exact h

end Sylow
