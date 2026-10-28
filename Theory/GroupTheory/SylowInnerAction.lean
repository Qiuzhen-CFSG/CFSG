module

public import Theory.GroupTheory.AutomorphismTowerSimple
public import Mathlib.GroupTheory.Sylow

/-!
# Inner actors in a p-subgroup of automorphisms

For a centerless group, conjugation is injective. If a p-subgroup of
automorphisms contains the conjugations by a Sylow p-subgroup S, its
inner actors are conjugations by elements of S: the preimage under
conjugation is a p-subgroup containing S, and Sylow maximality applies.

Source application: Aschbacher–Smith, proof of Lemma 1.3.9(1), printed p.514.
-/
open Subgroup
namespace MulAut
variable {G : Type*} [Group G]

/-- Sylow maximality identifies the possible inner conjugators in a p-group of actors. -/
public theorem inner_mem_image_sylow {p : ℕ} (hc : center G = ⊥)
    (S : Sylow p G) (R : Subgroup (MulAut G)) (hR : IsPGroup p R)
    (hSR : (S : Subgroup G).map (conj : G →* MulAut G) ≤ R)
    {b : G} (hb : conj b ∈ R) : b ∈ S := by
  have he : R.comap (conj : G →* MulAut G) = S :=
    S.is_maximal' (hR.comap_of_injective _ (conj_injective_of_center_eq_bot hc))
      (map_le_iff_le_comap.mp hSR)
  have hb' : b ∈ R.comap (conj : G →* MulAut G) := hb
  rwa [he] at hb'

/-- An inner actor stabilizing a disjoint subgroup fixes it pointwise when
that subgroup normalizes the Sylow subgroup. -/
public theorem inner_actor_fixes_disjoint_subgroup {p : ℕ} (hc : center G = ⊥)
    (S : Sylow p G) (R : Subgroup (MulAut G)) (hR : IsPGroup p R)
    (hSR : (S : Subgroup G).map (conj : G →* MulAut G) ≤ R)
    (A : Subgroup G) (hd : Disjoint (S : Subgroup G) A)
    (hn : A ≤ normalizer (S : Set G))
    {β : MulAut G} (hβ : β ∈ R) (hi : ∃ b, β = conj b)
    (hA : ∀ a ∈ A, β a ∈ A) : ∀ a ∈ A, β a = a := by
  obtain ⟨b, rfl⟩ := hi
  have hb := inner_mem_image_sylow hc S R hR hSR hβ
  intro a ha
  have hcA : b * a * b⁻¹ * a⁻¹ ∈ A := A.mul_mem (hA a ha) (A.inv_mem ha)
  have hcS : b * a * b⁻¹ * a⁻¹ ∈ (S : Subgroup G) := by
    have hh := (mem_normalizer_iff.mp (hn ha) b⁻¹).mp (S.inv_mem hb)
    simpa only [mul_assoc] using S.mul_mem hb hh
  have he : b * a * b⁻¹ * a⁻¹ = 1 := hd.le_bot ⟨hcS, hcA⟩
  exact mul_inv_eq_one.mp he

end MulAut
