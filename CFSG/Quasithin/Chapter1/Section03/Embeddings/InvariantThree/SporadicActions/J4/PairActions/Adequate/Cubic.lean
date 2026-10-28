module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Reduction

/-!
# Pulling back a characteristic cubic subgroup

An elementary-nine subgroup containing a characteristic cubic subgroup in
an injective image has a proper nonzero invariant subgroup. Pull it back
and map through the actual Frattini quotient, which is injective here.
Every compatible actor preserves this line.

The characteristic cubic subgroup, its containment in the image, and the
compatible automorphisms are explicit inputs. Constructing them in the
actual max2 quotient remains a concrete local-model obligation.

Source application: Aschbacher–Smith, proof of Proposition 1.3.4,
printed p.511/PDF p.528 of `refs/quasithin.pdf`.
-/

public section

open Subgroup

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate

/-- An actual characteristic cubic subgroup contained in the image supplies
a proper nonzero Frattini subgroup for every compatible actor. -/
theorem actorReducible_of_characteristic_cubic
    {R H : Type*} [Group R] [Finite R] [IsElementaryAbelian 3 R] [Group H]
    (hR : Nat.card R = 9) (D : Subgroup (MulAut R))
    (f : R →* H) (hf : Function.Injective f)
    (C : Subgroup H) [C.Characteristic] (hC : Nat.card C = 3)
    (hle : C ≤ f.range)
    (hact : ∀ a ∈ D, ∃ c : MulAut H, ∀ r : R, f (a r) = c (f r)) :
    ActorReducible D := by
  let A := C.comap f
  have hmap : A.map f = C := map_comap_eq_self hle
  have hAc : Nat.card A = 3 := by
    rw [← card_map_of_injective (K := A) hf, hmap, hC]
  have hAb : A ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hAc
    omega
  have hAt : A ≠ ⊤ := by
    intro h
    rw [h, card_top, hR] at hAc
    omega
  have hA : ∀ a ∈ D, ∀ r ∈ A, a r ∈ A := by
    intro a ha r hr
    obtain ⟨c, hc⟩ := hact a ha
    change f (a r) ∈ C
    rw [hc]
    exact characteristic_iff_le_comap.mp inferInstance c hr
  let _ : Fact (IsPGroup 3 R) := ⟨IsElementaryAbelian.isPGroup 3 R⟩
  let q := QuotientGroup.mk' (frattini R)
  have hq : Function.Injective q := by
    apply q.ker_eq_bot_iff.mp
    rw [QuotientGroup.ker_mk', frattini_eq_bot_of_isElementaryAbelian (p := 3)]
  refine ⟨A.map q, ?_, ?_, ?_⟩
  · intro h
    exact hAb ((A.map_eq_bot_iff_of_injective hq).mp h)
  · intro h
    apply hAt
    apply map_injective hq
    rw [h, map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  · rintro a ha _ ⟨r, hr, rfl⟩
    exact ⟨a r, hA a ha r hr, (quotientAut_apply_mk _ _ _).symm⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate
