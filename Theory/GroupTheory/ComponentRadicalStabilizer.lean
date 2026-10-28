module
public import Theory.GroupTheory.ComponentSaturatedSylow
public import Theory.GroupTheory.PRadical
public import Theory.GroupTheory.RadicalNormalizerControl
/-!
# Radical stabilizers of components

Let Q be a radical p-subgroup and L an ordinary component. Its stabilizer
R = N_Q(L) is the p-core of its normalizer inside LR. More generally this
holds when Q is saturated under an actor A: every A-invariant p-subgroup
lies in Q. The p-core of N_{LR}(R) factors over R, and its intersection
with L is controlled by the commuting component-orbit saturation theorem.

This is the ordinary-component part of Aschbacher, *Some results on pushing
up in finite groups*, Math. Z. 177 (1981), Lemma 8.2(5), used in 10.3;
the literal C-component quotient transport for C.2.4 is separate.
-/
public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem IsComponent.stabilizer_radical_of_saturation
    {L A Q : Subgroup G} (hL : IsComponent G L)
    (hQ : IsPGroup p Q) (hAQ : A ≤ normalizer (Q : Set G))
    (hsat : ∀ P : Subgroup G, IsPGroup p P →
      A ≤ normalizer (P : Set G) → P ≤ Q) :
    let R := Q ⊓ normalizer (L : Set G)
    ((L ⊔ R) ⊓ normalizer (R : Set G)).pCoreIn p = R := by
  let R := Q ⊓ normalizer (L : Set G)
  let Y := (L ⊔ R) ⊓ normalizer (R : Set G)
  let P := Y.pCoreIn p
  have hAR : A ⊓ normalizer (L : Set G) ≤ normalizer (R : Set G) :=
    (le_inf (inf_le_left.trans hAQ) (inf_le_right.trans
      (normalizer (L : Set G)).le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hAY : A ⊓ normalizer (L : Set G) ≤ normalizer (Y : Set G) :=
    (le_inf ((le_inf inf_le_right hAR).trans (normalizer_inf_normalizer_le_normalizer_sup L R))
      (hAR.trans (normalizer (R : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hAP : A ⊓ normalizer (L : Set G) ≤ normalizer (P : Set G) :=
    hAY.trans (normalizer_le_normalizer_characteristic_image Y (pCore p Y))
  have hPLQ : P ⊓ L ≤ Q := hL.stabilizer_saturation hsat _ inf_le_right
    ((isPGroup_pCoreIn p Y).to_le inf_le_left)
    ((le_inf hAP inf_le_right).trans inf_normalizer_le_normalizer_inf)
  have hPN : P ≤ normalizer (L : Set G) :=
    (pCoreIn_le p Y).trans (inf_le_left.trans (sup_le L.le_normalizer inf_le_right))
  apply le_antisymm
  · intro x hx
    have hxprod : x ∈ (L : Set G) * (R : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left L R (show R ≤ normalizer (L : Set G) from inf_le_right)]
      exact ((pCoreIn_le p Y).trans inf_le_left) hx
    obtain ⟨l, hl, r, hr, he⟩ := hxprod
    have hRP : R ≤ P := le_pCoreIn_of_normalizes (hQ.to_le inf_le_left)
      (le_inf le_sup_right R.le_normalizer) inf_le_right
    have hlP : l ∈ P := by
      have hh := P.mul_mem hx (P.inv_mem (hRP hr))
      rwa [← he, mul_inv_cancel_right] at hh
    exact ⟨he ▸ Q.mul_mem (hPLQ ⟨hlP, hl⟩) hr.1, hPN hx⟩
  · exact le_pCoreIn_of_normalizes (hQ.to_le inf_le_left)
      (le_inf le_sup_right R.le_normalizer) inf_le_right

/-- The actual radical subgroup supplies the saturation needed above. -/
theorem IsComponent.stabilizer_radical {L Q : Subgroup G}
    [Fact p.Prime] (hL : IsComponent G L) (hq : IsPRadical p Q) :
    let R := Q ⊓ normalizer (L : Set G)
    ((L ⊔ R) ⊓ normalizer (R : Set G)).pCoreIn p = R := by
  apply hL.stabilizer_radical_of_saturation hq.isPGroup le_rfl
  intro P hp hn
  exact le_of_normalizer_le_normalizer_of_pCore_normalizer_le Q P
    hq.isPGroup hp hq.2.le hn

end Theory.GroupTheory
