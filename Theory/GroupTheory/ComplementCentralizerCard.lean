module
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Subgroup.Centralizer
/-!
# Comparing centralizers through a normal complement

When a complement centralizes s, its full order contributes to C(s).
The relative-index formula bounds C(t) by the fixed part of the normal
subgroup times the same complement order. Comparing the two fixed parts
therefore compares the whole centralizers. The actual source application
is the chosen Hall-torus complement in Aschbacher–Smith 2.4.23(4).
-/
public section
open Subgroup
namespace Subgroup
variable {P : Type*} [Group P] [Finite P]
theorem card_centralizer_le_of_complement_core_card
    (R A : Subgroup P) [R.Normal] (hc : IsComplement' R A)
    (s t : P) (hAs : A ≤ centralizer ({s}:Set P))
    (hfixed : Nat.card (R ⊓ centralizer ({t}:Set P) : Subgroup P) ≤
      Nat.card (R ⊓ centralizer ({s}:Set P) : Subgroup P)) :
    Nat.card (centralizer ({t}:Set P)) ≤ Nat.card (centralizer ({s}:Set P)) := by
  let S := centralizer ({s}:Set P)
  let U := centralizer ({t}:Set P)
  have hsplit : (R ⊓ S) ⊔ A=S := by
    apply le_antisymm (sup_le inf_le_right hAs)
    intro g hg
    obtain ⟨⟨r,a⟩,he⟩ := hc.2 g
    have hrS : (r:P) ∈ S := by
      have hh := S.mul_mem hg (S.inv_mem (hAs a.property))
      rw [←he] at hh
      simpa only [mul_inv_cancel_right] using hh
    rw [←he]
    exact mul_mem_sup ⟨r.property,hrS⟩ a.property
  have hn : A≤normalizer (R ⊓ S : Set P) :=
    (le_inf le_normalizer_of_normal (hAs.trans S.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hsCard : Nat.card S=Nat.card (R ⊓ S : Subgroup P)*R.index := by
    calc
      Nat.card S = Nat.card ((R ⊓ S) ⊔ A : Subgroup P) := congrArg (fun B : Subgroup P => Nat.card B) hsplit.symm
      _ = Nat.card (R ⊓ S : Subgroup P)*Nat.card A :=
        card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn (hc.disjoint.mono inf_le_left le_rfl)
      _ = Nat.card (R ⊓ S : Subgroup P)*R.index := by rw [hc.symm.index_eq_card]
  have htCard := relIndex_mul_relIndex (⊥:Subgroup P) (R ⊓ U) U bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right] at htCard
  have hind : R.relIndex U≤R.index := by
    simpa only [relIndex_top_right] using relIndex_le_of_le_right
      (show U≤(⊤:Subgroup P) from le_top)
      (show R.relIndex (⊤:Subgroup P)≠0 by rw [relIndex_top_right];exact Subgroup.index_ne_zero_of_finite)
  change Nat.card U≤Nat.card S
  rw [←htCard,hsCard]
  exact Nat.mul_le_mul hfixed hind
end Subgroup
