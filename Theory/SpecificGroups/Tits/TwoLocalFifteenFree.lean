module
public import Theory.SpecificGroups.ReeF4.SubfieldTitsEmbedding
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.TwoLocalOrders

/-!
# Fifteen-free two-local normalizers in the Tits group

The actual Parrott group embeds into the Ree group at parameter one. Under
this embedding the normalizer of a nontrivial two-subgroup embeds into the
normalizer of its image. The full Ree two-local order obstruction therefore
applies without a Sylow-containment or maximality premise.

Source: the Ree subfield construction and the two parabolic orders used in
Aschbacher--Smith C.3.5, printed p.150.
-/

public section
open Subgroup
namespace Tits

/-- Every normalizer of a nontrivial two-subgroup of the actual Tits model
has order indivisible by fifteen. -/
theorem normalizer_fifteen_free (P : Subgroup ParrottGroup)
    (hne : P ≠ ⊥) (hp : IsPGroup 2 P) :
    ¬ 15 ∣ Nat.card (normalizer (P : Set ParrottGroup)) := by
  obtain ⟨f,hf⟩ := ReeF4.Subfield.exists_tits_embedding 1
  have hne' : P.map f ≠ ⊥ := fun he => hne
    ((map_eq_bot_iff_of_injective P hf).mp he)
  have hN : (normalizer (P : Set ParrottGroup)).map f ≤
      normalizer (P.map f : Set (ReeF4.Model 1)) := P.le_normalizer_map f
  intro hd
  apply ReeF4.ConverseParabolics.normalizer_fifteen_free (by decide : 1 ≤ 1)
    (P.map f) hne' (hp.map f)
  have hc := card_dvd_of_le hN
  rw [card_map_of_injective hf] at hc
  exact hd.trans hc

end Tits
