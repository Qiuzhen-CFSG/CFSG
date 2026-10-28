module

public import Theory.Mathieu.M12.Properties.SylowAutomorphisms

/-!
# Faithful actions fixing an M₁₂ Sylow subgroup

Every faithful group of automorphisms fixing a Sylow two-subgroup of the actual
Witt-design M₁₂ pointwise has order at most two. Sylow conjugacy transports the
action to the marked common Sylow subgroup. Its pointwise automorphism
stabilizer consists of the identity and conjugation by the distinguished
central involution, by `SylowAutomorphisms.eq_one_or_conj_of_fixes_sylow`.

This is the intrinsic component obstruction used for the M₁₂ and Aut(M₁₂)
alternatives of Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, F.6.18(12)–(13), printed pp.309–310, in the
proof of 15.4.18, printed pp.1162–1163. The marked local calculation is reused
from `SylowAutomorphisms`; no outer-automorphism order bound is required.
-/

open Subgroup
namespace Sporadic.Mathieu
open M12SmallPair

/-- A faithful automorphism action fixing any Sylow two-subgroup of the actual
Witt-design M₁₂ pointwise has at most two actors. -/
public theorem m12_faithful_sylow_fixed_action_card_le_two
    {A : Type*} [Group A] (P : Sylow 2 M12)
    (ρ : A →* MulAut M12) (hinj : Function.Injective ρ)
    (hfixed : ∀ a : A, ∀ x : P, ρ a x = x) : Nat.card A ≤ 2 := by
  classical
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M12 commonSylow P
  let e : MulAut M12 := MulAut.conj g
  let ρ' : A →* MulAut M12 := (MulAut.conj e⁻¹).toMonoidHom.comp ρ
  have hinj' : Function.Injective ρ' := (MulAut.conj e⁻¹).injective.comp hinj
  have hfixed' (a : A) (x : M12) (hx : x ∈ sylowCandidate) : ρ' a x = x := by
    have hmem : e x ∈ P := by
      rw [← hg]
      change e x ∈ sylowCandidate.map e.toMonoidHom
      exact mem_map_of_mem e.toMonoidHom hx
    have hf := hfixed a ⟨e x, hmem⟩
    change e⁻¹ (ρ a (e x)) = x
    rw [hf]
    exact e.symm_apply_apply x
  let j : A → ({1, MulAut.conj z} : Finset (MulAut M12)) := fun a =>
    ⟨ρ' a, by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using
        SylowAutomorphisms.eq_one_or_conj_of_fixes_sylow (ρ' a) (hfixed' a)⟩
  have hj : Function.Injective j := fun a b hab => hinj' (congrArg Subtype.val hab)
  have hcard := Nat.card_le_card_of_injective j hj
  have htwo : Nat.card ({1, MulAut.conj z} : Finset (MulAut M12)) ≤ 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact Finset.card_le_two
  exact hcard.trans htwo

end Sporadic.Mathieu
