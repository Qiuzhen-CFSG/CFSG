module

public import Theory.GroupAction.FiveFourSquareFixed

/-!
# Fixed layers for a Sylow subgroup in a five-four action

Suppose a finite group acts on elementary sixteen through a faithful
five-four quotient. A subgroup fixed by a Sylow two-subgroup after passage
through a homomorphism with kernel of order at most two has order at most
four. Conjugate an order-four complement element into the Sylow image;
it fixes exactly two quotient points, and each fiber has at most two points.

Source: the five-four fixed-point calculation of Parrott (1972), pp.673–674,
and the derived-quotient argument in Thompson VI, printed p.630.
-/

namespace Theory.GroupAction
open Subgroup

/-- A layer fixed modulo a kernel of order at most two by a Sylow subgroup
in a faithful five-four quotient action has order at most four. -/
public theorem five_four_sylow_fixed_layer_card_le_four
    {H U W : Type*} [Group H] [Finite H] [Group U] [Finite U]
    [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 16)
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (hφ : Function.Injective φ)
    (π : H →* SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ)
    (hπ : Function.Surjective π)
    (action : H →* MulAut W) (hkernel : π.ker = action.ker)
    (T : Sylow 2 H) (q : U →* W) (hq : Nat.card q.ker ≤ 2)
    (E : Subgroup U)
    (hfixed : ∀ t ∈ (T : Subgroup H), ∀ e : E, action t (q e) = q e) :
    Nat.card E ≤ 4 := by
  classical
  let M := SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ
  let _ : Finite M := Finite.of_equiv
    (Multiplicative (ZMod 5) × Multiplicative (ZMod 4)) SemidirectProduct.equivProd.symm
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let a : M := SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 4))
  have ha : orderOf a = 4 := by
    rw [orderOf_injective SemidirectProduct.inr SemidirectProduct.inr_injective]
    simp [orderOf_ofAdd_eq_addOrderOf]
  have hp : IsPGroup 2 (zpowers a) := IsPGroup.of_card (n := 2)
    (by rw [Nat.card_zpowers, ha]; decide)
  obtain ⟨T₀, hT₀⟩ := hp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq M T₀ (T.mapSurjective hπ)
  have hb : MulAut.conj c a ∈ ((T.mapSurjective hπ : Sylow 2 M) : Subgroup M) := by
    rw [← hc]
    exact mem_map_of_mem (MulAut.conj c).toMonoidHom (hT₀ (mem_zpowers a))
  obtain ⟨t, ht, htb⟩ := hb
  have ht4 : orderOf (π t) = 4 := by
    rw [htb]
    exact (orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective a).trans ha
  let f := π.liftOfSurjective hπ ⟨action, hkernel.le⟩
  have hfactor (p : H) : f (π p) = action p :=
    MonoidHom.liftOfRightInverse_comp_apply π (Function.surjInv hπ)
      (Function.rightInverse_surjInv hπ) ⟨action, hkernel.le⟩ p
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply bot_unique
    intro b hb
    obtain ⟨p, rfl⟩ := hπ b
    have hp : p ∈ action.ker := by
      change action p = 1
      exact (hfactor p).symm.trans hb
    rw [← hkernel] at hp
    exact hp
  have hF := (five_four_sixteen_order_four_fixed_cards hW φ hφ f hf (π t) ht4).1
  let F := FixedPoints.subgroup (zpowers (f (π t))) W
  let r : E →* W := q.comp E.subtype
  have hker : Nat.card r.ker ≤ 2 := by
    let i : r.ker → q.ker := fun e => ⟨e.val.val, e.property⟩
    have hi : Function.Injective i := by
      intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun v : q.ker => (v : U)) hab))
    exact (Nat.card_le_card_of_injective i hi).trans hq
  have hrange : r.range ≤ F := by
    rintro v ⟨e, rfl⟩
    apply (MulAut.mem_fixed_zpowers_iff _ _).mpr
    rw [hfactor]
    exact hfixed t ht e
  have hcard := r.ker.card_mul_index
  rw [index_ker] at hcard
  calc
    Nat.card E = Nat.card r.ker * Nat.card r.range := hcard.symm
    _ ≤ 2 * Nat.card F := Nat.mul_le_mul hker (card_le_of_le hrange)
    _ = 4 := by rw [hF]

end Theory.GroupAction
