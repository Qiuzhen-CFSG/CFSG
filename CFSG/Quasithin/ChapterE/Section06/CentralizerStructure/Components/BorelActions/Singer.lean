module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.Reduction
public import Theory.GroupAction.BinarySingerRegularity

/-!
# The binary Singer action in the Borel case of E.6.11

A cyclic subgroup X of order 2^n - 1 normalizing an elementary abelian
subgroup W of order 2^n acts regularly on W minus its identity whenever
X intersects C_G(W) trivially. Restrict the actual normalizer action to X;
the normalizer action's kernel formula proves faithfulness. The intrinsic
binary Singer theorem then discharges `BinarySingerRegularity` from
`Reduction`, independently of the construction of a Borel model witness.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, E.6.11,
printed p.250, regularity of the cyclic complement on [V,X] minus its identity.
-/

open Subgroup

namespace CFSG.Quasithin.ChapterE.Section06.Components.BorelActions

/-- The actual conjugation action satisfies binary Singer regularity in every
finite ambient group. -/
public theorem binarySingerRegularity {G : Type*} [Group G] [Finite G] :
    BinarySingerRegularity (G := G) := by
  intro W X n hn hel hW he hnorm hdis
  obtain ⟨e⟩ := he
  let := hel
  let : IsCyclic X := isCyclic_of_injective e.toMonoidHom e.injective
  have hpos : 0 < 2 ^ n - 1 := by
    have := Nat.lt_two_pow_self (n := n)
    omega
  let : NeZero (2 ^ n - 1) := ⟨ne_of_gt hpos⟩
  have hX : Nat.card X = 2 ^ n - 1 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]
  let ρ : X →* MulAut W := W.normalizerMonoidHom.comp (inclusion hnorm)
  have hρ : Function.Injective ρ := by
    apply ρ.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro x hx
    apply mem_bot.mpr
    apply Subtype.ext
    have hxC : (x : G) ∈ centralizer (W : Set G) := by
      have hker : inclusion hnorm x ∈ W.normalizerMonoidHom.ker := hx
      rw [W.normalizerMonoidHom_ker] at hker
      exact hker
    exact mem_bot.mp (hdis ▸ (show (x : G) ∈ X ⊓ centralizer (W : Set G) from
      ⟨x.property, hxC⟩))
  refine ⟨hnorm, ?_⟩
  intro a ha ha1 b hb hb1
  have ha' : (⟨a, ha⟩ : W) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hb' : (⟨b, hb⟩ : W) ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  obtain ⟨x, hx, huniq⟩ :=
    Theory.GroupAction.faithful_cyclic_binary_singer_regular
      ρ hρ hn hX hW ⟨a, ha⟩ ⟨b, hb⟩ ha' hb'
  refine ⟨x, congrArg Subtype.val hx, ?_⟩
  intro y hy
  exact huniq y (Subtype.ext hy)

end CFSG.Quasithin.ChapterE.Section06.Components.BorelActions
