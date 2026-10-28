module

public import Theory.GroupTheory.CComponent.TwoComponent
public import Theory.GroupTheory.PPrimeCoreReduction

/-!
# Two-components in products with solvable or odd-core-free factors

If one factor is solvable, the projection of a perfect subgroup to that factor
is trivial. Its other projection is injective and retains subnormality, so a
trivial odd core in the other factor makes its intrinsic odd core trivial.
If both factors have trivial odd core, their product does too. These observations
make every two-component quasisimple when each factor is solvable or has trivial
odd core.

This is the product reduction used in the alternating-group case of GLS II,
Definition 2.4, with the centralizer structure of GLS III, Proposition 5.2.8(a).
-/

public section

open Subgroup Theory.GroupTheory

namespace Subgroup.IsTwoComponent
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

omit [Finite G] in
private theorem quasisimple_of_intrinsic_oddCore {L : Subgroup G} (hL : L.IsTwoComponent)
    (ho : pPrimeCore 2 L = ⊥) : IsQuasisimple L := by
  let := hL.2
  exact IsQuasisimple.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq ho).trans QuotientGroup.quotientBot)

omit [Finite G] in
private theorem quasisimple_prod_solvable_left [Group.IsSolvable G]
    {L : Subgroup (G × H)} (hL : L.IsTwoComponent)
    (hH : pPrimeCore 2 H = ⊥) : IsQuasisimple L := by
  let := hL.1.perfect
  have hf : ∀ x : L, x.val.1 = 1 := by
    let := Group.IsPerfect.map (H := L) (MonoidHom.fst G H)
    have hb : L.map (MonoidHom.fst G H) = ⊥ := by
      apply le_bot_iff.mp
      simpa only [solvableResidual_eq_bot] using
        le_solvableResidual_of_isPerfect (L.map (MonoidHom.fst G H))
    intro x
    exact mem_bot.mp (hb ▸ mem_map_of_mem (MonoidHom.fst G H) x.property)
  let f := (MonoidHom.snd G H).subgroupMap L
  have hi : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact Prod.ext ((hf x).trans (hf y).symm) (congrArg Subtype.val hxy)
  let e : L ≃* L.map (MonoidHom.snd G H) :=
    MulEquiv.ofBijective f ⟨hi, (MonoidHom.snd G H).subgroupMap_surjective L⟩
  apply hL.quasisimple_of_intrinsic_oddCore
  exact pPrimeCore_eq_bot_of_equiv e
    ((hL.1.subnormal.map Prod.snd_surjective).pPrimeCore_eq_bot hH)

/-- Two-components of a product are ordinary when each factor is solvable or has trivial odd core. -/
theorem isQuasisimple_prod_of_solvable_or_oddCore
    (hG : Group.IsSolvable G ∨ pPrimeCore 2 G = ⊥)
    (hH : Group.IsSolvable H ∨ pPrimeCore 2 H = ⊥)
    {L : Subgroup (G × H)} (hL : L.IsTwoComponent) : IsQuasisimple L := by
  rcases hG with hsG | hoG <;> rcases hH with hsH | hoH
  · let := hsG
    let := hsH
    exact (hL.1.not_isSolvable inferInstance).elim
  · let := hsG
    exact hL.quasisimple_prod_solvable_left hoH
  · let := hsH
    let e : G × H ≃* H × G := MulEquiv.prodComm
    have hq := (hL.map_equiv e).quasisimple_prod_solvable_left hoG
    exact IsQuasisimple.of_mulEquiv (e.subgroupMap L).symm (hG := hq)
  · exact (hL.isComponent_of_oddCore_eq_bot (pPrimeCore_prod_eq_bot hoG hoH)).2

end Subgroup.IsTwoComponent
