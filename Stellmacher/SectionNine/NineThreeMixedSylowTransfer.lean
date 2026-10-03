module
public import Stellmacher.SectionNine.NineThreeMixedGeometry
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Conjugating a two-element subgroup into a Sylow centralizer

If a local group is transitive on the nonidentity elements of a subgroup
containing an order-two subgroup, and that larger subgroup has a nontrivial
Sylow-fixed element, a local conjugate of the Sylow centralizes the given
order-two subgroup. The inverse of the vector transporter is used, matching
the explicit `MulAut.conj` convention.

This isolates the final transport in Stellmacher (9.3), printed p.50/PDF p.40
of `refs/files/stellmacher-n-group.pdf`. It does not assume that the whole
commutator plane is Sylow-invariant, nor that quotient actor centralizers
lift to literal actor centralizers.
-/

namespace Stellmacher.SectionNine

public theorem conjugate_centralizes_order_two_of_transitive
    {G : Type*} [Group G] [Finite G]
    (localGroup sylow mixed plane : Subgroup G)
    (hcard : Nat.card mixed = 2) (hplane : mixed ≤ plane)
    (hfixed : plane ⊓ Subgroup.centralizer (sylow : Set G) ≠ ⊥)
    (htransitive : ∀ first ∈ plane, first ≠ 1 →
      ∀ second ∈ plane, second ≠ 1 →
      ∃ conjugator ∈ localGroup, (MulAut.conj conjugator) first = second) :
    ∃ conjugator : G, conjugator ∈ localGroup ∧
      sylow.map (MulAut.conj conjugator).toMonoidHom ≤
        Subgroup.centralizer (mixed : Set G) := by
  obtain ⟨vector, hvector, hunique⟩ := (Nat.card_eq_two_iff' (1 : mixed)).mp hcard
  have hvectorNe : (vector : G) ≠ 1 := by
    intro heq
    exact hvector (Subtype.ext heq)
  obtain ⟨fixed, hfixedNe⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hfixed
  have hfixedNe' : (fixed : G) ≠ 1 := by
    intro heq
    exact hfixedNe (Subtype.ext heq)
  obtain ⟨conjugator, hlocal, hconjugate⟩ := htransitive
    vector (hplane vector.property) hvectorNe fixed fixed.property.1 hfixedNe'
  refine ⟨conjugator⁻¹, localGroup.inv_mem hlocal, ?_⟩
  rintro member ⟨original, horiginal, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro element helement
  by_cases hidentity : element = 1
  · simp [hidentity]
  · have heq : element = vector := congrArg Subtype.val
      (hunique ⟨element, helement⟩ (fun heq => hidentity (congrArg Subtype.val heq)))
    rw [heq]
    have hcomm := Subgroup.mem_centralizer_iff.mp fixed.property.2 original horiginal
    have hback : (MulAut.conj conjugator⁻¹) (fixed : G) = vector := by
      rw [← hconjugate]
      simp [MulAut.conj_apply, mul_assoc]
    have htransport := congrArg (MulAut.conj conjugator⁻¹) hcomm
    simp only [map_mul, hback] at htransport
    simpa [MulAut.conj_apply] using htransport.symm

open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_three_mixed_order_two_and_sylow_of_action
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second)
    (horder :
      let m := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
      Nat.card (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ m,
        ZAt ctx.Γ m ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G) = 2)
    (haction :
      let m := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
      let plane := (⁅ZAt ctx.Γ ctx.criticalPath.a,
        ZAt ctx.Γ m ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
      plane ⊓ Subgroup.centralizer (T : Set G) ≠ ⊥ ∧
        ∀ vector ∈ plane, vector ≠ 1 → ∀ target ∈ plane, target ≠ 1 →
          ∃ conjugator ∈ GAt ctx.Γ ctx.criticalPath.a,
            (MulAut.conj conjugator) vector = target) :
    let m := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ m,
      ZAt ctx.Γ m ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
    Nat.card mixed = 2 ∧ ∃ conjugator : G,
      conjugator ∈ GAt ctx.Γ ctx.criticalPath.a ∧
      T.map (MulAut.conj conjugator).toMonoidHom ≤
        Subgroup.centralizer (mixed : Set G) := by
  refine ⟨horder, conjugate_centralizes_order_two_of_transitive
    (GAt ctx.Γ ctx.criticalPath.a) T _ _ horder ?_ haction.1 haction.2⟩
  exact Subgroup.commutator_mono inf_le_left le_rfl

end Stellmacher.SectionNine
