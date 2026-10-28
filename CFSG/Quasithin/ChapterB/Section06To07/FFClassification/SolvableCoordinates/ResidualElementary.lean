module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.SolvableCoordinates.WreathActor
public import Theory.GroupTheory.WreathTwoResidual
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The actual elementary cubic residual of the small natural actor

The single factor embeds its residual in A₃. The full wreath residual has
the existing literal two-axis cubic coordinates. Transporting through the
whole natural actor equivalences therefore proves that the original
residual is elementary abelian of exponentthree.

Source: the first step of Aschbacher–Smith13.2.9, printedp.880.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB

private theorem symmetric_three_residual_elementary :
    IsElementaryAbelian 3 (pResidual 2 (Equiv.Perm (Fin 3))) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup,Nat.card_fin]
    rfl
  let : IsCyclic (alternatingGroup (Fin 3)) := isCyclic_of_prime_card hc
  let : IsElementaryAbelian 3 (alternatingGroup (Fin 3)) := {
    exponent_dvd_p := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro x
      have hx := pow_card_eq_one' (x := x)
      rwa [hc] at hx }
  have hle : pResidual 2 (Equiv.Perm (Fin 3)) ≤ alternatingGroup (Fin 3) := by
    apply sInf_le
    refine ⟨inferInstance,IsPGroup.of_card (n := 1) ?_⟩
    change (alternatingGroup (Fin 3)).index = 2^1
    simp
  exact IsElementaryAbelian.of_injective (inclusion hle) (inclusion_injective hle)

private theorem residual_elementary_of_equiv {G D : Type*} [Group G] [Finite G] [Group D]
    (e : G ≃* D) [IsElementaryAbelian 3 (pResidual 2 D)] :
    IsElementaryAbelian 3 (pResidual 2 G) := by
  let i : pResidual 2 G →* pResidual 2 D :=
    (e.toMonoidHom.comp (pResidual 2 G).subtype).codRestrict _
      (fun x => (map_pResidual_le 2 e.toMonoidHom) (mem_map_of_mem _ x.property))
  apply IsElementaryAbelian.of_injective i
  intro x y h
  apply Subtype.ext
  exact e.injective (congrArg Subtype.val h)

/-- The constructed source actor's residual is genuinely elementary cubic. -/
theorem SmallNaturalWreathAction.residual_elementary
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} (h : SmallNaturalWreathAction ρ) :
    IsElementaryAbelian 3 (pResidual 2 G) := by
  rcases h with ⟨_,e,_⟩ | ⟨e,_,_⟩
  · obtain ⟨eS⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
    let := symmetric_three_residual_elementary
    exact residual_elementary_of_equiv (e.trans eS)
  · obtain ⟨eC⟩ := WreathTwoResidual.residual_equiv_elementaryNine
    let : IsElementaryAbelian 3 (Multiplicative (Fin 2 → ZMod 3)) := {
      exponent_dvd_p := by
        apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        exact (by decide +kernel : ∀ x : Multiplicative (Fin 2 → ZMod 3),x^3=1) }
    let : IsElementaryAbelian 3 (pResidual 2 WreathTwoResidual.Actor) :=
      IsElementaryAbelian.of_injective eC.toMonoidHom eC.injective
    exact residual_elementary_of_equiv e
end CFSG.Quasithin.ChapterB
