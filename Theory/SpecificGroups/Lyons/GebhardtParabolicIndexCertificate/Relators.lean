module

public import Theory.SpecificGroups.Lyons.GebhardtParabolicIndexCertificate.LiteralRelators

/-!
# Realizing the nine parabolic relators in the fixed presentation

The literal signed words are compared in the free group with Gebhardt's
`parabolicRelators`. The three generators are then realized inside the actual
subgroup `LocalTower.parabolic`. Its generation proof uses only subgroup
closure, with no finiteness or order assumption.

Source: Gebhardt (2000), Section 3B, pp. 335–336.
-/

namespace Lyons.Gebhardt.ParabolicIndexCertificate
open Subgroup.CosetWordCertificate LocalTower

@[expose] public def embed (i : Fin 3) : Alphabet := ⟨i.val, by omega⟩
@[expose] public def localGenerator (i : Fin 3) : parabolic :=
  ⟨generator (embed i), generator_mem 3 (embed i) i.isLt⟩

private theorem relator_exact (i : Fin 9) :
    FreeGroup.map embed (FreeGroup.mk (relatorFin i)) =
      parabolicRelators[i.val]'(by change i.val < 9; exact i.isLt) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [relatorFin, parabolicRelators, word, letter, equationRelator,
      conjugate, commutatorWord, FreeGroup.map_eq_lift, FreeGroup.lift_mk,
      embed, pow_succ, mul_assoc]

private theorem relator_mem (i : Fin 9) :
    FreeGroup.map embed (FreeGroup.mk (relatorFin i)) ∈ parabolicRelators := by
  rw [relator_exact]
  exact List.getElem_mem _

public theorem relator_ok (r : Nat) : eval localGenerator (relatorWords r) = 1 := by
  by_cases hr : r < 9
  · simp only [relatorWords, dif_pos hr]
    apply Subtype.ext
    change (parabolic.subtype.comp (FreeGroup.lift localGenerator))
      (FreeGroup.mk (relatorFin ⟨r, hr⟩)) = 1
    rw [FreeGroup.lift_unique _ (f := fun i => generator (embed i)) (by intro i; rfl)]
    rw [← FreeGroup.lift_unique ((PresentedGroup.mk relators).comp (FreeGroup.map embed))
      (f := fun i => generator (embed i)) (by intro i; simp [generator, PresentedGroup.of])]
    exact parabolicRelator_eq_one _ (relator_mem ⟨r, hr⟩)
  · simp [relatorWords, hr]

public theorem localGenerator_generates : Subgroup.closure (Set.range localGenerator) = ⊤ := by
  apply Subgroup.map_injective parabolic.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  change Subgroup.closure _ = Subgroup.closure _
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨embed i, i.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨localGenerator ⟨i.val, hi⟩, ⟨⟨i.val, hi⟩, rfl⟩, ?_⟩
    rfl
end Lyons.Gebhardt.ParabolicIndexCertificate
