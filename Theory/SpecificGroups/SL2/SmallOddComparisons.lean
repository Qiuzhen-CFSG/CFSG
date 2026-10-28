module

public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# The odd small-field PSL₂ exceptions

The faithful projective-line action shows that PSL₂(3) is solvable, hence
not perfect. Transport of the existing icosahedral comparison over the
five-element field gives PSL₂(5) ≃ PSL₂(4) for any field implementation.

These comparisons are used in Aschbacher--Smith, G.7.3(1), printed p.348.
The order-seven and order-nine comparisons are supplied separately by
`Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters`.
-/

public section

namespace Matrix.ProjectiveSpecialLinearGroup
open scoped MatrixGroups LinearAlgebra.Projectivization

/-- The projective action on four points rules out perfection at order three. -/
theorem not_perfect_of_card_three {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 3) : ¬ Group.IsPerfect PSL(2,F) := by
  classical
  intro hperfect
  let : Group.IsPerfect PSL(2,F) := hperfect
  let Ω := ℙ F (Fin 2 → F)
  let : Fintype Ω := Fintype.ofFinite _
  have hΩ : Nat.card Ω = 4 := by
    change Nat.card (ℙ F (Fin 2 → F)) = 4
    rw [Projectivization.card_of_finrank_two F (Fin 2 → F) (by simp), hF]
  let eΩ : Ω ≃ Fin 4 := Fintype.equivFinOfCardEq (by
    simpa only [Nat.card_eq_fintype_card] using hΩ)
  let f : PSL(2,F) →* Equiv.Perm (Fin 4) :=
    eΩ.permCongrHom.toMonoidHom.comp (MulAction.toPermHom PSL(2,F) Ω)
  have hf : Function.Injective f :=
    eΩ.permCongrHom.injective.comp MulAction.toPerm_injective
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable PSL(2,F) := Group.isSolvable_of_isSolvable_injective hf
  have hc := psl2_card_twice (F := F) (hF ▸ (by decide : Odd 3))
  rw [hF] at hc
  have hlarge : 1 < Nat.card PSL(2,F) := by omega
  let : Nontrivial PSL(2,F) := Finite.one_lt_card_iff_nontrivial.mp hlarge
  exact Group.IsPerfect.not_isSolvable PSL(2,F) inferInstance

/-- The characteristic-five exception is the actual binary PSL₂(4) group. -/
noncomputable def cardFiveEquivFour {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 5) : PSL(2,F) ≃* PSL(2, GaloisField 2 2) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fintype F := Fintype.ofFinite F
  let e : F ≃+* ZMod 5 := (ZMod.ringEquivOfPrime F (by decide : Nat.Prime 5)
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  exact (Atlas.fieldEquivPSL 2 e).trans five_equiv_four.some

end Matrix.ProjectiveSpecialLinearGroup
