module
public import Theory.GroupTheory.ElementaryEightFixedPointOrder24
public import Theory.SpecificGroups.SymmetricFourSylow
import all Theory.GroupTheory.ElementaryEightFixedPointOrder24

/-! An order-eight automorphism group of an elementary eight fixing a
nonidentity point is dihedral. The existing action on the four affine
characters embeds it in S₄, where it is Sylow. Source: 14.3.19. -/

public section
open Subgroup

/-- The faithful four-character action identifies a point-fixing eight as D₈. -/
theorem elementaryEight_fixed_point_order8_equiv_D8
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hcard : Nat.card E = 8) (z : E) (hz : z ≠ 1)
    (A : Subgroup (MulAut E)) (hA : Nat.card A = 8)
    (hfix : ∀ a : A, (a : MulAut E) z = z) :
    Nonempty (A ≃* DihedralGroup 4) := by
  classical
  let (z : V) : Fintype (X z) := Subtype.fintype _
  let e := coord E hcard
  let conjugate : MulAut E ≃* MulAut V := MulAut.congr e
  let B := A.map conjugate.toMonoidHom
  let ab : A ≃* B := A.equivMapOfInjective conjugate.toMonoidHom conjugate.injective
  have hfixB : ∀ b : B, (b : MulAut V) (e z) = e z := by
    intro b
    obtain ⟨a, rfl⟩ := ab.surjective b
    change e ((a : MulAut E) (e.symm (e z))) = e z
    rw [e.symm_apply_apply, hfix a]
  have hzne : e z ≠ 1 := by
    intro he
    exact hz (e.injective (he.trans (e.map_one).symm))
  let r := (rep B hfixB).comp ab.toMonoidHom
  have hr : Function.Injective r := (rep_injective hzne B hfixB).comp ab.injective
  have hc : Nat.card (X (e z)) = 4 := by rw [Nat.card_eq_fintype_card]; exact countX _ hzne
  let f:A→*Equiv.Perm (Fin 4) :=
    (Equiv.permCongrHom (Finite.equivFinOfCardEq hc)).toMonoidHom.comp r
  have hf:Function.Injective f := (Equiv.permCongrHom (Finite.equivFinOfCardEq hc)).injective.comp hr
  have hfcard:Nat.card f.range=8 :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans hA
  let S:Sylow 2 (Equiv.Perm (Fin 4)) := Sylow.ofCard f.range (by
    rw [hfcard]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
    rw [show 24 = 2 ^ 3 * 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization])
  obtain ⟨d⟩ := Equiv.Perm.sylow_two_equiv_dihedral_four S
  exact ⟨(MonoidHom.ofInjective hf).trans d⟩
