module
public import Theory.SpecificGroups.PSL2.PrimeSylowFixers
public import GorensteinWalter.PGL2SplitTorus

/-!
# Removing the diagonal extension of PSL₂(17)

Prime-field automorphism coverage identifies Aut(PSL₂(17)) with PGL₂(17).
The inner subgroup has index two, and the split torus has an element of
order sixteen. Thus an automorphism subgroup containing every inner
automorphism and having no element of order sixteen is itself inner.

Source: the diagonal-actor step in Guralnick--Malle, Classification of
2F-modules I, Proposition 4.1, manuscript p.9.
-/

public section
namespace Theory.PSL2.SeventeenGeometry
open Subgroup GorensteinWalter
local instance : Fact (Nat.Prime 17) := ⟨by decide⟩
abbrev Model := Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 17)

/-- The full automorphism group contributes order sixteen as soon as a
subgroup containing the inner automorphisms has any outer element. -/
theorem le_inner_of_no_order_sixteen (J : Subgroup (MulAut Model))
    (hi : (MulAut.conj : Model →* MulAut Model).range ≤ J)
    (h16 : ∀ a ∈ J, orderOf a ≠ 16) :
    J ≤ (MulAut.conj : Model →* MulAut Model).range := by
  let hK : IsOddPrimePower (Nat.card (ZMod 17)) :=
    ⟨17, 1, by decide, by decide, by decide, by simp⟩
  have hc : 3 < Nat.card (ZMod 17) := by simp
  let f := pgl2InnerAutPSL2 (ZMod 17) hK hc
  let e : PGL2 (ZMod 17) ≃* MulAut Model := MulEquiv.ofBijective f
    ⟨pgl2InnerAutPSL2_injective _ _ _, Theory.PSL2.primeField_pgl_coverage
      (by decide : Odd 17) (by decide : 3 < 17)⟩
  let H : Subgroup (PGL2 (ZMod 17)) :=
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod 17)).range
  let K := J.comap e.toMonoidHom
  have hH : H.index = 2 := pgl2_psl2Range_index_eq_two _ hK
  have hHK : H ≤ K := by
    rintro _ ⟨s, rfl⟩
    change f (Matrix.ProjectiveSpecialLinearGroup.toPGL s) ∈ J
    rw [show f (Matrix.ProjectiveSpecialLinearGroup.toPGL s) = MulAut.conj s from
      pgl2InnerAutPSL2_toPGL _ _ _ s]
    exact hi ⟨s, rfl⟩
  have hKH : K ≤ H := by
    intro a ha
    by_contra haH
    have htop : K = ⊤ := by
      apply top_unique
      intro b _
      by_cases hb : b ∈ H
      · exact hHK hb
      · have hba : b * a⁻¹ ∈ H := (H.mul_mem_iff_of_index_two hH).mpr
          (by simp only [H.inv_mem_iff, hb, haH])
        simpa only [inv_mul_cancel_right] using K.mul_mem (hHK hba) ha
    obtain ⟨U, w, hU, hUc, _⟩ := pgl2_split_torus_reflection_data (ZMod 17)
    let : IsCyclic U := hU
    obtain ⟨z, hz⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := U)
    have hz16 : orderOf (e (z : PGL2 (ZMod 17))) = 16 := by
      rw [e.orderOf_eq, Subgroup.orderOf_coe, hz, hUc]
      simp
    exact h16 _ (show e (z : PGL2 (ZMod 17)) ∈ J from
      (show (z : PGL2 (ZMod 17)) ∈ K from htop ▸ mem_top _)) hz16
  intro a ha
  obtain ⟨b, rfl⟩ := e.surjective a
  obtain ⟨s, hs⟩ := hKH ha
  refine ⟨s, ?_⟩
  rw [← hs]
  exact (pgl2InnerAutPSL2_toPGL _ _ _ s).symm

end Theory.PSL2.SeventeenGeometry
