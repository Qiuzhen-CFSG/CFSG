module

public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Displacement from inversion in a central quotient

Suppose an ambient actor inverts an odd-order element of the central quotient
of a normal subgroup. Choose any lift `y`. The actual commutator `[t,y]`
maps to the inverse square of the chosen quotient element, so its projective
order is unchanged. Its binary displacement is at most twice that of `t`.

No assertion about the order of the lift or the size of the central kernel
is needed. This allows displacement bounds for projective odd-order elements
to be used on the original representation of a central cover.

Source: the inverted order-seven argument in Guralnick–Malle,
*Classification of 2F-modules I*, Proposition 4.3, manuscript pp.10–11,
as used in Aschbacher–Smith K.2, printed p.453.
-/

public section
open Subgroup
namespace Representation.BinaryOffender

/-- Inversion of an odd-order projective element supplies an actual
commutator of the same projective order and at most twice the displacement.
The ambient actor itself need not have order two. -/
theorem exists_small_displacement_of_inverted_centralQuotient
    {G S V : Type*} [Group G] [Group S]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
    (e : L ⧸ center L ≃* S) (t : G) (s : S)
    (hodd : Odd (orderOf s))
    (hinv : MulAut.centralQuotientAction e (MulAut.conjNormal t) s = s⁻¹) :
    ∃ x : L, orderOf (e (QuotientGroup.mk' (center L) x)) = orderOf s ∧
      fixedCodim (ρ.comp L.subtype) (zpowers x) ≤
        2 * fixedCodim ρ (zpowers t) := by
  obtain ⟨z, hz⟩ := e.surjective s
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (center L) z
  have hys : e (QuotientGroup.mk' (center L) y) = s := by rw [hy, hz]
  let x : L := MulAut.conjNormal t y * y⁻¹
  have hx : e (QuotientGroup.mk' (center L) x) = (s ^ 2)⁻¹ := by
    change e (QuotientGroup.mk' (center L) (MulAut.conjNormal t y * y⁻¹)) = _
    rw [map_mul, map_inv, map_mul, map_inv,
      ← MulAut.centralQuotientAction_apply, hys, hinv]
    group
  refine ⟨x, ?_, ?_⟩
  · rw [hx, orderOf_inv]
    exact hodd.coprime_two_right.orderOf_pow
  · have hcodim : fixedCodim (ρ.comp L.subtype) (zpowers x) =
        fixedCodim ρ (zpowers (x : G)) := by
      simp only [fixedCodim_zpowers_eq_displacement_rank]
      rfl
    rw [hcodim]
    exact fixedCodim_commutator_le_twice ρ t y

end Representation.BinaryOffender
