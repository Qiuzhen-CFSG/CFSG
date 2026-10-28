module

public import Theory.Alternating.proposition_5_2_7_8
public import Theory.Representation.HexacodeAction.Cover
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Outer involutions invert the center of the triple A₆ cover

The two determinant-minus-one normal forms on the standard nine-subgroup
both invert the cubic center. In the exceptional case we change the marking
of the covering projection by the normalizing permutation. This avoids any
assumption that that permutation lifts to an automorphism of the cover.

Source: GLS3 5.2.3 and 5.2.7; the actor application is Aschbacher–Smith
K.1–K.1.3, printed pp.452–453.
-/

public section
open Subgroup Theory.GroupTheory
namespace GLS3.Chapter5.TripleSixActorInversion

theorem center_inverted_of_noninner_quotient
    {E : Type} [Group E] [Finite E] [IsQuasisimple E]
    (f : Covering E (alternatingGroup (Fin 6)))
    (hker : Nat.card f.toMonoidHom.ker = 3)
    (x : MulAut E) (β : MulAut (alternatingGroup (Fin 6)))
    (hcompat : ∀ k : E, f (x k) = β (f k))
    (hβ : orderOf β = 2)
    (hout : ∀ g : alternatingGroup (Fin 6), β ≠ MulAut.conj g) :
    ∀ z : E, z ∈ center E → x z = z⁻¹ := by
  obtain ⟨δ, hX, hY⟩ | ⟨τ, δ, hX, hY⟩ :=
    a6_noninner_standardNine_normalForm β hβ hout
  · exact tripleCoverA6_center_inverted_of_reflection_normalForm
      f hker x β hcompat δ hX hY
  · let a : MulAut (alternatingGroup (Fin 6)) := MulAut.conjNormal τ
    let f' : Covering E (alternatingGroup (Fin 6)) := {
      toMonoidHom := a.symm.toMonoidHom.comp f.toMonoidHom
      surjective := a.symm.surjective.comp f.surjective }
    have hker' : Nat.card f'.toMonoidHom.ker = 3 := by
      change Nat.card (a.symm.toMonoidHom.comp f.toMonoidHom).ker = 3
      rw [MonoidHom.ker_comp_of_injective _ _ a.symm.injective]
      exact hker
    have hc : ∀ k : E, f' (x k) = (a⁻¹ * β * a) (f' k) := by
      intro k
      change a.symm (f (x k)) = a.symm (β (a (a.symm (f k))))
      rw [a.apply_symm_apply, hcompat]
    exact tripleCoverA6_center_inverted_of_matrix_normalForm
      f' hker' x (a⁻¹ * β * a) hc δ
      (by simpa only [mul_assoc] using hX)
      (by simpa only [mul_assoc] using hY)

open Atlas.Codes Representation

/-- Every non-inner involution of the actual even hexacode group inverts its center. -/
theorem hexEven_center_inverted (x : MulAut HexEvenAutomorphisms)
    (hx : x ^ 2 = 1) (hout : ∀ a : HexEvenAutomorphisms, x ≠ MulAut.conj a) :
    ∀ z : HexEvenAutomorphisms, z ∈ center HexEvenAutomorphisms → x z = z⁻¹ := by
  let := Hexacode.even_isQuasisimple
  let e := Hexacode.even_quotient_center_equiv
  let q := MulAut.centralQuotientAction e
  let β := q x
  have hβout : ∀ a : alternatingGroup (Fin 6), β ≠ MulAut.conj a := by
    intro a ha
    obtain ⟨b, hb⟩ := (MulAut.centralQuotientAction_inner_iff e x).mp ⟨a, ha⟩
    exact hout b hb
  have hβ : orderOf β = 2 := by
    apply orderOf_eq_prime
    · change q x ^ 2 = 1
      rw [← map_pow, hx, map_one]
    · intro h
      exact hβout 1 (h.trans (map_one MulAut.conj).symm)
  let f : Covering HexEvenAutomorphisms (alternatingGroup (Fin 6)) := {
    toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center HexEvenAutomorphisms))
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective _) }
  have hk : Nat.card f.toMonoidHom.ker = 3 := by
    change Nat.card (e.toMonoidHom.comp (QuotientGroup.mk' _)).ker = 3
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
    exact Hexacode.even_center_card
  exact center_inverted_of_noninner_quotient f hk x β
    (fun k => (MulAut.centralQuotientAction_apply e x k).symm) hβ hβout

end GLS3.Chapter5.TripleSixActorInversion
