module

public import Theory.SpecificGroups.PSL3Three.EightGeometry.Transport

/-!
# Full automorphism geometry in the outer case of Lemma 2.5.15

The source identifies its actual action group with Aut(PSL₃(3)) and its
component image with the inner subgroup. The concrete model now supplies
conjugacy of all elementary eights, conjugacy of all outer involutions,
and the marked elementary-eight two-core attached to every inner four.
No conjugacy or graph marking is an additional input.

Source: Aschbacher--Smith, Lemma 2.5.15, printed pp.558--559. The source
assembly supplies its original action-group identification and transports
these facts to the direct product with the marked central involution.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
variable {A : Type*} [Group A]

/-- Elementary-eight fusion in the actual source action group. -/
theorem linear_three_action_eight_fusion (e : A ≃* MulAut Matrix.PSL3Three.PSL)
    (B C : Subgroup A) (hB : IsElementaryAbelian 2 B) (hBc : Nat.card B = 8)
    (hC : IsElementaryAbelian 2 C) (hCc : Nat.card C = 8) :
    ∃ a : A, B.map (MulAut.conj a).toMonoidHom = C :=
  Matrix.PSL3Three.EightGeometry.eight_conjugate_of_equiv e B C hB hBc hC hCc

/-- Outer involution fusion retains the original component image K. -/
theorem linear_three_action_outer_fusion (e : A ≃* MulAut Matrix.PSL3Three.PSL)
    (K : Subgroup A) (hK : K = (MulAut.innerSubgroup Matrix.PSL3Three.PSL).comap e.toMonoidHom)
    (f g : A) (hf : orderOf f = 2) (hg : orderOf g = 2) (hfo : f ∉ K) (hgo : g ∉ K) :
    IsConj f g := by
  apply Matrix.PSL3Three.EightGeometry.outer_involutions_conjugate_of_equiv e f g hf hg
  · exact fun h => hfo (hK ▸ h)
  · exact fun h => hgo (hK ▸ h)

/-- The exact source normalizer core and its S₄ graph marking. -/
theorem linear_three_action_four_core (e : A ≃* MulAut Matrix.PSL3Three.PSL)
    (K : Subgroup A) (hK : K = (MulAut.innerSubgroup Matrix.PSL3Three.PSL).comap e.toMonoidHom)
    (E : Subgroup A) (hEK : E ≤ K) (hE : IsElementaryAbelian 2 E) (hc : Nat.card E = 4) :
    let F := centralizer (E : Set A)
    IsElementaryAbelian 2 F ∧ Nat.card F = 8 ∧
    (pCore 2 (normalizer (E : Set A))).map (normalizer (E : Set A)).subtype = F ∧
    ∃ f : A, orderOf f = 2 ∧ f ∉ K ∧
      K ⊓ centralizer ({f} : Set A) = K ⊓ normalizer (E : Set A) ∧
      Nonempty ((K ⊓ normalizer (E : Set A) : Subgroup A) ≃* Equiv.Perm (Fin 4)) ∧
      F = E ⊔ zpowers f := by
  subst K
  exact Matrix.PSL3Three.EightGeometry.inner_four_structure_of_equiv e E hEK hE hc

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
