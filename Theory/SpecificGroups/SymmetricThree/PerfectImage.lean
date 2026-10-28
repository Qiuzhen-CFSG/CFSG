module
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# Images of two-perfect groups in S₃

A homomorphism sends the two-residual into the two-residual. Hence every
image of a two-perfect group in S₃ lies in A₃, and every image element
has cube one. This retains the supplied homomorphism and element.

Source application: the original L₂,₊ = O²([L₂,T ∩ L]) conjugator in
Aschbacher–Smith, The Classification of Quasithin Groups, Notation 13.2.1
and Lemma 13.8.29(4), printed pp.877 and 964.
-/

public section
open Subgroup
namespace Equiv.Perm

/-- Every element in a two-perfect image in S₃ has cube one. -/
theorem cube_eq_one_of_isPPerfect {G : Type*} [Group G]
    (hG : IsPPerfect 2 G) (f : G →* Equiv.Perm (Fin 3)) (g : G) :
    f g ^ 3 = 1 := by
  have hm : f g ∈ pResidual 2 (Equiv.Perm (Fin 3)) :=
    map_pResidual_le 2 f ⟨g,by rw [(pResidual_eq_top_iff 2 G).mpr hG]; trivial,rfl⟩
  rw [twoResidual_eq_alternating] at hm
  have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup,Nat.card_fin]
    rfl
  exact congrArg Subtype.val
    (hc ▸ pow_card_eq_one' (x := (⟨f g,hm⟩ : alternatingGroup (Fin 3))))

end Equiv.Perm
