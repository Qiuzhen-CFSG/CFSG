module
public import Stellmacher.MaxElementaryOffenderEquality
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.ThreeSubgroups

/-!
# Saturation by a maximum elementary replacement

Let W ≤ U ≤ S be elementary abelian, and let E be elementary abelian in S.
If W C_E(W) is maximum in S and C_E(W)=C_E(U), then maximality puts U
inside W C_E(W). Thus E acts trivially on U/W. If K normalizes U and W,
and K=[K,E], the three-subgroups lemma gives [U,K]≤W. In particular a
fully moved U equals W. All normality here is relative.

Source application: Aschbacher–Smith 13.4.7(2), the first replacement
case on printed p.902.
-/

public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Equal actor kernels make a maximum elementary replacement contain the
larger module, on whose quotient the actor is therefore trivial. -/
theorem commutator_le_of_maximum_replacement
    (S W U E : Subgroup G) [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 E]
    (hWU : W ≤ U) (hUS : U ≤ S) (hES : E ≤ S)
    (hEW : E ≤ normalizer (W : Set G))
    (hmax : W ⊔ (E ⊓ centralizer (W : Set G)) ∈ elementaryAbelianMaxSubgroups S)
    (hker : E ⊓ centralizer (W : Set G) = E ⊓ centralizer (U : Set G)) :
    U ≤ W ⊔ (E ⊓ centralizer (W : Set G)) ∧ ⁅U,E⁆ ≤ W := by
  let C := E ⊓ centralizer (W : Set G)
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le inf_le_left
  have hCU : C ≤ centralizer (U : Set G) := hker.le.trans inf_le_right
  let : IsElementaryAbelian 2 (U ⊔ C : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hCU
  have hle : W ⊔ C ≤ U ⊔ C := sup_le_sup_right hWU C
  have heq : W ⊔ C = U ⊔ C := eq_of_le_of_card_ge hle
    (hmax.2.2 _ (sup_le hUS (inf_le_left.trans hES)) inferInstance)
  have hUB : U ≤ W ⊔ C := le_sup_left.trans_eq heq.symm
  refine ⟨hUB, (commutator_mono hUB le_rfl).trans ?_⟩
  apply commutator_sup_le_of_relative_normal (normalizer (W : Set G)) W C E W le_rfl
    W.le_normalizer (inf_le_right.trans (centralizer_le_normalizer _))
    (le_normalizer_iff_commutator_le_left.mp hEW)
  exact (commutator_eq_bot_iff_le_centralizer.mpr
    (inf_le_left.trans (le_centralizer E))).le.trans bot_le

/-- Full component movement turns the saturated replacement into equality
of the original and enlarged modules. -/
theorem eq_of_maximum_replacement_of_full_actor
    (S W U E K : Subgroup G) [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 E]
    (hWU : W ≤ U) (hUS : U ≤ S) (hES : E ≤ S)
    (hEW : E ≤ normalizer (W : Set G))
    (hKW : K ≤ normalizer (W : Set G)) (hKU : K ≤ normalizer (U : Set G))
    (hmax : W ⊔ (E ⊓ centralizer (W : Set G)) ∈ elementaryAbelianMaxSubgroups S)
    (hker : E ⊓ centralizer (W : Set G) = E ⊓ centralizer (U : Set G))
    (hKE : ⁅K,E⁆ = K) (hUK : ⁅U,K⁆ = U) : U = W := by
  have hUE := (commutator_le_of_maximum_replacement S W U E
    hWU hUS hES hEW hmax hker).2
  have hUW : U ≤ normalizer (W : Set G) :=
    ((le_centralizer U).trans (centralizer_le hWU)).trans (centralizer_le_normalizer _)
  have hUKW : ⁅K,U⁆ ≤ W := by
    rw [←hKE]
    apply commutator_commutator_le_of_rotate_of_le_normalizer hKW hEW hUW
    · rw [commutator_comm E U]
      exact (commutator_mono hUE le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hKW)
    · have hUKle : ⁅U,K⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp hKU
      exact (commutator_mono hUKle (le_refl E)).trans hUE
  rw [commutator_comm,hUK] at hUKW
  exact le_antisymm hUKW hWU

end Subgroup
