module
public import Theory.SpecificGroups.SymmetricFourWreath.NormalElementaryGeometry
/-! The intrinsic extraspecial core times the marked central factor has index four
in the dihedral wreath Sylow group. Source: Aschbacher--Smith 2.4.29, p.545. -/
public section
open Subgroup
namespace SymmetricFourWreath
variable {D S : Type*} [Group D] [Finite D] [IsElementaryAbelian 2 D]
  [Group S] [Finite S]
theorem core_sup_factor_index (e : S ≃* P×D)
    (Q : Subgroup S) [Q.Normal] [IsExtraspecial 2 Q] (hQ : Nat.card Q=32) :
    (Q ⊔ ((MonoidHom.fst P D).comp e.toMonoidHom).ker).index = 4 := by
  let a := (MonoidHom.fst P D).comp e.toMonoidHom
  have ha : Function.Surjective a := fun p=>⟨e.symm (p,1),by simp [a]⟩
  rw [←relIndex_top_right,core_sup_factor_eq_comap_of_equiv_prod e Q hQ,
    relIndex_comap,map_top_of_surjective a ha,relIndex_top_right]
  have hh := coreInP.card_mul_index
  rw [card_coreInP,card_P] at hh
  omega
end SymmetricFourWreath
