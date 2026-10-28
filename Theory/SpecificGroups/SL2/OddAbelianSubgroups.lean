module

public import Theory.Representation.QuadraticFourGroup.Recognition.FactorSylows.Linear
public import Mathlib.GroupTheory.SpecificGroups.ZGroup

/-!
# Odd abelian subgroups in binary SL₂

A finite odd abelian group with a faithful determinant-one representation
of degree two in characteristic two is cyclic. Its odd Sylow subgroups
are cyclic by the eigenline argument; its Sylow two-subgroup is trivial.
The cyclic Sylow criterion for finite nilpotent groups finishes the proof.

This supplies the inverted-subgroup consequence of GLS, Volume 4,
Chapter 4, Lemma 3.7 used in Chapter 2, Proposition 16.5, without requiring
the full classification of proper subgroups of PSL₂.
-/

namespace Matrix.SL2

/-- A faithful binary degree-two representation makes an odd abelian
finite group cyclic. No restriction to a prime field is needed. -/
public theorem odd_abelian_isCyclic_of_injective
    {F : Type*} [Field F] [CharP F 2]
    {A : Type*} [Group A] [Finite A] [IsMulCommutative A]
    (hodd : Odd (Nat.card A))
    (ρ : A →* Matrix.SpecialLinearGroup (Fin 2) F) (hρ : Function.Injective ρ) :
    IsCyclic A := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  let : IsZGroup A := ⟨fun p hp P => by
    let : Fact p.Prime := ⟨hp⟩
    by_cases hp2 : p = 2
    · subst p
      have hsub : Subsingleton P := by
        apply subsingleton_of_forall_eq 1
        intro x
        by_contra hx
        have hd := dvd_trans (P.isPGroup'.dvd_orderOf hx) (orderOf_dvd_natCard x)
        exact hodd.not_two_dvd_nat
          (dvd_trans hd (P : Subgroup A).card_subgroup_dvd_card)
      let := hsub
      infer_instance
    · exact odd_pGroup_isCyclic_of_injective P.isPGroup' hp2
        (ρ.comp (P : Subgroup A).subtype) (hρ.comp Subtype.val_injective)⟩
  infer_instance

end Matrix.SL2
