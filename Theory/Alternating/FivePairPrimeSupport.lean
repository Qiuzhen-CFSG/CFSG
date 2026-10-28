module
public import Theory.Alternating.FivePairTypeCover

/-!
# Prime support of the automorphisms of an A₅ pair

The inner group is a quotient of A₅ × A₅, and the outer group is a two-group.
Thus the full automorphism group has prime divisors only two, three and five.
This allows a faithful odd actor on the pair to be located using the actual
prime-to-three and prime-to-five residuals of its ambient group.

Source application: Aschbacher–Smith, 10.2.3, printed p.745.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.AlternatingFive

/-- Every prime divisor of Aut(A₅ × A₅) is two, three or five. -/
theorem pair_automorphism_isPGroup_thirty :
    IsPGroup 30 (MulAut (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) := by
  let A := alternatingGroup (Fin 5) × alternatingGroup (Fin 5)
  have ha : IsPGroup 30 A := IsPGroup.of_card_dvd_pow (n := 4) (by
    dsimp [A]
    rw [Nat.card_prod, nat_card_alternatingGroup]
    norm_num [Nat.factorial])
  have hi : IsPGroup 30 (MulAut.innerSubgroup A) :=
    ha.of_surjective MulAut.conj.rangeRestrict MulAut.conj.rangeRestrict_surjective
  have ho : IsPGroup 30 (MulAut.Outer A) := by
    have hh := normal_pair_outer_isPGroup_two (MonoidHom.id A) Function.injective_id
    have hh' : IsPGroup 2 (MulAut.Outer A) :=
      hh.of_equiv (MulAut.outerCongr ((MonoidHom.ofInjective Function.injective_id).symm))
    exact hh'.mono (by decide)
  have hk : IsPGroup 30 (QuotientGroup.mk' (MulAut.innerSubgroup A)).ker := by
    rw [QuotientGroup.ker_mk']
    exact hi
  have hh := (ho.to_subgroup ⊤).comap_of_ker_isPGroup
    (QuotientGroup.mk' (MulAut.innerSubgroup A)) hk
  simpa using hh.of_equiv Subgroup.topEquiv

end Theory.AlternatingFive
