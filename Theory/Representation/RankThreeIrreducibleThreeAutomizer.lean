module

public import Theory.Representation.AbelianWeightNormalizerSolvable
public import Theory.GroupTheory.SmallIndexSolvable
public import Theory.Representation.RankThreeThreeGroupWeightBase
public import Theory.GroupTheory.PGroup.AbelianIndexThreeNormalizerOrbit
public import Mathlib.GroupTheory.PGroup

/-!
# Solvable automizers of absolutely irreducible three-groups in GL₃

An abelian subgroup with abelian ambient centralizer has solvable normalizer
in degree three. If its normalizer meets the original subgroup's normalizer
in index at most four, the coset action proves that the latter is solvable
as well. Its induced automizer is a homomorphic image.

A nonabelian three-group in cross characteristic has an abelian index-three
subgroup with abelian ambient centralizer, obtained from its character weights.
The normalizer has an orbit of size at most four on these subgroups. Combining
these structural results discharges both premises of the solvability reduction.
No characteristic-subgroup assumption is required.

Source: Aschbacher–Smith, Lemma A.3.21(c), printed pp. 55–56.
-/

public section

namespace Representation

/-- A small orbit of an abelian subgroup with abelian centralizer suffices
for solvability of a degree-three matrix automizer. -/
theorem rankThree_automizer_isSolvable_of_abelian_normalizer_index
    {F : Type*} [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (hp : 3 ≠ p) (Q A : Subgroup (GL (Fin 3) F)) (hA : IsPGroup 3 A)
    [IsMulCommutative A]
    [IsMulCommutative (Subgroup.centralizer (A : Set (GL (Fin 3) F)))]
    (hi : (Subgroup.normalizer (A : Set (GL (Fin 3) F))).relIndex
      (Subgroup.normalizer (Q : Set (GL (Fin 3) F))) ≤ 4) :
    Group.IsSolvable Q.normalizerMonoidHom.range := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have horder : (Nat.card A : F) ≠ 0 := by
    obtain ⟨a, ha⟩ := hA.exists_card_eq
    rw [ha, Nat.cast_pow]
    apply pow_ne_zero
    rw [Ne, CharP.cast_eq_zero_iff]
    exact fun h => hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
      (by decide : Nat.Prime 3)).mp h).symm
  let : Group.IsSolvable (Subgroup.normalizer (A : Set (GL (Fin 3) F))) :=
    generalLinear_normalizer_isSolvable_of_abelian_centralizer 3 (by decide) A horder
  let : Group.IsSolvable (Subgroup.normalizer (Q : Set (GL (Fin 3) F))) :=
    Subgroup.isSolvable_of_relIndex_le_four _ _ hi
  exact Group.isSolvable_of_surjective Q.normalizerMonoidHom.rangeRestrict_surjective

/-- The automizer of an absolutely irreducible nonabelian three-subgroup of
GL₃ over a finite field of characteristic different from three is solvable. -/
theorem rankThree_automizer_isSolvable_of_absolutelyIrreducible_threeGroup
    {F : Type*} [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (hp : 3 ≠ p) (Q : Subgroup (GL (Fin 3) F)) (hQ : IsPGroup 3 Q)
    (hn : ¬ IsMulCommutative Q)
    (hirr : IsAbsolutelyIrreducible ((generalLinearNatural (F := F) 3).comp Q.subtype)) :
    Group.IsSolvable Q.normalizerMonoidHom.range := by
  obtain ⟨A, _hAn, hAc, hi, hcentralizer⟩ :=
    generalLinear_absolutelyIrreducible_threeGroup_weightBase p hp Q hQ hn hirr
  let : IsMulCommutative A := hAc
  let : IsMulCommutative (Subgroup.centralizer
      ((A.map Q.subtype : Subgroup (GL (Fin 3) F)) : Set (GL (Fin 3) F))) := hcentralizer
  exact rankThree_automizer_isSolvable_of_abelian_normalizer_index p hp Q
    (A.map Q.subtype) ((hQ.to_subgroup A).map Q.subtype)
    (Subgroup.normalizer_relIndex_le_four_of_abelian_index_three Q hQ hn A hAc hi)

end Representation
