module
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.Index
public import Theory.GroupTheory.PGroup.Omega
import Mathlib.Tactic

/-!
# Omega normalizer transfer at prime relative index

For finite subgroups, a proper subgroup of a finite nilpotent group has a
strictly larger normalizer.  If that normalizer is contained in an overgroup
where the original subgroup has prime relative index, relative-index
multiplication forces the overgroup back into the nilpotent group.  A
characteristic `Ω₁` subgroup supplies the required normalizer containment:
normalizers of `U` normalize its image in the ambient group.  The public
transfer theorem applies this argument to `U = S ∩ C_G(T)`, `R = S ∩ K`, and
`D = S ∩ N_G(T)`; the explicit hypotheses retain the local content needed by
the parent ABG argument without importing that application layer.
-/

namespace Subgroup

private theorem le_of_prime_relIndex_of_normalizer_le
    {G : Type*} [Group G] [Finite G]
    (U R D : Subgroup G) [Group.IsNilpotent R]
    (hUR : U < R) (hUD : U ≤ D)
    (hindex : Nat.Prime (U.relIndex D))
    (hnorm : R ⊓ normalizer (U : Set G) ≤ D) : D ≤ R := by
  have hproper : U.subgroupOf R < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, subgroupOf_eq_top]
    exact not_le_of_gt hUR
  have hlt := Group.normalizerCondition_of_isNilpotent (U.subgroupOf R) hproper
  obtain ⟨element, helement, houtside⟩ := SetLike.exists_of_lt hlt
  have hnormalizer : (element : G) ∈ normalizer (U : Set G) := by
    rw [← subgroupOf_normalizer_eq hUR.le] at helement
    exact helement
  have hinD : (element : G) ∈ D := hnorm ⟨element.property, hnormalizer⟩
  have hUinf : U ≤ D ⊓ R := le_inf hUD hUR.le
  have hnotone : U.relIndex (D ⊓ R) ≠ 1 := by
    intro heq
    exact houtside (relIndex_eq_one.mp heq ⟨hinD, element.property⟩)
  have hmul := relIndex_mul_relIndex U (D ⊓ R) D hUinf inf_le_left
  have hfactor : U.relIndex (D ⊓ R) = U.relIndex D :=
    ((Nat.dvd_prime hindex).mp ⟨(D ⊓ R).relIndex D, hmul.symm⟩).resolve_left hnotone
  have hother : (D ⊓ R).relIndex D = 1 := by
    rw [hfactor] at hmul
    exact (Nat.mul_left_cancel hindex.pos (hmul.trans (Nat.mul_one _).symm))
  exact (relIndex_eq_one.mp hother).trans inf_le_right

private theorem normalizer_le_normalizer_omega
    {G : Type*} [Group G] (U : Subgroup G) :
    normalizer (U : Set G) ≤
      normalizer (((omega₁ U (p := 2)).map U.subtype : Subgroup G) : Set G) := by
  classical
  apply le_normalizer_iff.mpr
  intro element helement point hpoint
  obtain ⟨pointU, hpointU, rfl⟩ := mem_map.mp hpoint
  let automorphism := normalizerMonoidHom U ⟨element, helement⟩
  have hfix := (omega₁_characteristic U (p := 2)).fixed automorphism
  have himage : automorphism pointU ∈ omega₁ U (p := 2) := by
    change pointU ∈ (omega₁ U (p := 2)).comap automorphism.toMonoidHom
    rw [hfix]
    exact hpointU
  exact ⟨automorphism pointU, himage, by
    simp [automorphism, normalizerMonoidHom_apply_apply_coe, mul_assoc]⟩

public theorem normalizer_le_of_centralizer_lt_of_omega
    {G : Type*} [Group G] [Finite G]
    (S K T : Subgroup G) (hS : IsPGroup 2 S)
    (hproper : S ⊓ centralizer (T : Set G) < S ⊓ K)
    (homega : (omega₁ ↥(S ⊓ centralizer (T : Set G)) (p := 2)).map
      (S ⊓ centralizer (T : Set G)).subtype = T)
    (hindex : (S ⊓ centralizer (T : Set G)).relIndex
      (S ⊓ normalizer (T : Set G)) = 2) :
    S ⊓ normalizer (T : Set G) ≤ K := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Group.IsNilpotent ↥(S ⊓ K) :=
    (hS.of_injective (inclusion inf_le_left)
      (inclusion_injective inf_le_left)).isNilpotent
  have hnorm := normalizer_le_normalizer_omega (S ⊓ centralizer (T : Set G))
  rw [homega] at hnorm
  exact (le_of_prime_relIndex_of_normalizer_le
    (S ⊓ centralizer (T : Set G)) (S ⊓ K)
    (S ⊓ normalizer (T : Set G)) hproper
    (inf_le_inf_left S (centralizer_le_normalizer _))
    (hindex ▸ Nat.prime_two)
    (fun _ helement => ⟨helement.1.1, hnorm helement.2⟩)).trans inf_le_right

end Subgroup
