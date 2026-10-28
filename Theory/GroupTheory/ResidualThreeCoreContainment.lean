module
public import Theory.GroupTheory.ResidualTwoByThreeJoin
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# Two-core containment from a three-group residual quotient

The two-core of a two-residual has trivial image whenever the target
residual is a three-group. In a group with S3 two-core quotient, a normal
subgroup of order prime to three is a two-group, by the order formula.
Consequently intersecting an ambient prime-to-three core with that local
group lands in the local two-core.

Source application: the first containment in Aschbacher--Smith 13.2.13,
The Classification of Quasithin Groups, printed p.883. The application
retains the original residual and both literal subgroup inclusions.
-/

public section
open Subgroup
namespace Subgroup
variable {G D : Type*} [Group G] [Group D] [Finite G] [Finite D]

omit [Finite G] [Finite D] in
/-- A two-core in a two-residual has trivial image in a group whose two-residual is a three-group. -/
theorem residual_twoCore_map_eq_bot_of_three_residual
    (f : G →* D) (hD : IsPGroup 3 (pResidual 2 D)) :
    ((pCore 2 (pResidual 2 G)).map (pResidual 2 G).subtype).map f = ⊥ := by
  let K := ((pCore 2 (pResidual 2 G)).map (pResidual 2 G).subtype).map f
  have hK : IsPGroup 2 K := (pCore_isPGroup.map _).map _
  have hle : K ≤ pResidual 2 D :=
    (map_mono (map_subtype_le _)).trans (map_pResidual_le 2 f)
  simpa only [inf_idem] using
    (IsPGroup.disjoint_of_ne 2 3 (by decide) K K hK (hD.to_le hle)).eq_bot

/-- A normal subgroup of order prime to three in an S3 extension by a two-group lies in its two-core. -/
theorem normal_primeToThree_le_twoCore_of_symmetricThree
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3))
    (N : Subgroup G) [N.Normal] (hc : Nat.Coprime 3 (Nat.card N)) :
    N ≤ pCore 2 G := by
  apply le_sSup
  refine ⟨inferInstance,?_⟩
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
  have hd := N.card_subgroup_dvd_card
  rw [SymmetricThreeTwoCore.card_eq e,hn] at hd
  have hd' : Nat.card N ∣ 3 * 2 ^ (n+1) := by
    convert hd using 1
    ring
  exact IsPGroup.of_card_dvd_pow (hc.symm.dvd_mul_left.mp hd')

/-- Intersecting the prime-to-three core with such a local subgroup lands in the local two-core. -/
theorem inf_primeToThreeCore_le_twoCore
    (P : Subgroup G) (e : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) :
    P ⊓ pPrimeCore 3 G ≤ P.pCoreIn 2 := by
  let N := (pPrimeCore 3 G).comap P.subtype
  have hc : Nat.Coprime 3 (Nat.card N) :=
    pPrimeCore_coprime_card.of_dvd_right
      (card_comap_dvd_of_injective (pPrimeCore 3 G) P.subtype P.subtype_injective)
  have hn := normal_primeToThree_le_twoCore_of_symmetricThree e N hc
  rintro x ⟨hxP,hxN⟩
  exact mem_map_of_mem P.subtype (hn (show (⟨x,hxP⟩ : P) ∈ N from hxN))

end Subgroup
