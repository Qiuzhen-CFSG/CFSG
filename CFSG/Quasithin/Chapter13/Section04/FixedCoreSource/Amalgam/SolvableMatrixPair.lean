module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CyclicComponent
public import CFSG.Quasithin.ChapterF.Section06.Elementary.PrimeToThree.DistinctCores
public import Theory.SpecificGroups.SL2.PrimeFieldOddSubgroups

/-!
# Solvable Goldschmidt pairs in prime-field GL₂

The two-residual of a Goldschmidt pair lies in its derived subgroup, so
all odd Sylow subgroups have determinant one in a faithful matrix action.
Odd prime subgroups of SL₂ over a prime field are cyclic. In particular
the three-core of the prime-to-three quotient is cyclic. If the vertex
two-cores differed, that quotient would retain a Goldschmidt triple;
F.6.17 would give a quasisimple component, contradicting solvability.

This proves the equal-core consequence of the Dickson argument in
Aschbacher--Smith 13.4.7, printed p.901, without classifying the matrix
range. It needs faithfulness only on that range, not on the original
prime-core action, whose full kernel may be nontrivial.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
variable {G : Type*} [Group G] [Finite G]

/-- The literal faithful prime-field action makes every odd Sylow cyclic. -/
theorem pair_odd_sylow_cyclic_of_prime_matrix
    {A B : Subgroup G} (hg : ChapterF.IsGoldschmidtTriple A B)
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hr : r ≠ 2)
    (f : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p))
    (hf : Function.Injective f) (S : Sylow r G) : IsCyclic S := by
  have hS : (S : Subgroup G) ≤ pResidual 2 G := by
    intro x hx
    apply mem_pResidual_of_orderOf_coprime
    obtain ⟨n,hn⟩ := S.isPGroup' ⟨x,hx⟩
    have hp : x ^ (r ^ n) = 1 := congrArg Subtype.val hn
    exact (((Nat.coprime_primes Nat.prime_two (Fact.out : r.Prime)).mpr
      hr.symm).pow_right n).of_dvd_right (orderOf_dvd_of_pow_eq_one hp)
  let d := Matrix.GeneralLinearGroup.det.comp f
  have hd : (S : Subgroup G) ≤ d.ker := hS.trans
    ((ChapterF.Cyclic.triple_residual_le_derived hg).trans
      (Abelianization.commutator_subset_ker d))
  let j : S →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) := {
    toFun := fun s => ⟨(f s.val).val, congrArg Units.val (hd s.property)⟩
    map_one' := by apply Subtype.ext; exact congrArg Units.val f.map_one
    map_mul' := by intro s t; apply Subtype.ext; exact congrArg Units.val (f.map_mul s.val t.val) }
  have hj : Function.Injective j := by
    intro s t he
    apply Subtype.ext
    apply hf
    apply Units.ext
    exact congrArg Subtype.val he
  exact Matrix.SpecialLinearGroup.isCyclic_of_odd_pGroup_injective_primeField
    S.isPGroup' hr j hj

private theorem cyclic_core_of_cyclic_sylow_quotient
    {H : Type*} [Group H] [Finite H]
    {r : ℕ} [Fact r.Prime] (S : Sylow r G) (hS : IsCyclic S)
    (q : G →* H) (hq : Function.Surjective q) : IsCyclic (pCore r H) := by
  let : IsCyclic S := hS
  let P := S.mapSurjective hq
  let : IsCyclic P := isCyclic_of_surjective (q.subgroupMap (S : Subgroup G))
    (q.subgroupMap_surjective _)
  exact isCyclic_of_le (pCore_isPGroup.le_sylow_of_normal P)

/-- A solvable Goldschmidt pair in prime-field GL₂ has equal vertex two-cores. -/
theorem solvable_pair_matrix_cores_equal
    {A B : Subgroup G} (hg : ChapterF.IsGoldschmidtTriple A B)
    (hs : Group.IsSolvable G) {p : ℕ} [Fact p.Prime]
    (f : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod p))
    (hf : Function.Injective f) : A.pCoreIn 2 = B.pCoreIn 2 := by
  by_contra hne
  let Q := G ⧸ pPrimeCore 3 G
  let q := QuotientGroup.mk' (pPrimeCore 3 G)
  let S : Sylow 3 G := Classical.choice inferInstance
  have hc := cyclic_core_of_cyclic_sylow_quotient S
    (pair_odd_sylow_cyclic_of_prime_matrix hg (by decide) f hf S)
    q (QuotientGroup.mk'_surjective _)
  have hq := hg.quotient_primeToThreeCore_of_distinct_cores hne
  obtain ⟨C,hC,_⟩ := ChapterF.Cyclic.exists_component_of_cyclic_three_core_quotient
    (MulEquiv.refl Q) hq hc
  let : Group.IsSolvable G := hs
  let : IsQuasisimple C := hC.2
  let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
  let : Nontrivial C := (QuotientGroup.mk'_surjective (center C)).nontrivial
  exact Group.IsPerfect.not_isSolvable C inferInstance
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
