module

public import Theory.SpecificGroups.SymmetricFive.OuterFourGeometry
public import Theory.SpecificGroups.SymmetricFive.AutomorphismRank
public import CFSG.Quasithin.ChapterE.Section01.Inheritance
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.OddSections

/-!
# E₁ generation for a positioned outer four-group in S₅

The dihedral local of order twelve has the original actor as its Sylow
intersection. Triviality of the ambient two-core and the actor centralizer
calculation give precisely the ambient tau condition. The intrinsic E₁
quotient and its rank-one actor image come from `PrimeGeometry.OddSections`.
Conjugation transports this actual local member, including every quotient
map, to the given actor and Sylow subgroup. Its join with that Sylow is S₅.

Source: Aschbacher–Smith E.1.2(E1), E.1.5 and E.1.8, pp.210–211;
application to E.1.14(7), p.214, and Aschbacher (1982), Lemma 4.11.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.FiveGeneration
open Theory.SpecificGroups.SymmetricFive.OuterFourGeometry

/-- The concrete D₁₂ is an E₁ member for the specified outer four-group. -/
theorem standard_member : IsEMemberAt 1 eight four localGroup := by
  let : Nontrivial four := Finite.one_lt_card_iff_nontrivial.mp (by rw [four_card]; decide)
  have hfour : IsKleinFour four := ⟨four_card, IsElementaryAbelian.exponent_eq_prime⟩
  have ho : ECaseOdd four localGroup :=
    PSLTwoGeneration.PrimeGeometry.eCaseOdd_of_localModel four localGroup hfour four_le_local
      (Or.inr ⟨3, Nat.prime_three, by decide, ⟨localEquiv⟩⟩)
  have htau : tau eight four = four :=
    PSLTwoGeneration.PrimeGeometry.tau_eq_self_of_selfCentralizing standardSylow four
      four_le_eight Theory.SpecificGroups.SymmetricFive.pCore_two_eq_bot four_centralizer
  have hr : Group.rank ((four.subgroupOf localGroup).map
      (QuotientGroup.mk' (pCore 2 localGroup))) = 1 := ho.choose_spec.2.2.2.2.2
  exact ⟨⟨inferInstance, four_le_eight, four_le_local,
    (by rw [htau]; exact le_inf four_le_eight four_le_local), local_sylow, Or.inl ho⟩,
    Or.inl ⟨ho, hr.le⟩⟩

/-- Every positioned outer four-group has a genuine E₁ member which generates
S₅ with the given Sylow subgroup. -/
theorem exists_generating_member (S : Sylow 2 (Equiv.Perm (Fin 5)))
    (B : Subgroup (Equiv.Perm (Fin 5))) (hB : IsElementaryAbelian 2 B)
    (hcard : Nat.card B = 4) (hBS : B ≤ (S : Subgroup _))
    (hout : ¬ B ≤ alternatingGroup (Fin 5)) :
    ∃ H : Subgroup (Equiv.Perm (Fin 5)),
      IsEMemberAt 1 (S : Subgroup _) B H ∧ H ⊔ (S : Subgroup _) = ⊤ := by
  let := hB
  obtain ⟨e, hS, hBe⟩ := exists_marking S B hcard hBS hout
  have hSr : eight.map e.symm.toMonoidHom = (S : Subgroup _) := by
    rw [← hS]
    simp [map_map]
  have hBr : four.map e.symm.toMonoidHom = B := by
    rw [← hBe]
    simp [map_map]
  refine ⟨localGroup.map e.symm.toMonoidHom, ?_, ?_⟩
  · have hm := IsEMemberAt.map_equiv standard_member e.symm
    rwa [hSr, hBr] at hm
  · have hg := congrArg (Subgroup.map e.symm.toMonoidHom) local_sup_eight
    simpa only [Subgroup.map_sup, hSr,
      map_top_of_surjective e.symm.toMonoidHom e.symm.surjective] using hg

/-- Local E₁ generation for an outer four-group in S₅. The inner four-group
case is deliberately absent from the statement. -/
theorem positioned_four_generation (S : Sylow 2 (Equiv.Perm (Fin 5)))
    (B : Subgroup (Equiv.Perm (Fin 5))) (hB : IsElementaryAbelian 2 B)
    (hcard : Nat.card B = 4) (hBS : B ≤ (S : Subgroup _))
    (hout : ¬ B ≤ alternatingGroup (Fin 5)) :
    eSubgroup 1 (S : Subgroup _) B ⊔ (S : Subgroup _) = ⊤ := by
  obtain ⟨H, hH, hg⟩ := exists_generating_member S B hB hcard hBS hout
  apply top_unique
  rw [← hg]
  exact sup_le_sup_right (show H ≤ eSubgroup 1 (S : Subgroup _) B from le_sSup hH) _
end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.FiveGeneration
