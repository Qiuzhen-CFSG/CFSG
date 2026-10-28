module

public import CFSG.Quasithin.ChapterE.Section01.Basic
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.OddSections.Common
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Symmetric-three sections for the small graph extension

A surjection from a local subgroup to S₃ with two-group kernel identifies
that kernel with the intrinsic two-core. Every elementary two-subgroup
with nontrivial image then satisfies all of E.1.2(E1), including the
commutator equality and rank exactly one in the actual two-core quotient.
The final constructor retains the ambient tau and Sylow-intersection
conditions separately, for use with the graph extension's local geometry.

Source: Aschbacher--Smith, E.1.2 and E.1.5, printed pp.209--210;
application to E.1.14(7), printed p.214.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree
open PSLTwoGeneration.PrimeGeometry.OddSections

private theorem alternating_three_selfCentralizing :
    centralizer (alternatingGroup (Fin 3) : Set (Equiv.Perm (Fin 3))) ≤
      alternatingGroup (Fin 3) := by
  intro x hx
  exact (show ∀ x : Equiv.Perm (Fin 3),
    (∀ y : Equiv.Perm (Fin 3), y ∈ alternatingGroup (Fin 3) → y * x = x * y) →
      x ∈ alternatingGroup (Fin 3) by
        simp only [Equiv.Perm.mem_alternatingGroup]
        decide +kernel) x (mem_centralizer_iff.mp hx)

variable {G : Type*} [Group G] [Finite G]

/-- The two-group kernel is proved to be O₂(K); the actor's image and its
rank are transported through the canonical quotient map. -/
theorem eCaseOdd_of_symmetricThree_quotient (A K : Subgroup G)
    (hA : IsElementaryAbelian 2 A) (hAK : A ≤ K)
    (f : K →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (ha : ¬ A.subgroupOf K ≤ f.ker) :
    ECaseOdd A K := by
  let _ := hA
  let _ : IsElementaryAbelian 2 (A.subgroupOf K) :=
    IsElementaryAbelian.subgroupOf hAK
  let _ : IsElementaryAbelian 2 ((A.subgroupOf K).map f) :=
    IsElementaryAbelian.map f
  have hne : (A.subgroupOf K).map f ≠ ⊥ :=
    fun h => ha ((Subgroup.map_eq_bot_iff _).mp h)
  refine ⟨3, Nat.prime_three, by decide, ?_⟩
  apply intrinsic_of_epimorphism (A.subgroupOf K) f hf
    (ker_eq_twoCore_of_surjective_perm_three f hf hk)
  exact primeSection Nat.prime_three (by decide) (alternatingGroup (Fin 3))
    (by rw [nat_card_alternatingGroup]; norm_num [Nat.factorial])
    (by norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial])
    alternating_three_selfCentralizing _ hne

/-- Actual E1 membership from a local symmetric-three quotient, with the
literal ambient tau and intrinsic Sylow intersection supplied by geometry. -/
theorem isEMemberAt_of_symmetricThree_quotient (T A K : Subgroup G)
    (hA : IsElementaryAbelian 2 A) (hAT : A ≤ T) (hAK : A ≤ K)
    (htau : tau T A ≤ K)
    (hSyl : ∃ S : Sylow 2 K, (S : Subgroup K) = T.subgroupOf K)
    (f : K →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (ha : ¬ A.subgroupOf K ≤ f.ker) :
    IsEMemberAt 1 T A K := by
  have ho := eCaseOdd_of_symmetricThree_quotient A K hA hAK f hf hk ha
  refine ⟨⟨hA, hAT, hAK, le_inf (tau_le _ _) htau, hSyl, Or.inl ho⟩,
    Or.inl ⟨ho, ?_⟩⟩
  obtain ⟨p, hp, hodd, hq, hne, hcomm, hrank⟩ := ho
  exact hrank.le

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree
