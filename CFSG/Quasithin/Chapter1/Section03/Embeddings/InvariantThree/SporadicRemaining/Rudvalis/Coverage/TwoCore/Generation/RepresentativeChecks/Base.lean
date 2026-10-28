module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.Representatives
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.WordMaps


/-!
# Soundness of Rudvalis representative checks

The certified orbital rigidity shows that two elements of the original
Rudvalis model are equal when their actions agree on the first five points.
Thus a recovery certificate needs only five point calculations. A fixed
34-letter certificate recovers the standard generator b from a and the
fourteen Sylow generators; recovering a alone then supplies both witnesses
in the exact inverse-closed extension alphabet.

The six representatives with empty sector word belong to max4 and hence
normalize its intrinsic two-core. The remaining representatives require
separate recovery or intrinsic-center normalization certificates.
No double-coset coverage, maximality, or local-order bound is assumed.

Source application: Aschbacher--Smith, printed p.511 (PDF p.528), citing
Aschbacher (1986), no.343. The permutations and generator words are the
preserved ATLAS data used by Representatives and WordMaps.
-/

namespace Rudvalis.SylowOvergroups.TwoCore.Generation.RepresentativeChecks
open Subgroup Representatives RadicalCoverage.SylowCertificate
open OuterNormalizer OuterNormalizer.RigidityCertificate
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration

/-- The precise normalization-or-recovery alternative used by the assembly. -/
@[expose] public def Alternative (i : Index) : Prop :=
  representative i ∈ normalizer (coreImage : Set Model) ∨
  representative i ∈ normalizer (centerImage fixedSylow : Set Model) ∨
  ∃ wa wb : List (Fin 30), extensionWord (representative i) wa = a ∧
    extensionWord (representative i) wb = b

/-- Certified orbital rigidity makes the first five points a base. -/
public theorem eq_of_five (g h : Model)
    (he : ∀ i : Fin 5, g • (i.castLE (by decide) : Fin 4060) = h • i.castLE (by decide)) :
    g = h := by
  have hfix : h⁻¹ * g = 1 := by
    apply Subtype.ext
    apply fix_five_eq_one
    · exact model_le_relationAut aPerm_mem_relationAut bPerm_mem_relationAut (h⁻¹ * g).property
    · intro x hx
      change (h⁻¹ * g) • x = x
      rw [mul_smul, show g • x = h • x from he ⟨x.val, hx⟩, inv_smul_smul]
  exact (inv_mul_eq_one.mp hfix).symm

@[expose] public def recoverBWord : List (Fin 30) :=
 [8, 19, 16, 29, 17, 0, 13, 3, 14, 4, 1, 0, 14, 13, 3, 14, 4, 1, 0, 14, 5, 2, 13, 3, 14, 4, 1, 0, 14, 4, 5, 9, 11, 8]

/-- The common recovery word is checked in the kernel on a certified base. -/
public theorem recoverB : extensionWord a recoverBWord = b := by
  apply eq_of_five
  have hh : ∀ x : Fin 5, LocalOrder.evalWord
      (extensionLetterMap Data.aMap Data.aMap) recoverBWord (x.castLE (by decide)) =
        Data.bMap (x.castLE (by decide)) := by decide +kernel
  intro x
  rw [extensionWord_smul a Data.aMap Data.aMap (fun _ => rfl) (fun _ => rfl)]
  exact hh x

/-- Word-subgroup closure substitutes a recovery of a into the common word for b. -/
public theorem recovery_of_a (g : Model) (wa : List (Fin 30))
    (ha : extensionWord g wa = a) :
    ∃ wb : List (Fin 30), extensionWord g wb = b := by
  let W := wordSubgroup (symmGen (extensionGenerators g)) symmInv
    (symmGen_inv (extensionGenerators g))
  have hc : candidate ≤ W := by
    apply (closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    refine ⟨[Fin.castAdd 15 j.castSucc], ?_⟩
    simp only [evalWord, symmGen, Fin.addCases_left, extensionGenerators,
      Fin.lastCases_castSucc, mul_one]
  have ha' : a ∈ W := ⟨wa, ha⟩
  have hle : closure (insert a (candidate : Set Model)) ≤ W := by
    apply (closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact ha'
    · exact hc hx
  exact hle (recoverB ▸ extensionWord_mem a recoverBWord)

@[expose] public def recoveryMap (i : Index) (w : List (Fin 30)) (x : Fin 4060) : Fin 4060 :=
  LocalOrder.evalWord
    (extensionLetterMap (representativeMap i) (representativeInverseMap i)) w x

/-- Five certified point evaluations imply the actual model-word equality. -/
public theorem recovers_a_of_five (i : Index) (w : List (Fin 30))
    (h : ∀ x : Fin 5, recoveryMap i w (x.castLE (by decide)) =
      Data.aMap (x.castLE (by decide))) :
    extensionWord (representative i) w = a := by
  apply eq_of_five
  intro x
  rw [extensionWord_smul _ _ _ (representative_smul i) (representative_inv_smul i)]
  exact h x

public theorem alternative_of_recovers_a (i : Index) (w : List (Fin 30))
    (h : extensionWord (representative i) w = a) : Alternative i := by
  obtain ⟨wb, hb⟩ := recovery_of_a (representative i) w h
  exact Or.inr (Or.inr ⟨w, wb, h, hb⟩)

private theorem localValue_mem (w : List (Fin 4)) : localValue w ∈ max4 := by
  have hx : max4Generators.1 ∈ max4 := subset_closure (Set.mem_insert _ _)
  have hy : max4Generators.2 ∈ max4 :=
    subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  apply max4.list_prod_mem
  intro g hg
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
  fin_cases j
  · exact hx
  · exact hy
  · exact max4.inv_mem hx
  · exact max4.inv_mem hy

public theorem core_of_sector_zero (i : Index) (hi : (coordinates i).2 = 0) :
    representative i ∈ normalizer (coreImage : Set Model) := by
  have hm : max4 ≤ normalizer (coreImage : Set Model) := by
    simpa only [coreImage, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (pCore 2 max4).le_normalizer_map max4.subtype
  apply hm
  rw [representative_factorization, hi]
  change localValue (localWords (coordinates i).1) * 1 ∈ max4
  rw [mul_one]
  exact localValue_mem _

/-- The first six representatives normalize the intrinsic max4 two-core. -/
public theorem first_six (i : Index) (hi : i.val < 6) : Alternative i := by
  apply Or.inl
  apply core_of_sector_zero
  have h : ∀ j : Fin 6, (coordinates ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩).2 = 0 := by decide +kernel
  exact h ⟨i.val, hi⟩

end Rudvalis.SylowOvergroups.TwoCore.Generation.RepresentativeChecks
