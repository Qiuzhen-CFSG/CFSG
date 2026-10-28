module
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.SourceCompletion
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.SourceNormality
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.Source
/-!
# The single odd-prime branch of the original radical theorem

For a maximal local component with nonquasisimple two-core quotient, the
proved A.3.6 and normal-or-quasisimple A.3.8 give the actual Xi radical,
its irreducible complement action, and its noncyclic Sylow automizer.
When the odd Fitting support is a single prime, the existing coprime omega
normalizer argument supplies characteristic-normalizer control. Genuine
A/C uniqueness supplies the maximal normalizer and its equality with the
radical normalizer. These construct every field of Configuration internally.
The full C.2.7 input then gives starred membership by the completed model
exclusion. Higher homocyclic exponents remain allowed.

Only the genuine universal C.2.7 theorem remains explicit in this branch.
The multiple-prime branch and the full1.3.8 theorem are not asserted.
Source: Aschbacher--Smith, proof of1.3.8, printed pp.512--514.
-/
public section

namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
open Subgroup Theory.GroupTheory Section02 RadicalNormalizers RadicalActions
universe u
variable {G : Type u} [Group G] [Finite G]

theorem XiP_mem_XiStar_of_singlePrime_C27
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (source : FullSieve.SourceInterface.Source KnownSimple.IsKnownSimple G)
    {L : Subgroup G} (hL : L ∈ LStar G T)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hs : ∀ q : ℕ, q.Prime → Odd q →
      q ∣ Nat.card (fittingSubgroup (XiQuotient L)) → q = p) :
    XiP p L ∈ XiStar G (T : Subgroup G) := by
  classical
  let hA := fun (D : Type u) [Group D] [Finite D] =>
    ChapterA.Section02.theoremA_knownSimple (G := D)
  let hC := fun (D : Type u) [Group D] [Finite D] =>
    ChapterA.Section02.theoremC_knownSimple (G := D)
  let hA36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC hA hC
  have hA38 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → B.Normal ∨ IsQuasisimple B :=
    fun _ _ _ hD hO _ hB => ChapterA.Section03.NoncentralNormality.normal_or_quasisimple hD hO hB
  have hQall : ∀ K ∈ Chapter1.L G (T : Subgroup G),
      IsSQTK KnownSimple.IsKnownSimple ((K ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)) :=
    fun _ hK => uniqueness_local_quotient_sqtk hG hK.2.2
  have h127 : ∀ K ∈ LStar G (T : Subgroup G),
      IsMaximalTwoLocal (normalizer (componentOrbit K (T : Subgroup G) : Set G)) ∧
      ∀ M : Subgroup G, IsMaximalTwoLocal M → K ⊔ (T : Subgroup G) ≤ M →
        M = normalizer (componentOrbit K (T : Subgroup G) : Set G) := by
    intro K hK
    have h := nonsolvable_uniqueness_of_theoremsAC hA hC hG T hK
    exact ⟨h.normalizer_maximal,h.normalizer_unique⟩
  have h114 := lemma_1_1_4_6 T (hG.evenCharacteristic T)
  have h113 := fun M (hM : M ∈ He G) N (hN : N ≠ ⊥) (hNM : N ≤ M)
    (hnorm : (N.subgroupOf M).IsSubnormal) => lemma_1_1_3_1 hM hN hNM hnorm
  have hQ := hQall L hL.1
  obtain ⟨hNX,hmax,_,_⟩ := XiP_normalizer_structure_of_source
    hA36 hA38 h113 h114 h127 hL hQ hn ho hd
  obtain ⟨hp3,hodd⟩ := XiP_oddQuotient_of_A36 hA36 hL.1 hQ hn ho hd
  have hXi : XiP p L ∈ Xi G (T : Subgroup G) :=
    lemma_1_3_3 hA36 hA38 hQall ⟨L,hL.1,hn,p,Fact.out,ho,hd,rfl⟩
  let P : Sylow p (XiP p L) := Classical.arbitrary _
  let P₀ := (P : Subgroup (XiP p L)).map (XiP p L).subtype
  have hc : Configuration p T (XiP p L) P₀ L (normalizer (L : Set G)) := {
    prime := Fact.out
    odd := ho
    large := hp3
    xi := hXi
    radical := rfl
    maximal_local := hL
    quotient := hodd
    sylow := ⟨P,rfl⟩
    automizer_not_cyclic := XiP_automizer_not_isCyclic_of_A36 hA36 hL.1 hQ hn ho hd P
    irreducible := XiP_normalizer_irreducible_of_A36 hA36 hL.1 hQ hn ho hd P
    normalizer_local := rfl
    normalizer_radical := hNX
    maximal_twoLocal := hmax
    characteristic_control :=
      (radical_singlePrime_normalizers_of_source hA36 hA38 h127 hL hQ hn ho hd hs).2 }
  exact Configuration.mem_XiStar_of_C27 hG T source hc
end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
