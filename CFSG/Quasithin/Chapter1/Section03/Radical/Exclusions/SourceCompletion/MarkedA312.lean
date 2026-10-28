module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.SourceCompletion.StarModels
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.MarkedA312
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.SourceNormality
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Application.Source.Complete

/-!
# Canonical radicals with only the marked A.3.12 premise remaining

The actual Sylow radical, irreducible action, normalizer equality and
characteristic-normalizer theorem construct the original Configuration.
Its source-complete model exclusion then proves starred membership.
The sole earlier classification premise is the actual marked A.3.12
embedding in each escaping characteristic normalizer; it remains unproved.
Source: Aschbacher–Smith, 1.3.8, printed pp.512–514.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
open Section02 RadicalNormalizers RadicalActions
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original canonical radical is starred, conditional on its actual marked embeddings. -/
theorem XiP_mem_XiStar_of_marked_A312
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G T)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hMarked : MarkedA312Input p L T) :
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
      characteristicNormalizerClosure_le_of_marked_A312 hG hA36 hA38
        ThompsonSource.source_theoremB216 T h127 hL hn ho hd hMarked }
  exact Configuration.mem_XiStar_knownSimple hG T hc

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
