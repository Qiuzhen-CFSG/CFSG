module

public import CFSG.Quasithin.Chapter13.Section01.RadicalConjugateRigidity.Conjugates
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.SourceNormality
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.Source
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete

/-!
# Original 13.1.11 for the canonical radical of a maximal local component

The completed A/C structure and Chapter 1 uniqueness theorem supply the
actual Ξ_p(L), its odd quotient and N_G(Ξ_p(L))=N_G(L). Quasithinness gives
the needed rank bound at that maximal two-local. The preceding comparison
then proves the original unique-conjugate conclusion for every intermediate
irreducible actor X₁. No Chapter 3 cubic-ratio theorem is used here.

Source: Aschbacher--Smith 13.1.11, p.872, with 1.3.3 and 1.2.7(3).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.RadicalConjugateRigidity
open Chapter1 Chapter1.Section02 Chapter1.RadicalNormalizers
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The canonical radical structure needed in 13.1.11, with every universal
A/C, normality and maximal-two-local uniqueness input discharged. -/
theorem maximal_radical_structure
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    XiOddQuotient p (XiQuotient (XiP p L)) ∧
      normalizer (XiP p L : Set G) = normalizer (L : Set G) ∧
      IsMaximalTwoLocal (normalizer (L : Set G)) := by
  let hA := fun (D : Type u) [Group D] [Finite D] =>
    ChapterA.Section02.theoremA_knownSimple (G := D)
  let hC := fun (D : Type u) [Group D] [Finite D] =>
    ChapterA.Section02.theoremC_knownSimple (G := D)
  let hA36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC hA hC
  have hA38 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → B.Normal ∨ IsQuasisimple B :=
    fun _ _ _ hD hO _ hB => ChapterA.Section03.NoncentralNormality.normal_or_quasisimple hD hO hB
  have hQ := uniqueness_local_quotient_sqtk hG hL.1.2.2
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
  obtain ⟨hNX,hmax,_,_⟩ := XiP_normalizer_structure_of_source
    hA36 hA38 h113 h114 h127 hL hQ hn ho hd
  exact ⟨(XiP_oddQuotient_of_A36 hA36 hL.1 hQ hn ho hd).2,hNX.symm,hmax⟩

/-- Original 13.1.11 for X=Ξ_p(L): every conjugate containing the original
irreducible X₁ is M itself, and its original conjugator belongs to M. -/
theorem maximal_radical_unique_conjugate
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (X₁ : Subgroup G) (hXX₁ : XiP p L ≤ X₁)
    (hX₁M : X₁ ≤ normalizer (L : Set G))
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient (XiP p L)),
      (∀ s : X₁, ∀ a ∈ A,
        xiFrattiniAction X₁ (XiP p L) (XiP_invariant p hX₁M) s a ∈ A) →
          A = ⊥ ∨ A = ⊤)
    (g : G) (hg : X₁ ≤ (normalizer (L : Set G)).conjBy g) :
    g ∈ normalizer (L : Set G) ∧
      (normalizer (L : Set G)).conjBy g = normalizer (L : Set G) := by
  obtain ⟨hq,hNX,hm⟩ := maximal_radical_structure hG T hL hn ho hd
  exact conjugate_eq_of_irreducible ho (XiP p L) (normalizer (L : Set G)) X₁
    (isQuasithin_iff_twoLocal.mp hG.quasithin _ hm.1) hNX
    (XiP_isPPerfect p L) hq hXX₁ hX₁M hirr g hg

end CFSG.Quasithin.Chapter13.Section01.RadicalConjugateRigidity
