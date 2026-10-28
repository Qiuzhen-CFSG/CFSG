module
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.SourceCompletion
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.SourceNormality
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.Source
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Assembly
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Application.Source.Complete
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.Source
/-!
# The original maximal radical family for every odd-prime support

The proved multiple-prime characteristic-normalizer argument extends the
single-prime construction to every canonical radical of a nonquasisimple
maximal local component. Complete A/C supply A.3.6 and A.3.8; the proved
solvable Thompson factorization supplies B.2.16. The actual Sylow radical,
its irreducible action and normalizer identify the original configuration.
The full C.2.7 theorem then excludes every possible outside model.

Only the genuine universal A.3.12 embedding theorem and full C.2.7 source
implication remain earlier inputs. No characteristic-normalizer bound or
single-prime support is assumed.
Source: Aschbacher--Smith 1.3.8, pp.512--514.
-/

public section

namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
open Subgroup Theory.GroupTheory Section02 RadicalNormalizers RadicalActions
universe u
variable {G : Type u} [Group G] [Finite G]

theorem XiP_mem_XiStar_of_A312_C27
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hA312 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK KnownSimple.IsKnownSimple A → pCore 2 A = ⊥ →
      ∀ (S : Sylow 2 A) (B : Subgroup A),
        B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (source : FullSieve.SourceInterface.Source KnownSimple.IsKnownSimple G)
    {L : Subgroup G} (hL : L ∈ LStar G T)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
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
  have hA38full : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK KnownSimple.IsKnownSimple A → pCore 2 A = ⊥ →
      ∀ B : Subgroup A, B.IsCComponent →
        B.Normal ∨ (normalizer (B : Set A)).index = 2 ∧ NonnormalCComponentModel B := by
    intro A _ _ hA' hcore B hB
    by_cases hnB : B.Normal
    · exact Or.inl hnB
    · have hq := (hA38 A hA' hcore B hB).resolve_left hnB
      exact Or.inr (ChapterA.SQTKStructure.NonnormalOuterSource.nonnormal_component_index_and_model
        hA hC hA' hcore B ⟨hB.subnormal,hq⟩ hnB)
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
      characteristicNormalizerClosure_le_of_source hG hA36 hA38 hA38full hA312
        ThompsonSource.source_theoremB216 T h127 hL hn ho hd }
  exact Configuration.mem_XiStar_of_C27 hG T source hc

/-- Original 1.3.8 for the entire maximal radical family, retaining only
its genuine A.3.12 and C.2.7 earlier source implications. -/
theorem XiRadStar_subset_XiStar_of_A312_C27
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hA312 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK KnownSimple.IsKnownSimple A → pCore 2 A = ⊥ →
      ∀ (S : Sylow 2 A) (B : Subgroup A),
        B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (source : FullSieve.SourceInterface.Source KnownSimple.IsKnownSimple G) :
    XiRadStar G (T : Subgroup G) ⊆ XiStar G (T : Subgroup G) := by
  let hA36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun (A : Type u) _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun (A : Type u) _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
  have hA38 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK KnownSimple.IsKnownSimple A → pCore 2 A = ⊥ →
      ∀ B : Subgroup A, B.IsCComponent → B.Normal ∨ IsQuasisimple B :=
    fun _ _ _ hA hO _ hB => ChapterA.Section03.NoncentralNormality.normal_or_quasisimple hA hO hB
  have hQ : ∀ K ∈ Chapter1.L G (T : Subgroup G),
      IsSQTK KnownSimple.IsKnownSimple ((K ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)) :=
    fun _ hK => uniqueness_local_quotient_sqtk hG hK.2.2
  intro X hX
  obtain ⟨L,hL,p,hp,ho,_,hn,hd,rfl,_⟩ :=
    XiRadStar_identification_of_A36 hA36 hA38 hQ hX
  let : Fact p.Prime := ⟨hp⟩
  exact XiP_mem_XiStar_of_A312_C27 hG T hA312 source hL hn ho hd

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
