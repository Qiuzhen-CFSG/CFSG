module
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.RadicalIdentity
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.Source
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
/-!
# The maximal normalizer of an original nonquasisimple faithful component

For a maximal local component, the genuine A/C uniqueness theorem and the
canonical radical identify its normalizer. Every smaller faithful component
with nonquasisimple two-core quotient has the same radical as a maximal
containing component. Thus its radical normalizer is a maximal two-local
containing the original LT. The whole-orbit bound retains its earlier source
producer; neither maximality nor a model list is assumed.

Source: Aschbacher--Smith, Lemma 13.1.4(2), printed p.867.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01
open Chapter1 Chapter1.XiEmbedding Chapter12.Section02
open Chapter1.Section02 Chapter1.Section02.Adequate
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
    (h : Hypothesis1311 T)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ C : Subgroup D, C.IsCComponent → A36Conclusion C)
    (hA38 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ C : Subgroup D, C.IsCComponent → C.Normal ∨ IsQuasisimple C)
    (hA : ∀ (D : Type u) [Group D] [Finite D],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple D)
    (hC : ∀ (D : Type u) [Group D] [Finite D],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple D)
include h hA36 hA38 hA hC

theorem Hypothesis1311.maximal_radical_normalizer_data
    {K : Subgroup G} (hK : K ∈ LStar G T) (hn : ¬ IsQuasisimple (XiQuotient K))
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient K))) :
    normalizer (K : Set G) = normalizer (XiP p K : Set G) ∧
      IsMaximalTwoLocal (normalizer (K : Set G)) ∧
      K ⊔ (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      ∀ M : Subgroup G, IsMaximalTwoLocal M → K ⊔ (T : Subgroup G) ≤ M →
        M = normalizer (K : Set G) := by
  apply XiP_normalizer_structure_of_source hA36 hA38
    (fun M hM N hne hNM hsub => lemma_1_1_3_1 hM hne hNM hsub)
    (lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T))
    (fun L hL => ?_) hK
    (uniqueness_local_quotient_sqtk h.simpleQTKE hK.1.2.2) hn ho hd
  have hu := nonsolvable_uniqueness_of_theoremsAC hA hC h.simpleQTKE T hL
  exact ⟨hu.normalizer_maximal, hu.normalizer_unique⟩

variable (hA410 : A410EarlierResult G)
    (hbound : ∀ (K W : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T K →
      ∀ D : ChosenModule T K W, cubicRatio D.orbitRepresentation ≤ 2)
include hA410 hbound

theorem Hypothesis1311.radical_normalizer_maximal_of_orbit_bound
    {L₀ : Subgroup G} (hL : L₀ ∈ nonquasisimpleFaithful T)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L₀))) :
    IsMaximalTwoLocal (normalizer (XiP p L₀ : Set G)) ∧
      L₀ ⊔ (T : Subgroup G) ≤ normalizer (XiP p L₀ : Set G) := by
  have hl := ((mem_faithfulLocalComponents_iff T L₀).mp hL.1).1
  obtain ⟨K, hK, hLK⟩ := exists_mem_LStar_ge hl
  have hKL := h.nonquasisimpleFaithful_overgroup_of_orbit_bound hA36 hA38 hA410 hbound hL hK.1 hLK
  have hn := h.radical_normal_in_overgroup_of_orbit_bound hA36 hA38 hA410 hbound hL hK.1 hLK ho hd
  have hshape := (XiP_oddQuotient_of_A36 hA36 hl
    (uniqueness_local_quotient_sqtk h.simpleQTKE hl.2.2) hL.2 ho hd).2
  have hdK := prime_dvd_fitting_of_normal_radical ((XiP_le p L₀).trans hLK) hn hshape
  have heq := h.radical_eq_of_overgroup_of_orbit_bound hA36 hA38 hA410 hbound hL hK.1 hLK ho hd
  obtain ⟨he, hmax, hKT, _⟩ := h.maximal_radical_normalizer_data hA36 hA38 hA hC hK hKL.2 ho hdK
  rw [← heq] at he
  exact ⟨he ▸ hmax, (sup_le_sup_right hLK (T : Subgroup G)).trans (he ▸ hKT)⟩
end CFSG.Quasithin.Chapter13.Section01
