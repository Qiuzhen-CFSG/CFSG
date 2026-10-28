module
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.CoreMaximality.Setup
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.WordCoverage
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks.Action

/-!
# Finite certificate interfaces for the Held order-three extensions

For rows 1 and 3, Q is the literal core candidate and P is the intersection of
its ambient centralizer with the fixed representative T. The checked 1024-word
cover bounds |T|. Given an element u of P whose conjugate under a normalizer of
Q leaves T, we have Q < P. A representative element not centralizing the row
also gives P < T. Since |Q| = 256, the two strict subgroup indices force |P| = 512.

The other interfaces turn generator conjugation and point-image displacement
checks into statements about the literal ambient subgroups. No full-centralizer
bound, Sylow assertion, or p-core identification is used.

Source: original ATLAS HeG1-p2058B0 and max5 words; GLS3 Table 5.3p and
quasithin condition E. `RowOne` and `RowThree` discharge every finite premise.
-/

@[expose] public section
namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates.ExtensionCertificates
open Subgroup LocalPairs.SylowGeometry.Calculations SpanCertificates
open IntrinsicEnumeration IntrinsicEnumeration.ExtensionChecks

def x : He := (MulAut.conj (conjugator 0)) max5First
def y : He := (MulAut.conj (conjugator 0)) max5Second

theorem centralizes_of_generators (j : Fin 22) (t : He)
    (h : ∀ a : Fin (generatorWords j).length,
      wordGenerator (generatorWords j) a * t = t * wordGenerator (generatorWords j) a) :
    t ∈ centralizer (ambient j : Set He) := by
  have hc : ambient j ≤ centralizer ({t} : Set He) := by
    rw [ambient_eq_word_closure, closure_le]
    rintro _ ⟨a, rfl⟩
    exact mem_centralizer_singleton_iff.mpr (h a)
  intro a ha
  exact mem_centralizer_singleton_iff.mp (hc ha)

theorem normalizes_of_generators (j : Fin 22) (t : He)
    (h : ∀ a : Fin (spanWords j).length,
      t * wordGenerator (spanWords j) a * t⁻¹ ∈ coreCandidate j) :
    t ∈ normalizer (coreCandidate j : Set He) := by
  rw [mem_normalizer_iff_map_conj_eq]
  apply eq_of_le_of_card_ge
  · rw [coreCandidate_eq_word_closure, MonoidHom.map_closure, closure_le]
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    rw [← coreCandidate_eq_word_closure]
    exact h a
  · exact le_of_eq (card_map_of_injective (MulAut.conj t).injective).symm

theorem product_mem_core (j : Fin 22) (w : List (Fin (spanWords j).length)) :
    eval (wordGenerator (spanWords j)) w ∈ coreCandidate j := by
  rw [coreCandidate_eq_word_closure]
  apply Subgroup.list_prod_mem
  rintro _ hx
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
  exact subset_closure ⟨a, rfl⟩

theorem not_mem_representative_of_image (z : He) (a v : Fin 2058)
    (hz : representation z a = v)
    (h : ∀ i : Fin 1024, normalFormAction i a ≠ v) : z ∉ representative := by
  intro hm
  obtain ⟨i, hi⟩ := normalForm_surjective ⟨z, hm⟩
  apply h i
  rw [normalFormAction_eq, hi, hz]

private theorem twice_card_le_of_lt {G : Type*} [Group G] [Finite G]
    {Q P : Subgroup G} (h : Q < P) : 2 * Nat.card Q ≤ Nat.card P := by
  have hi : 2 ≤ (Q.subgroupOf P).index := by
    apply (Q.subgroupOf P).one_lt_index_of_ne_top
    intro he
    have hpq : P ≤ Q := subgroupOf_eq_top.mp he
    exact h.not_ge hpq
  have hc := (Q.subgroupOf P).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe h.le).toEquiv] at hc
  calc 2 * Nat.card Q ≤ (Q.subgroupOf P).index * Nat.card Q :=
        Nat.mul_le_mul_right _ hi
       _ = Nat.card P := hc

/-- The 1024-word cover and the two strict inclusions force the middle order. -/
theorem card_of_displacement (j : Fin 22) (hj : j = 1 ∨ j = 3)
    (t u v : He) (ht : t ∈ normalizer (coreCandidate j : Set He))
    (hu : u ∈ centralizerTwoCandidate j) (htu : t * u * t⁻¹ ∉ representative)
    (hv : v ∈ representative) (hvC : v ∉ centralizer (ambient j : Set He)) :
    Nat.card (centralizerTwoCandidate j) = 512 := by
  have hQT := coreCandidate_le_representative j
  have hQP := coreCandidate_le_centralizerTwoCandidate j (hj.imp_right Or.inl)
  have huQ : u ∉ coreCandidate j := by
    intro h
    exact htu (hQT ((mem_normalizer_iff.mp ht u).mp h))
  have hQPlt : coreCandidate j < centralizerTwoCandidate j := by
    apply lt_of_le_of_ne hQP
    intro he
    exact huQ (he ▸ hu)
  have hPTlt : centralizerTwoCandidate j < representative := by
    apply lt_of_le_of_ne inf_le_left
    intro he
    exact hvC ((he.symm ▸ hv).2)
  have hl := twice_card_le_of_lt hQPlt
  have hupp := twice_card_le_of_lt hPTlt
  have hT : Nat.card representative ≤ 1024 := by
    simpa only [Nat.card_fin] using Nat.card_le_card_of_surjective normalForm normalForm_surjective
  rw [coreCandidate_card j hj] at hl
  omega

theorem not_centralizes_of_generator (j : Fin 22) (z : He)
    (a : Fin (generatorWords j).length)
    (h : (wordPerm (generatorWords j) a * representation z) 0 ≠
      (representation z * wordPerm (generatorWords j) a) 0) :
    z ∉ centralizer (ambient j : Set He) := by
  intro hz
  have hg : wordGenerator (generatorWords j) a ∈ ambient j := by
    rw [ambient_eq_word_closure]
    exact subset_closure ⟨a, rfl⟩
  have he := congrArg (fun u : He => representation u 0) (hz _ hg)
  apply h
  simpa only [map_mul, wordPerm_eq] using he

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates.ExtensionCertificates
