module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.FourModuleOrbit
/-!
# Stabilizers of paired modules in the actual four-module orbit

The regular Klein four action has identical stabilizers on every point.
The original module and its chosen right conjugate therefore have exactly
the same normalizer inside the source overgroup. The actual conjugation
homomorphism translates the permutation table back to subgroup equality.

Source: Aschbacher–Smith, C.5.6(7), printed pp.158–160.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.FourModuleOrbit
variable {G : Type*} [Group G] {M T U V : Subgroup G} {x : G}

theorem SourceInputs.paired_normalizers (h : SourceInputs M T U V x) :
    M ⊓ normalizer (U : Set G) = M ⊓ normalizer (U.conjBy x⁻¹ : Set G) := by
  obtain ⟨t,ht⟩ := source_setup h.toInputs
  have hf (g : M) (i : Fin 4) : action h.toInputs g i = i ↔
      (g : G) ∈ normalizer (modules U V x i : Set G) := by
    constructor
    · intro he
      have ha := action_apply h.toInputs g i
      rw [he] at ha
      exact mem_normalizer_iff_map_conj_eq.mpr ha.symm
    · intro hn
      apply h.distinct
      rw [action_apply]
      exact mem_normalizer_iff_map_conj_eq.mp hn
  ext g
  constructor
  · rintro ⟨hg,hn⟩
    refine ⟨hg,?_⟩
    apply (hf ⟨g,hg⟩ 2).mp
    have h0 := (hf ⟨g,hg⟩ 0).mpr hn
    rcases ht.table ⟨g,hg⟩ with h0' | h1 | h2 | h3
    · exact h0'.2.2.1
    · rw [h1.1] at h0
      contradiction
    · rw [h2.1] at h0
      contradiction
    · rw [h3.1] at h0
      contradiction
  · rintro ⟨hg,hn⟩
    refine ⟨hg,?_⟩
    apply (hf ⟨g,hg⟩ 0).mp
    have h2 := (hf ⟨g,hg⟩ 2).mpr hn
    rcases ht.table ⟨g,hg⟩ with h0 | h1 | h2' | h3
    · exact h0.1
    · rw [h1.2.2.1] at h2
      contradiction
    · rw [h2'.2.2.1] at h2
      contradiction
    · rw [h3.2.2.1] at h2
      contradiction

theorem SourceInputs.normalizers_eq (h : SourceInputs M T U V x) (i j : Fin 4) :
    M ⊓ normalizer (modules U V x i : Set G) = M ⊓ normalizer (modules U V x j : Set G) := by
  obtain ⟨t,ht⟩ := source_setup h.toInputs
  have hf (g : M) (i : Fin 4) : action h.toInputs g i = i ↔
      (g : G) ∈ normalizer (modules U V x i : Set G) := by
    constructor
    · intro he
      have ha := action_apply h.toInputs g i
      rw [he] at ha
      exact mem_normalizer_iff_map_conj_eq.mpr ha.symm
    · intro hn
      apply h.distinct
      rw [action_apply]
      exact mem_normalizer_iff_map_conj_eq.mp hn
  have hfix (g : M) (i : Fin 4) : action h.toInputs g i = i ↔ action h.toInputs g 0 = 0 := by
    rcases ht.table g with h0 | h1 | h2 | h3
    · fin_cases i <;> simp_all
    · fin_cases i <;> simp_all
    · fin_cases i <;> simp_all
    · fin_cases i <;> simp_all
  ext g
  constructor
  · rintro ⟨hg,hn⟩
    exact ⟨hg,(hf ⟨g,hg⟩ j).mp ((hfix ⟨g,hg⟩ j).mpr ((hfix ⟨g,hg⟩ i).mp ((hf ⟨g,hg⟩ i).mpr hn)))⟩
  · rintro ⟨hg,hn⟩
    exact ⟨hg,(hf ⟨g,hg⟩ i).mp ((hfix ⟨g,hg⟩ i).mpr ((hfix ⟨g,hg⟩ j).mp ((hf ⟨g,hg⟩ j).mpr hn)))⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.FourModuleOrbit
