module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section213Alpha.Geometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.LocalSylow

/-!
# Local subgroups for Held's Section 2.13 overgroup

Inside the marked A10 centralizer H, the intersection B of the displayed
Sylow subgroup with C_H(xi) has order 32 and center <pi,mu,xi>. Its squares
are 1 and pi*mu, and both occur. Thus normalizers of B will normalize the
eight-group and centralize pi*mu. The order-64 group C_H(mu) also normalizes
the eight-group and equals C_H(pi*mu). The calculations use the established
384 permutation normal forms, with all finite checks performed in the kernel.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Section 2.13, p.231.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
open Coordinates
local instance : DecidableEq Code := inferInstance

@[expose] public def overgroupModelB : Subgroup H :=
  centralizer ({xi} : Set H) ⊓ Fusion.modelD

public theorem overgroupModelB_word (a : Code) :
    word a ∈ overgroupModelB ↔ word a * xi = xi * word a ∧ a.2.2.2.1 = 0 := by
  simp only [overgroupModelB, mem_inf, mem_centralizer_singleton_iff,
    Fusion.word_mem_modelD]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
public theorem overgroupModelB_card : Nat.card overgroupModelB = 32 := by
  rw [← Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective word word_bijective)
    (fun a => (overgroupModelB_word a).symm)), Nat.card_eq_fintype_card]
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
public theorem overgroupModelB_centralizes (d : Bit) :
    overgroupModelB ≤ centralizer ({normalizedXi d} : Set H) := by
  intro x hx
  obtain ⟨a, rfl⟩ := word_bijective.surjective x
  have ha := (overgroupModelB_word a).mp hx
  apply mem_centralizer_singleton_iff.mpr
  have hc : ∀ d a, (word a * xi = xi * word a ∧ a.2.2.2.1 = 0) →
      word a * normalizedXi d = normalizedXi d * word a := by decide +kernel
  exact hc d a ha

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
public theorem overgroupModelB_square (x : H) (hx : x ∈ overgroupModelB) :
    x ^ 2 = 1 ∨ x ^ 2 = corePi := by
  obtain ⟨a, rfl⟩ := word_bijective.surjective x
  have ha := (overgroupModelB_word a).mp hx
  have hc : ∀ a, (word a * xi = xi * word a ∧ a.2.2.2.1 = 0) →
      word a ^ 2 = 1 ∨ word a ^ 2 = corePi := by decide +kernel
  exact hc a ha

public theorem overgroupModelB_square_witness :
    ∃ x ∈ overgroupModelB, x ^ 2 = corePi := by
  refine ⟨mup * (tau * lam), ?_, by decide +kernel⟩
  apply (overgroupModelB_word ((0,0,1,0),(1,0,0,1))).mpr
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
public theorem overgroupModelB_center (x : H) :
    x ∈ overgroupModelB ⊓ centralizer (overgroupModelB : Set H) ↔
      ∃ i : WordCode, section213Word 0 i = x := by
  constructor
  · rintro ⟨hx, hc⟩
    obtain ⟨a, rfl⟩ := word_bijective.surjective x
    have ha := (overgroupModelB_word a).mp hx
    have hm : mup ∈ overgroupModelB :=
      (overgroupModelB_word ((0,0,1,0),(0,0,0,0))).mpr (by decide +kernel)
    have ht : tau * lam ∈ overgroupModelB :=
      (overgroupModelB_word ((0,0,0,0),(1,0,0,1))).mpr (by decide +kernel)
    have hc' : ∀ a : Code, (word a * xi = xi * word a ∧ a.2.2.2.1 = 0) →
        (mup * word a = word a * mup ∧ (tau * lam) * word a = word a * (tau * lam)) →
        section213Word 0 (a.1.1, a.1.2.1, a.1.2.2.2) = word a := by
      set_option synthInstance.maxSize 256 in
        decide +kernel
    exact ⟨_, hc' a ha ⟨mem_centralizer_iff.mp hc _ hm, mem_centralizer_iff.mp hc _ ht⟩⟩
  · rintro ⟨i, rfl⟩
    constructor
    · apply (overgroupModelB_word ((i.1,i.2.1,0,i.2.2),(0,0,0,0))).mpr
      have hh : ∀ i : WordCode, word ((i.1,i.2.1,0,i.2.2),(0,0,0,0)) * xi =
          xi * word ((i.1,i.2.1,0,i.2.2),(0,0,0,0)) ∧ (0 : Fin 3) = 0 := by decide +kernel
      exact hh i
    · apply mem_centralizer_iff.mpr
      intro y hy
      obtain ⟨a, rfl⟩ := word_bijective.surjective y
      have hh : ∀ i a, (word a * xi = xi * word a ∧ a.2.2.2.1 = 0) →
          word a * section213Word 0 i = section213Word 0 i * word a := by decide +kernel
      exact hh i a ((overgroupModelB_word a).mp hy)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
public theorem overgroupModelP_centralizer :
    centralizer ({corePi} : Set H) = centralizer ({Coordinates.mu} : Set H) := by
  ext x
  obtain ⟨a, rfl⟩ := word_bijective.surjective x
  simp only [mem_centralizer_singleton_iff]
  have hc : ∀ a : Code, word a * corePi = corePi * word a ↔ word a * Coordinates.mu = Coordinates.mu * word a := by decide +kernel
  exact hc a

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
public theorem overgroupModelP_conjugates (x : H)
    (hx : x ∈ centralizer ({Coordinates.mu} : Set H)) (i : WordCode) :
    ∃ j : WordCode, section213Word 0 j = x * section213Word 0 i * x⁻¹ := by
  obtain ⟨a, rfl⟩ := word_bijective.surjective x
  have hx' := mem_centralizer_singleton_iff.mp hx
  have hc : ∀ a : Code, word a * Coordinates.mu = Coordinates.mu * word a → ∀ i : WordCode, ∃ j : WordCode,
      section213Word 0 j = word a * section213Word 0 i * (word a)⁻¹ := by decide +kernel
  exact hc a hx' i


public theorem overgroupModelXi_card (d : Bit) :
    Nat.card (centralizer ({normalizedXi d} : Set H)) = 96 := by
  fin_cases d
  · simpa [normalizedXi] using involution_centralizer_cards.2.2.2.2.2.1
  · simpa [normalizedXi] using involution_centralizer_cards.2.2.2.2.2.2.1

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
