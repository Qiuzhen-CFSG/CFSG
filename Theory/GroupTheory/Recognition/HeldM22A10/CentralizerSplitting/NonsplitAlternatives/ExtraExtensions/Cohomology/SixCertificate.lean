module
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ExtraExtensions.Cohomology.SixData
/-!
# Checked six-orbit cohomology certificate

Each block verifies original cocycle equations and the earlier-row additions
recorded by the elimination data. The pivot check makes these rows triangular.
The cochain checks cancel the free coordinates, up to the displayed scalar
obstruction. Every finite check is reduced by Lean's kernel.

The blocks bound kernel-reduction memory use. They implement the finite
calculation for Huppert--Blackburn III, XII.1.18(b), p.314.
-/

@[expose] public section
namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ExtraExtensions.Cohomology.Six

set_option Elab.async false
private abbrev validAt (k : ℕ) : Prop :=
  (∀ j ∈ (steps.get k).parents, j < k) ∧
    row steps k = rawRow sixOrbitColumns (steps.get k).source ^^^
      xorList ((steps.get k).parents.map (row steps))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma block0 : ∀ k : Fin 128, validAt (k.val + 0) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma block128 : ∀ k : Fin 128, validAt (k.val + 128) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma block256 : ∀ k : Fin 128, validAt (k.val + 256) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma block384 : ∀ k : Fin 128, validAt (k.val + 384) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma block512 : ∀ k : Fin 128, validAt (k.val + 512) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma block640 : ∀ k : Fin 128, validAt (k.val + 640) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma block768 : ∀ k : Fin 128, validAt (k.val + 768) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma block896 : ∀ k : Fin 128, validAt (k.val + 896) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma block1024 : ∀ k : Fin 128, validAt (k.val + 1024) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma block1152 : ∀ k : Fin 128, validAt (k.val + 1152) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma block1280 : ∀ k : Fin 128, validAt (k.val + 1280) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma block1408 : ∀ k : Fin 128, validAt (k.val + 1408) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma block1536 : ∀ k : Fin 128, validAt (k.val + 1536) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma block1664 : ∀ k : Fin 128, validAt (k.val + 1664) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma block1792 : ∀ k : Fin 128, validAt (k.val + 1792) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma block1920 : ∀ k : Fin 128, validAt (k.val + 1920) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma block2048 : ∀ k : Fin 128, validAt (k.val + 2048) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma block2176 : ∀ k : Fin 39, validAt (k.val + 2176) := by
  decide +kernel

lemma valid : Valid steps (rawRow sixOrbitColumns) := by
  change ∀ k : Fin steps.size, validAt k.val
  intro k
  have hk : k.val < 2215 := k.isLt
  by_cases h0 : k.val < 128
  · have he : k.val - 0 + 0 = k.val := by omega
    simpa only [he] using block0 ⟨k.val - 0, by omega⟩
  by_cases h128 : k.val < 256
  · have he : k.val - 128 + 128 = k.val := by omega
    simpa only [he] using block128 ⟨k.val - 128, by omega⟩
  by_cases h256 : k.val < 384
  · have he : k.val - 256 + 256 = k.val := by omega
    simpa only [he] using block256 ⟨k.val - 256, by omega⟩
  by_cases h384 : k.val < 512
  · have he : k.val - 384 + 384 = k.val := by omega
    simpa only [he] using block384 ⟨k.val - 384, by omega⟩
  by_cases h512 : k.val < 640
  · have he : k.val - 512 + 512 = k.val := by omega
    simpa only [he] using block512 ⟨k.val - 512, by omega⟩
  by_cases h640 : k.val < 768
  · have he : k.val - 640 + 640 = k.val := by omega
    simpa only [he] using block640 ⟨k.val - 640, by omega⟩
  by_cases h768 : k.val < 896
  · have he : k.val - 768 + 768 = k.val := by omega
    simpa only [he] using block768 ⟨k.val - 768, by omega⟩
  by_cases h896 : k.val < 1024
  · have he : k.val - 896 + 896 = k.val := by omega
    simpa only [he] using block896 ⟨k.val - 896, by omega⟩
  by_cases h1024 : k.val < 1152
  · have he : k.val - 1024 + 1024 = k.val := by omega
    simpa only [he] using block1024 ⟨k.val - 1024, by omega⟩
  by_cases h1152 : k.val < 1280
  · have he : k.val - 1152 + 1152 = k.val := by omega
    simpa only [he] using block1152 ⟨k.val - 1152, by omega⟩
  by_cases h1280 : k.val < 1408
  · have he : k.val - 1280 + 1280 = k.val := by omega
    simpa only [he] using block1280 ⟨k.val - 1280, by omega⟩
  by_cases h1408 : k.val < 1536
  · have he : k.val - 1408 + 1408 = k.val := by omega
    simpa only [he] using block1408 ⟨k.val - 1408, by omega⟩
  by_cases h1536 : k.val < 1664
  · have he : k.val - 1536 + 1536 = k.val := by omega
    simpa only [he] using block1536 ⟨k.val - 1536, by omega⟩
  by_cases h1664 : k.val < 1792
  · have he : k.val - 1664 + 1664 = k.val := by omega
    simpa only [he] using block1664 ⟨k.val - 1664, by omega⟩
  by_cases h1792 : k.val < 1920
  · have he : k.val - 1792 + 1792 = k.val := by omega
    simpa only [he] using block1792 ⟨k.val - 1792, by omega⟩
  by_cases h1920 : k.val < 2048
  · have he : k.val - 1920 + 1920 = k.val := by omega
    simpa only [he] using block1920 ⟨k.val - 1920, by omega⟩
  by_cases h2048 : k.val < 2176
  · have he : k.val - 2048 + 2048 = k.val := by omega
    simpa only [he] using block2048 ⟨k.val - 2048, by omega⟩
  have he : k.val - 2176 + 2176 = k.val := by omega
  simpa only [he] using block2176 ⟨k.val - 2176, by omega⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma covers : Covers steps pivots := by
  unfold Covers
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cochain_zero : ∀ i, cochain 0 i = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma free : ∀ p, pivots p = 0 → defectMask sixOrbitColumns cochain p = 0 ∨ defectMask sixOrbitColumns cochain p = obstruction := by decide +kernel
end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ExtraExtensions.Cohomology.Six
