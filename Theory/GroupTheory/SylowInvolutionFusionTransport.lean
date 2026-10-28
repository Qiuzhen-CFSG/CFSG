module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.PGroup
/-!
# Transporting involution fusion from a Sylow subgroup

Two ambient homomorphisms have the same fusion on involutions whenever
they have the same fusion on a chosen Sylow two-subgroup. Sylow conjugacy
moves each pair into that subgroup and retains both conjugation images.
Faithful maps also compare an involution with an arbitrary element.
-/

open Subgroup
public noncomputable section
namespace Sylow
variable {K G H : Type*} [Group K] [Finite K] [Group G] [Group H]
theorem involution_fusion_transport (P : Sylow 2 K) (f : K →* G) (g : K →* H)
    (hP : ∀ a b : K, a ∈ P → b ∈ P → a ^ 2 = 1 → b ^ 2 = 1 →
      (IsConj (f a) (f b) ↔ IsConj (g a) (g b)))
    (a b : K) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    IsConj (f a) (f b) ↔ IsConj (g a) (g b) := by
  have hplace (x : K) (hx : x ^ 2 = 1) : ∃ k : K, k * x * k⁻¹ ∈ (P : Subgroup K) := by
    have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hx)
    obtain ⟨S,hS⟩ := hp.exists_le_sylow
    obtain ⟨k,hk⟩ := MulAction.exists_smul_eq K S P
    refine ⟨k,?_⟩
    rw [← hk]
    exact ⟨x,hS (mem_zpowers x),rfl⟩
  obtain ⟨k,hk⟩ := hplace a ha
  obtain ⟨l,hl⟩ := hplace b hb
  have ha' : (k*a*k⁻¹)^2=1 := by
    simpa only [map_pow,map_one,MulAut.conj_apply] using congrArg (MulAut.conj k) ha
  have hb' : (l*b*l⁻¹)^2=1 := by
    simpa only [map_pow,map_one,MulAut.conj_apply] using congrArg (MulAut.conj l) hb
  have hfa := f.map_isConj (isConj_iff.mpr ⟨k,rfl⟩ : IsConj a (k*a*k⁻¹))
  have hfb := f.map_isConj (isConj_iff.mpr ⟨l,rfl⟩ : IsConj b (l*b*l⁻¹))
  have hga := g.map_isConj (isConj_iff.mpr ⟨k,rfl⟩ : IsConj a (k*a*k⁻¹))
  have hgb := g.map_isConj (isConj_iff.mpr ⟨l,rfl⟩ : IsConj b (l*b*l⁻¹))
  constructor
  · intro h
    exact hga.trans (((hP _ _ hk hl ha' hb').mp (hfa.symm.trans (h.trans hfb))).trans hgb.symm)
  · intro h
    exact hfa.trans (((hP _ _ hk hl ha' hb').mpr (hga.symm.trans (h.trans hgb))).trans hfb.symm)

/-- Once both embeddings are faithful, fusion of an involution with an
arbitrary element is likewise determined inside the original Sylow. -/
theorem involution_class_transport (P : Sylow 2 K) (f : K →* G) (g : K →* H)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hP : ∀ a b : K, a ∈ P → b ∈ P → a ^ 2 = 1 → b ^ 2 = 1 →
      (IsConj (f a) (f b) ↔ IsConj (g a) (g b)))
    (a b : K) (ha : a ^ 2 = 1) :
    IsConj (f a) (f b) ↔ IsConj (g a) (g b) := by
  by_cases hb : b ^ 2 = 1
  · exact P.involution_fusion_transport f g hP a b ha hb
  · constructor
    · intro hh
      exfalso
      apply hb
      apply hf
      rw [map_pow,map_one]
      have hs := hh.pow 2
      rw [← map_pow,ha,map_one] at hs
      exact isConj_one_right.mp hs
    · intro hh
      exfalso
      apply hb
      apply hg
      rw [map_pow,map_one]
      have hs := hh.pow 2
      rw [← map_pow,ha,map_one] at hs
      exact isConj_one_right.mp hs

end Sylow
