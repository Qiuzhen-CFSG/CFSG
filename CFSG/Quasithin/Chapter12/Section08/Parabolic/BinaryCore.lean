module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Basic
public import Theory.GroupTheory.SymmetricThreeConjugateKernel
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# The binary core factorization in the marked parabolic

The source S₃ quotient, the index-two action of U and normalization by the
two-core imply O₂(I₂)=W W^g. The proof restricts the actual U to I₂, applies
the central-extension argument there, then maps the result back through
the same inclusion. The conjugator must first be chosen inside I₂; the
ambient version below preserves the original marked conjugates.

Source: Aschbacher–Smith, G.2.3(3), printed pp.333–334, specialized in
12.8.9(2), printed pp.852–853. The inputs from 12.8.9(1) and the original
natural action remain with its source owner.
-/

open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem map_intrinsic_conjugate (I : Subgroup G) (A : Subgroup I) (g : I) :
    (A.conjBy g⁻¹).map I.subtype = conjugate (A.map I.subtype) (g : G) := by
  unfold Subgroup.conjBy conjugate
  rw [map_map, map_map]
  congr 1

/-- The actual binary instance of G.2.3(3), with the conjugator inside I₂.
The two-core quotient and action index are earlier 12.8.9(1) inputs. -/
public theorem binary_core_factorization_internal
    (F : InvariantFlag T V n) (L : Subgroup G) (g : G)
    (hg : g ∈ F.I₂ L)
    (hgen : F.U ⊔ conjugate F.U g = F.I₂ L)
    (e : ((F.I₂ L) ⧸ pCore 2 (F.I₂ L)) ≃* Equiv.Perm (Fin 3))
    (hcore : F.I₂ L ⊓ centralizer (F.Vi 2 : Set G) = (F.I₂ L).pCoreIn 2)
    (hnorm : (F.I₂ L).pCoreIn 2 ≤ normalizer (F.U : Set G))
    (hindex : F.W.relIndex F.U = 2) :
    (F.I₂ L).pCoreIn 2 = F.W ⊔ F.X g := by
  let I := F.I₂ L
  let U := F.U.subgroupOf I
  let q := QuotientGroup.mk' (pCore 2 I)
  let f := e.toMonoidHom.comp q
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 I := by
    ext i
    change e (q i) = 1 ↔ i ∈ pCore 2 I
    constructor
    · intro hi
      exact (QuotientGroup.eq_one_iff i).mp (e.injective (hi.trans e.map_one.symm))
    · intro hi
      change e (QuotientGroup.mk i) = 1
      rw [(QuotientGroup.eq_one_iff i).mpr hi, map_one]
  have hUI : F.U ≤ I := le_sup_left.trans hgen.le
  have hUmap : U.map I.subtype = F.U := map_subgroupOf_eq_of_le hUI
  have hW : F.U ⊓ I.pCoreIn 2 = F.W := by
    rw [← hcore, ← inf_assoc, inf_eq_left.mpr hUI]
    rfl
  have hnorm' : f.ker ≤ normalizer (U : Set I) := by
    rw [hk, ← subgroupOf_normalizer_eq hUI]
    intro i hi
    exact hnorm (mem_map_of_mem I.subtype hi)
  have hUf : Nat.card (U.map f) = 2 := by
    rw [← relIndex_ker U f, hk]
    have he := relIndex_map_map_of_injective (pCore 2 I) U I.subtype_injective
    rw [hUmap] at he
    change (I.pCoreIn 2).relIndex F.U = (pCore 2 I).relIndex U at he
    rw [← he, ← inf_relIndex_left, hW]
    exact hindex
  let gi : I := ⟨g, hg⟩
  have hgen' : U ⊔ U.conjBy gi⁻¹ = ⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup, map_intrinsic_conjugate, hUmap,
      ← MonoidHom.range_eq_map, range_subtype]
    exact hgen
  have hWmap : (U ⊓ f.ker).map I.subtype = F.W := by
    rw [map_inf _ _ _ I.subtype_injective, hUmap, hk]
    exact hW
  have hh := symmetric_three_kernel_eq_conjugate_intersections f hf
    (hk ▸ (show IsPGroup 2 (pCore 2 I) from pCore_isPGroup)) U hnorm' hUf gi⁻¹ hgen'
  have hm := congrArg (fun A : Subgroup I => A.map I.subtype) hh
  rw [Subgroup.map_sup, map_intrinsic_conjugate, hWmap, hk] at hm
  exact hm

/-- Preserve the original parabolic conjugator. The factorization through
H and I₂ is supplied by the earlier equality P=O₂(P)I₂, with O₂(P)≤H.
No assumption that the original g belongs to I₂ is made. -/
public theorem binary_core_factorization
    (F : InvariantFlag T V n) (L : Subgroup G) (g : G)
    (hgP : g ∈ F.P L)
    (hfactor : F.P L = (F.P L).pCoreIn 2 ⊔ F.I₂ L)
    (hPH : (F.P L).pCoreIn 2 ≤ F.H)
    (hgen : F.U ⊔ conjugate F.U g = F.I₂ L)
    (e : ((F.I₂ L) ⧸ pCore 2 (F.I₂ L)) ≃* Equiv.Perm (Fin 3))
    (hcore : F.I₂ L ⊓ centralizer (F.Vi 2 : Set G) = (F.I₂ L).pCoreIn 2)
    (hindex : F.W.relIndex F.U = 2) :
    (F.I₂ L).pCoreIn 2 = F.W ⊔ F.X g := by
  have hIP : F.I₂ L ≤ F.P L := le_sup_right.trans hfactor.ge
  have hnormal : normalizer (F.I₂ L : Set G) ≤
      normalizer ((F.I₂ L).pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image (F.I₂ L) (pCore 2 (F.I₂ L))
  have hPnormal : F.P L ≤ normalizer ((F.P L).pCoreIn 2 : Set G) :=
    (F.P L).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (F.P L) (pCore 2 (F.P L)))
  have hS : (F.I₂ L).pCoreIn 2 ≤ (F.P L).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 (F.I₂ L))
      ((pCoreIn_le 2 (F.I₂ L)).trans hIP)
      ((le_normalizer_conjugateSpanBy F.U (F.P L)).trans hnormal)
  have hnorm : (F.I₂ L).pCoreIn 2 ≤ normalizer (F.U : Set G) :=
    (hS.trans hPH).trans (le_normalizer_conjugateSpanBy V F.H)
  have hgprod : g ∈ ((F.P L).pCoreIn 2 : Set G) * (F.I₂ L : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ (hIP.trans hPnormal), ← hfactor]
    exact hgP
  obtain ⟨k, hk, h, hh, rfl⟩ := hgprod
  have hkU : conjugate F.U k = F.U := (conjugate_eq_iff _ _).mpr
    (le_normalizer_conjugateSpanBy V F.H (hPH hk))
  have hconj : conjugate F.U h = conjugate F.U (k * h) := by
    calc
      conjugate F.U h = conjugate (conjugate F.U k) h := by rw [hkU]
      _ = conjugate F.U (k * h) := by
        unfold conjugate
        rw [map_map]
        congr 1
        ext x
        simp [mul_assoc]
  have hgen' : F.U ⊔ conjugate F.U h = F.I₂ L := by rw [hconj]; exact hgen
  have hresult := F.binary_core_factorization_internal L h hh hgen' e hcore hnorm hindex
  have hUI : F.U ≤ F.I₂ L := le_sup_left.trans hgen.le
  have hW : F.U ⊓ (F.I₂ L).pCoreIn 2 = F.W := by
    rw [← hcore, ← inf_assoc, inf_eq_left.mpr hUI]
    rfl
  have hSg : conjugate ((F.I₂ L).pCoreIn 2) (k * h) = (F.I₂ L).pCoreIn 2 :=
    (conjugate_eq_iff _ _).mpr
      (hnormal (le_normalizer_conjugateSpanBy F.U (F.P L) hgP))
  have hSh : conjugate ((F.I₂ L).pCoreIn 2) h = (F.I₂ L).pCoreIn 2 :=
    (conjugate_eq_iff _ _).mpr (hnormal ((F.I₂ L).le_normalizer hh))
  have hX : F.X h = F.X (k * h) := by
    change conjugate F.W h = conjugate F.W (k * h)
    rw [← hW, conjugate_inf, conjugate_inf, hSh, hSg, hconj]
  rwa [hX] at hresult

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
