module

public import CFSG.Quasithin.ChapterG.Section02.Intersection
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.SymmetricThreeConjugateKernel

/-!
# The binary almost-special core

Once the source quotient and generation calculations identify I/O₂(I)
with S₃ and place the original conjugator in I, the existing central
extension theorem gives O₂(I)=W Wᵍ. All subgroup restrictions and quotient
maps below are the literal ones in Setup. Quotient recognition and the
index-two Sylow image remain explicit earlier-source premises.

Source: Aschbacher–Smith, G.2.3(3), printed pp.333–334. The restriction
calculation follows the marked parabolic BinaryCore implementation.
-/

open Subgroup

namespace CFSG.Quasithin.ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem binary_map_intrinsic_conjugate (I : Subgroup G) (A : Subgroup I) (g : I) :
    (A.conjBy g⁻¹).map I.subtype = conjugate (A.map I.subtype) (g : G) := by
  unfold Subgroup.conjBy conjugate
  rw [map_map, map_map]
  congr 1

/-- Clause (3) from the preceding quotient and generation calculations;
the original source conjugator is retained. -/
public theorem binary_core_factorization (D : Setup G) (g : G)
    (hg : g ∈ D.I g)
    (e : ((D.I g) ⧸ pCore 2 (D.I g)) ≃* Equiv.Perm (Fin 3))
    (hnorm : D.S g ≤ normalizer (D.U : Set G))
    (hindex : (D.W g).relIndex D.U = 2) :
    D.S g = D.W g ⊔ conjugate (D.W g) g := by
  let I := D.I g
  let U := D.U.subgroupOf I
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
  have hUI : D.U ≤ I := le_sup_left
  have hUmap : U.map I.subtype = D.U := map_subgroupOf_eq_of_le hUI
  have hW : D.U ⊓ I.pCoreIn 2 = D.W g := rfl
  have hnorm' : f.ker ≤ normalizer (U : Set I) := by
    rw [hk, ← subgroupOf_normalizer_eq hUI]
    intro i hi
    exact hnorm (mem_map_of_mem I.subtype hi)
  have hUf : Nat.card (U.map f) = 2 := by
    rw [← relIndex_ker U f, hk]
    have he := relIndex_map_map_of_injective (pCore 2 I) U I.subtype_injective
    rw [hUmap] at he
    change (I.pCoreIn 2).relIndex D.U = (pCore 2 I).relIndex U at he
    rw [← he, ← inf_relIndex_left, hW]
    exact hindex
  let gi : I := ⟨g, hg⟩
  have hgen' : U ⊔ U.conjBy gi⁻¹ = ⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup, binary_map_intrinsic_conjugate, hUmap,
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  have hWmap : (U ⊓ f.ker).map I.subtype = D.W g := by
    rw [map_inf _ _ _ I.subtype_injective, hUmap, hk]
    exact hW
  have hh := symmetric_three_kernel_eq_conjugate_intersections f hf
    (hk ▸ (show IsPGroup 2 (pCore 2 I) from pCore_isPGroup)) U hnorm' hUf gi⁻¹ hgen'
  have hm := congrArg (fun A : Subgroup I => A.map I.subtype) hh
  rw [Subgroup.map_sup, binary_map_intrinsic_conjugate, hWmap, hk] at hm
  exact hm


omit [Finite G] in
/-- The two-core is invariant under every element of the generated group. -/
public theorem binary_core_normalized (D : Setup G) (g : G) :
    D.I g ≤ normalizer (D.S g : Set G) :=
  (D.I g).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (D.I g) (pCore 2 (D.I g)))

omit [Finite G] in
/-- The two marked core intersections have the original U-intersection. -/
public theorem binary_marked_intersection (D : Setup G) (g : G)
    (hg : g ∈ D.I g) (hES : D.S₂ g ≤ D.S g) :
    D.S₂ g = D.W g ⊓ conjugate (D.W g) g := by
  have hSg : conjugate (D.S g) g = D.S g :=
    mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (D.S g : Set G)).inv_mem (D.binary_core_normalized g hg))
  change D.U ⊓ conjugate D.U g =
    (D.U ⊓ D.S g) ⊓ conjugate (D.U ⊓ D.S g) g
  have hc : conjugate (D.U ⊓ D.S g) g = conjugate D.U g ⊓ D.S g := by
    unfold conjugate
    rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective]
    exact congrArg (conjugate D.U g ⊓ ·) hSg
  rw [hc]
  exact le_antisymm (fun x hx => ⟨⟨hx.1, hES hx⟩, ⟨hx.2, hES hx⟩⟩)
    (fun _ hx => ⟨hx.1.1, hx.2.1⟩)

end CFSG.Quasithin.ChapterG.Section02.Setup
