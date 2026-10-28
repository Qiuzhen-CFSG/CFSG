module

public import Theory.GroupTheory.ComponentLocalOrbitCore

/-!
# Abelian local component orbits modulo the overgroup two-core

Let B ≤ L with L a component, and suppose the stabilizer of L in A
normalizes B. If [B,B] ≤ O₂(B), the A-conjugates of B generate a subgroup
with derived subgroup in O₂(⟨B,A⟩). Conjugate factors either coincide or
commute. The orbit of O₂(B) is a normal two-subgroup of the full overgroup,
and the images of all factors commute after quotienting by its two-core.

Source: the component and Borel calculation in Aschbacher--Smith,
E.2.2, pp.215--216, and 4.4.13, pp.623--624; component calculus A.3.3.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

private theorem commutator_iSup_le_normal {ι : Type*} (C : ι → Subgroup G)
    (N : Subgroup G) [N.Normal] (hc : ∀ i j, ⁅C i, C j⁆ ≤ N) :
    ⁅⨆ i, C i, ⨆ i, C i⁆ ≤ N := by
  let q := QuotientGroup.mk' N
  have hz (i j) : ⁅(C i).map q, (C j).map q⁆ = ⊥ := by
    rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hc i j
  have hall : ⁅⨆ i, (C i).map q, ⨆ i, (C i).map q⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply iSup_le
    intro i
    apply le_centralizer_iff.mp
    exact iSup_le fun j => commutator_eq_bot_iff_le_centralizer.mp (hz j i)
  have hmap : ⁅⨆ i, C i, ⨆ i, C i⁆.map q = ⊥ := by
    rwa [map_commutator, Subgroup.map_iSup]
  simpa only [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk', q] using hmap

variable [Finite G]

/-- Conjugate local factors give an abelian orbit modulo the full overgroup two-core. -/
theorem IsComponent.local_orbit_commutator_le_pCoreIn {L B A : Subgroup G}
    (hL : IsComponent G L) (hBL : B ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (B : Set G))
    (hd : ⁅B, B⁆ ≤ B.pCoreIn 2) :
    ⁅componentOrbit B A, componentOrbit B A⁆ ≤ (B ⊔ A).pCoreIn 2 := by
  let P := B ⊔ A
  let C (a : A) := B.map (MulAut.conj (a : G)).toMonoidHom
  have hCP (a : A) : C a ≤ P := (le_iSup (fun a : A => C a) a).trans
    (componentOrbit_le_sup B A)
  have hpair (a b : A) : ⁅C a, C b⁆ ≤ P.pCoreIn 2 := by
    rcases hL.local_conjugates_eq_or_commute hBL hinv b a with he | hz
    · change ⁅B.map (MulAut.conj (a : G)).toMonoidHom,
        B.map (MulAut.conj (b : G)).toMonoidHom⁆ ≤ P.pCoreIn 2
      rw [he, ← map_commutator]
      exact (map_mono hd).trans
        ((le_iSup (fun s : A => (B.pCoreIn 2).map (MulAut.conj (s : G)).toMonoidHom) b).trans
          (hL.local_core_orbit_le hBL hinv))
    · exact hz.le.trans bot_le
  have hint (a b : A) : ⁅(C a).subgroupOf P, (C b).subgroupOf P⁆ ≤ pCore 2 P := by
    apply (map_le_map_iff_of_injective P.subtype_injective).mp
    rw [map_commutator, map_subgroupOf_eq_of_le (hCP a), map_subgroupOf_eq_of_le (hCP b)]
    exact hpair a b
  have hh := map_mono (f := P.subtype)
    (commutator_iSup_le_normal (fun a => (C a).subgroupOf P) (pCore 2 P) hint)
  simpa only [map_commutator, Subgroup.map_iSup, map_subgroupOf_eq_of_le (hCP _),
    componentOrbit, C, P, pCoreIn] using hh

end Theory.GroupTheory
