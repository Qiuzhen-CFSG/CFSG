module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Conj

/-!
# Weak fusion from a unique elementary subgroup in a centralizer

Let E be elementary abelian of prime exponent in a finite group, with
N_G(E)=C_G(z). Suppose C_G(z) contains an ambient Sylow subgroup for that
prime and E is its unique elementary subgroup of order |E|. Then no
ambient conjugate of z in E differs from z.

If g sends z to t in E, write F=E^g. Abelianness gives E≤C_G(t)=N_G(F),
so E and F generate a p-group. Conjugating this group into the selected
Sylow puts both elementary subgroups inside C_G(z). Their uniqueness
there forces E=F. Thus g normalizes E, hence centralizes z.

This general Sylow transport argument justifies the weak-closure step in
David Parrott, *A characterization of the Tits' simple group* (1972),
Lemma 3, p.675. The consumer must prove uniqueness for its actual E.
-/

open Subgroup
open scoped IsMulCommutative

/-- Uniqueness of the elementary subgroup in a centralizer prevents fusion inside it. -/
public theorem conjugate_eq_of_unique_elementary_centralizer
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (z : G) (E : Subgroup G) [IsElementaryAbelian p E]
    (hN : normalizer (E : Set G) = centralizer ({z} : Set G))
    (S : Sylow p G) (hS : (S : Subgroup G) ≤ centralizer ({z} : Set G))
    (hunique : ∀ A : Subgroup G, A ≤ centralizer ({z} : Set G) →
      IsElementaryAbelian p A → Nat.card A = Nat.card E → A = E)
    (t : G) (htE : t ∈ E) (ht : IsConj z t) : t = z := by
  classical
  obtain ⟨g, hgt⟩ := isConj_iff.mp ht
  let f : G ≃* G := MulAut.conj g
  let F := E.map f.toMonoidHom
  have hfz : f z = t := hgt
  have hEF : E ≤ normalizer (F : Set G) := by
    rw [← map_equiv_normalizer_eq E f]
    intro x hx
    refine ⟨f.symm x, ?_, f.apply_symm_apply x⟩
    rw [hN]
    apply mem_centralizer_singleton_iff.mpr
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply, hfz] using
      (setLike_mul_comm hx htE : x * t = t * x)
  have hEp : IsPGroup p E := IsElementaryAbelian.isPGroup p E
  have hFp : IsPGroup p F := hEp.map f.toMonoidHom
  obtain ⟨T, hT⟩ := (hEp.to_sup_of_normal_right' hFp hEF).exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq G T S
  let c : G ≃* G := MulAut.conj k
  have hmapS : (E ⊔ F).map c.toMonoidHom ≤ (S : Subgroup G) := by
    rw [← hk]
    exact map_mono hT
  have hEc : E.map c.toMonoidHom = E := by
    apply hunique
    · exact (map_mono le_sup_left).trans (hmapS.trans hS)
    · exact IsElementaryAbelian.map c.toMonoidHom
    · exact card_map_of_injective c.injective
  have hFc : F.map c.toMonoidHom = E := by
    let : IsElementaryAbelian p F := IsElementaryAbelian.map f.toMonoidHom
    apply hunique
    · exact (map_mono le_sup_right).trans (hmapS.trans hS)
    · exact IsElementaryAbelian.map c.toMonoidHom
    · rw [card_map_of_injective c.injective, card_map_of_injective f.injective]
  have hFE : F = E := map_injective c.injective (hFc.trans hEc.symm)
  have hgN : g ∈ normalizer (E : Set G) := mem_normalizer_iff_map_conj_eq.mpr hFE
  have hgz : g * z * g⁻¹ = z :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hN ▸ hgN))
  exact hgt.symm.trans hgz
