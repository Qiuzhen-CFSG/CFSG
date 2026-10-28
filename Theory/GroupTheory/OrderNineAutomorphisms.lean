module

public import Theory.SpecificGroups.SymmetricFourSolvable
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Automorphisms of a group of order nine are solvable

The eight nonidentity elements form four inverse pairs. Automorphisms act
on these pairs, with image in the solvable symmetric group on four letters.
An automorphism in the kernel sends every element to itself or its inverse;
two such automorphisms commute. Thus the full automorphism group is solvable.

This elementary inverse-pair argument supplies the affine branch of the
primitive degree-nine calculation for the A₉ case of Aschbacher–Smith,
Theorem 0.1.2(3), condition K (printed pp.4 and 482).
-/

open Equiv

namespace MulAut

variable {G : Type*} [Group G]

private def inversePairs (G : Type*) [Group G] := by
  classical
  exact {s : Finset G // ∃ x : G, x ≠ 1 ∧ s = {x, x⁻¹}}

private noncomputable def pairPerm (a : MulAut G) : Perm (inversePairs G) := by
  classical
  apply (Equiv.finsetCongr a.toEquiv).subtypeEquiv
  intro s
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨a x, by simpa using hx, by simp⟩
  · rintro ⟨x, hx, he⟩
    refine ⟨a.symm x, by simpa using hx, ?_⟩
    calc
      s = (Equiv.finsetCongr a.toEquiv).symm ((Equiv.finsetCongr a.toEquiv) s) :=
        ((Equiv.finsetCongr a.toEquiv).symm_apply_apply s).symm
      _ = (Equiv.finsetCongr a.toEquiv).symm {x,x⁻¹} := congrArg _ he
      _ = _ := by simp

private noncomputable def pairHom : MulAut G →* Perm (inversePairs G) where
  toFun := pairPerm
  map_one' := by
    classical
    apply Equiv.ext
    intro s
    apply Subtype.ext
    change Finset.map (Function.Embedding.refl G) s.val = s.val
    exact Finset.map_refl
  map_mul' a b := by
    classical
    apply Equiv.ext
    intro s
    apply Subtype.ext
    change Finset.map (a * b).toEquiv.toEmbedding s.val =
      Finset.map a.toEquiv.toEmbedding (Finset.map b.toEquiv.toEmbedding s.val)
    rw [Finset.map_map]
    rfl

private theorem pair_ker_apply (a : (pairHom (G := G)).ker) (x : G) :
    a.val x = x ∨ a.val x = x⁻¹ := by
  classical
  by_cases hx : x = 1
  · simp [hx]
  · let s : inversePairs G := ⟨{x,x⁻¹}, x, hx, rfl⟩
    have hs := congrArg (fun p : Perm (inversePairs G) => (p s).val) a.property
    change Finset.map a.val.toEquiv.toEmbedding {x,x⁻¹} = {x,x⁻¹} at hs
    have hmem : a.val x ∈ ({x,x⁻¹} : Finset G) := by
      rw [← hs]
      exact Finset.mem_map.mpr ⟨x, by simp, rfl⟩
    simpa using hmem

private theorem pair_ker_solvable : Group.IsSolvable (pairHom (G := G)).ker := by
  apply Group.isSolvable_of_comm
  intro a b
  apply Subtype.ext
  apply MulEquiv.ext
  intro x
  change a.val (b.val x) = b.val (a.val x)
  rcases pair_ker_apply a x with ha | ha <;>
    rcases pair_ker_apply b x with hb | hb <;>
    simp [ha, hb]

private theorem inv_ne_self_of_card_nine [Finite G] (hG : Nat.card G = 9)
    (x : G) (hx : x ≠ 1) : x⁻¹ ≠ x := by
  intro hi
  have hs : x ^ 2 = 1 := by simpa only [pow_two, hi] using inv_mul_cancel x
  have hp := pow_card_eq_one' (x := x)
  rw [hG, show 9 = 2 * 4 + 1 from rfl, pow_add, pow_mul, hs] at hp
  exact hx (by simpa using hp)

private theorem card_pairs_le_four [Finite G] (hG : Nat.card G = 9) :
    Nat.card (inversePairs G) ≤ 4 := by
  classical
  let r : inversePairs G → G := fun s => s.property.choose
  have hr (s : inversePairs G) : r s ≠ 1 ∧ s.val = {r s, (r s)⁻¹} :=
    s.property.choose_spec
  let f : inversePairs G × Bool → {x : G // x ≠ 1} := fun z =>
    ⟨if z.2 then r z.1 else (r z.1)⁻¹, by split <;> simp_all⟩
  have hf : Function.Injective f := by
    rintro ⟨s,b⟩ ⟨t,c⟩ he
    have he' := congrArg Subtype.val he
    have hs : s = t := by
      apply Subtype.ext
      rw [(hr s).2, (hr t).2]
      cases b <;> cases c <;> simp only [f, Bool.false_eq_true, ↓reduceIte] at he'
      · rw [inv_inj.mp he']
      · rw [← he', inv_inv, Finset.pair_comm]
      · rw [he', inv_inv, Finset.pair_comm]
      · rw [he']
    subst t
    have hb : b = c := by
      cases b <;> cases c
      · rfl
      · exact False.elim (inv_ne_self_of_card_nine hG _ (hr s).1 he')
      · exact False.elim (inv_ne_self_of_card_nine hG _ (hr s).1 he'.symm)
      · rfl
    subst c
    rfl
  have hc := Nat.card_le_card_of_injective f hf
  let := Fintype.ofFinite G
  have hn : Nat.card {x : G // x ≠ 1} = 8 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun x : G => x = 1)]
    simp [← Nat.card_eq_fintype_card, hG]
  rw [Nat.card_prod, (show Nat.card Bool = 2 by simp [Nat.card_eq_fintype_card]), hn] at hc
  omega

/-- The automorphism group of any group of order nine is solvable. -/
public theorem isSolvable_of_card_nine [Finite G] (hG : Nat.card G = 9) : Group.IsSolvable (MulAut G) := by
  classical
  let : Finite (inversePairs G) := inferInstanceAs (Finite {s : Finset G // _})
  let := Fintype.ofFinite (inversePairs G)
  have hcard : Fintype.card (inversePairs G) ≤ Fintype.card (Fin 4) := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_fin] using card_pairs_le_four hG
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let : Group.IsSolvable (Perm (Fin 4)) := Perm.isSolvable_fin_four
  let : Group.IsSolvable (Perm (inversePairs G)) :=
    Group.isSolvable_of_isSolvable_injective (Perm.viaEmbeddingHom_injective e)
  let : Group.IsSolvable (pairHom (G := G)).ker := pair_ker_solvable
  exact Group.isSolvable_of_ker_le_range (pairHom (G := G)).ker.subtype pairHom (by simp)

end MulAut
