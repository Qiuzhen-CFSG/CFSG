module

public import CFSG.Quasithin.ChapterG.Section08.Defs
public import Theory.GroupTheory.SpecificGroups.CyclicInvertedDihedral
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Embeddings of commuting dihedral products

An odd-prime dihedral group has trivial center. Therefore commuting embedded
products have trivial intersection. Multiplication gives an injective homomorphism
from their external product, with the prime lists joined along `Fin (m + n)`.

This supplies the actual product, rather than only pairwise commuting factors,
in Aschbacher–Smith G.8.6–8, printed p.350.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.ChapterG.Section08
variable {G : Type*} [Group G]

/-- Odd-prime dihedral products have no central elements other than one. -/
theorem DihedralProduct.range_inf_centralizer {n : ℕ} (D : DihedralProduct G n) :
    D.embedding.range ⊓ centralizer (D.embedding.range : Set G) = ⊥ := by
  apply bot_unique
  rintro x ⟨⟨a, rfl⟩, ha⟩
  have hac : a ∈ center (∀ i, DihedralGroup (D.prime i)) := by
    rw [mem_center_iff]
    intro b
    apply D.injective
    simpa only [map_mul] using ha (D.embedding b) ⟨b, rfl⟩
  have ha1 : a = 1 := by
    ext i
    have hi : a i ∈ center (DihedralGroup (D.prime i)) := by
      rw [Subgroup.center_pi] at hac
      exact hac i (Set.mem_univ i)
    rw [DihedralGroup.center_eq_bot_of_odd_ne_one (D.prime_odd i)
      (D.prime_isPrime i).ne_one] at hi
    exact hi
  simpa only [ha1, map_one] using (one_mem (⊥ : Subgroup G))

/-- Commuting faithful products are independent, since their centers vanish. -/
theorem DihedralProduct.disjoint_of_centralizes {m n : ℕ}
    (D : DihedralProduct G m) (E : DihedralProduct G n)
    (hc : D.embedding.range ≤ centralizer (E.embedding.range : Set G)) :
    Disjoint D.embedding.range E.embedding.range := by
  apply disjoint_iff_inf_le.mpr
  exact (le_inf inf_le_right (inf_le_left.trans hc)).trans E.range_inf_centralizer.le

private def finAddEquiv {m n : ℕ} (H : Fin (m + n) → Type*) [∀ i, Group (H i)] :
    (∀ i, H i) ≃* ((∀ i, H (Fin.castAdd n i)) × (∀ j, H (Fin.natAdd m j))) where
  toFun x := (fun i => x (Fin.castAdd n i), fun j => x (Fin.natAdd m j))
  invFun x := Fin.addCases x.1 x.2
  left_inv x := funext (Fin.addCases_castAdd_natAdd x)
  right_inv x := by ext <;> simp
  map_mul' _ _ := rfl

/-- Join two commuting products, retaining both prime lists and their actual ranges. -/
theorem DihedralProduct.exists_join {m n : ℕ}
    (D : DihedralProduct G m) (E : DihedralProduct G n)
    (hc : D.embedding.range ≤ centralizer (E.embedding.range : Set G)) :
    ∃ F : DihedralProduct G (m + n),
      F.embedding.range = D.embedding.range ⊔ E.embedding.range ∧
      F.prime = Fin.append D.prime E.prime := by
  let p := Fin.append D.prime E.prime
  let e : (∀ i, DihedralGroup (p i)) ≃*
      ((∀ i, DihedralGroup (D.prime i)) × (∀ i, DihedralGroup (E.prime i))) :=
    by
      refine (finAddEquiv (fun i => DihedralGroup (p i))).trans
        (MulEquiv.prodCongr (MulEquiv.piCongrRight fun i => ?_)
          (MulEquiv.piCongrRight fun i => ?_))
      · change DihedralGroup (Fin.append D.prime E.prime (Fin.castAdd n i)) ≃*
          DihedralGroup (D.prime i)
        rw [Fin.append_left]
      · change DihedralGroup (Fin.append D.prime E.prime (Fin.natAdd m i)) ≃*
          DihedralGroup (E.prime i)
        rw [Fin.append_right]
  have hcomm : ∀ a b, Commute (D.embedding a) (E.embedding b) := by
    intro a b
    exact (hc ⟨a, rfl⟩ (E.embedding b) ⟨b, rfl⟩).symm
  let f := (D.embedding.noncommCoprod E.embedding hcomm).comp e.toMonoidHom
  have hf : Function.Injective f :=
    ((MonoidHom.noncommCoprod_injective D.embedding E.embedding hcomm).mpr
      ⟨D.injective, E.injective, D.disjoint_of_centralizes E hc⟩).comp e.injective
  have hp : ∀ i, (p i).Prime := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [p] using D.prime_isPrime j
    · simpa [p] using E.prime_isPrime j
  have ho : ∀ i, Odd (p i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [p] using D.prime_odd j
    · simpa [p] using E.prime_odd j
  refine ⟨⟨p, hp, ho, f, hf⟩, ?_, rfl⟩
  change ((D.embedding.noncommCoprod E.embedding hcomm).comp e.toMonoidHom).range = _
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective,
    ← MonoidHom.range_eq_map, MonoidHom.noncommCoprod_range]

/-- Reindex an actual product without changing its ambient range. -/
theorem DihedralProduct.exists_reindex {m n : ℕ} (D : DihedralProduct G n)
    (e : Fin m ≃ Fin n) :
    ∃ E : DihedralProduct G m,
      E.embedding.range = D.embedding.range ∧ ∀ i, E.prime i = D.prime (e i) := by
  let f : (∀ i, DihedralGroup (D.prime i)) ≃* ∀ j, DihedralGroup (D.prime (e j)) :=
    { toFun := fun g j => g (e j)
      invFun := Equiv.piCongrLeft (fun i => DihedralGroup (D.prime i)) e
      left_inv := fun g =>
        (Equiv.piCongrLeft (fun i => DihedralGroup (D.prime i)) e).apply_symm_apply g
      right_inv := by intro g; funext j; simp only [Equiv.piCongrLeft_apply_apply]
      map_mul' := fun _ _ => rfl }
  refine ⟨⟨fun i => D.prime (e i), fun i => D.prime_isPrime (e i),
    fun i => D.prime_odd (e i), D.embedding.comp f.symm.toMonoidHom,
    D.injective.comp f.symm.injective⟩, ?_, fun _ => rfl⟩
  change (D.embedding.comp f.symm.toMonoidHom).range = _
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr f.symm.surjective,
    ← MonoidHom.range_eq_map]

end CFSG.Quasithin.ChapterG.Section08
