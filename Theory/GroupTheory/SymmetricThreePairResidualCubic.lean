module
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Cubic subgroups inside normal residuals of S₃ × S₃ subgroups

A nontrivial normal two-perfect subgroup of a subgroup of S₃ × S₃
lies in the alternating base of order nine. If it has order three it
is the required subgroup. If it has order nine it contains the first
alternating axis, whose pullback is normal in the original actor.
The conclusion retains containment in the prescribed residual.

Source application: Aschbacher--Smith 14.3.15, printed p.995.
-/

public section
open Subgroup
namespace Theory.GroupTheory.SymmetricThreePair
abbrev PairActor := Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)

theorem exists_normal_cubic_le_of_twoPerfect
    {D : Type*} [Group D] [Finite D]
    (f : D →* PairActor) (hf : Function.Injective f)
    (N : Subgroup D) [N.Normal] (hne : N ≠ ⊥) (hp : IsPPerfect 2 N) :
    ∃ C : Subgroup D, C.Normal ∧ Nat.card C = 3 ∧ C ≤ N := by
  classical
  let B := (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))
  have hB : Nat.card B = 9 := by
    change Nat.card ((alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))) = 9
    rw [←SymmetricThreeProductResidual.residual_eq]
    exact SymmetricThreeProductResidual.residual_card
  have hNB : N.map f ≤ B := by
    rintro _ ⟨x,hx,rfl⟩
    have hh := map_pResidual_le 2 (f.comp N.subtype)
    have ht : (⟨x,hx⟩ : N) ∈ pResidual 2 N := by
      rw [(pResidual_eq_top_iff 2 N).mpr hp]; trivial
    have hm := hh (mem_map_of_mem _ ht)
    rwa [SymmetricThreeProductResidual.residual_eq] at hm
  have hd : Nat.card N ∣ 9 := by
    rw [← card_map_of_injective (K := N) hf]
    exact hB ▸ card_dvd_of_le hNB
  have hc : Nat.card N = 3 ∨ Nat.card N = 9 := by
    have hh := Nat.mem_divisors.mpr ⟨hd,by decide⟩
    have he : (9 : ℕ).divisors = {1,3,9} := by decide
    rw [he,Finset.mem_insert,Finset.mem_insert,Finset.mem_singleton] at hh
    exact hh.resolve_left (fun hz => hne (card_eq_one.mp hz))
  rcases hc with h3 | h9
  · exact ⟨N,inferInstance,h3,le_rfl⟩
  have hmap : N.map f = B := eq_of_le_of_card_ge hNB (by rw [card_map_of_injective hf,h9,hB])
  let L := (alternatingGroup (Fin 3)).prod (⊥ : Subgroup (Equiv.Perm (Fin 3)))
  let C := L.comap f
  have hleft : L ≤ B := prod_mono le_rfl bot_le
  have hrange : L ≤ f.range := by
    rw [←hmap] at hleft
    exact hleft.trans (map_le_range _ _)
  have him : C.map f = L := by
    rw [map_comap_eq,inf_eq_right.mpr hrange]
  have hCN : C ≤ N := by
    apply (map_le_map_iff_of_injective hf).mp
    rw [him,hmap]
    exact hleft
  have hL : Nat.card L = 3 := by
    rw [Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod,card_bot,mul_one,
      nat_card_alternatingGroup,Nat.card_fin]
    decide
  refine ⟨C,inferInstance,?_,hCN⟩
  have hc := card_map_of_injective (K := C) hf
  rw [him,hL] at hc
  exact hc.symm
end Theory.GroupTheory.SymmetricThreePair
