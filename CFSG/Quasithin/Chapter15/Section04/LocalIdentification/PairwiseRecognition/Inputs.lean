module

public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.Residual
public import Theory.GroupTheory.PResidual.FiniteImage
public import Mathlib.GroupTheory.Perm.Fin
/-!
# Local overgroups as index-three extensions of the two-residuals

The source factors are two-perfect and normalized by `T₀`. Hence each is
exactly the embedded two-residual of its local overgroup. The S₃ core
quotient makes the common Sylow two-subgroup have index three in each.
These conclusions supply the finite S₆ recognition problem without assuming
any factor identification.

Source: Aschbacher–Smith, 15.4.19–23 and the following paragraph, printed
pp.1162–1165. The Sylow index calculation maps to the actual S₃ quotient.
-/

@[expose] public section

open Subgroup

private theorem residual_join {G : Type*} [Group G] (L T : Subgroup G)
    (hL : IsPPerfect 2 L) (hT : IsPGroup 2 T)
    (hn : T ≤ normalizer (L : Set G)) :
    (pResidual 2 ↥(L ⊔ T)).map (L ⊔ T).subtype = L := by
  let A := L.subgroupOf (L ⊔ T)
  let B := T.subgroupOf (L ⊔ T)
  let eA : L ≃* A := (subgroupOfEquivOfLe le_sup_left).symm
  have hA : IsPPerfect 2 A := hL.of_surjective eA.toMonoidHom eA.surjective
  have hB : IsPGroup 2 B := hT.of_equiv (subgroupOfEquivOfLe le_sup_right).symm
  have hBA : B ≤ normalizer (A : Set ↥(L ⊔ T)) := by
    apply le_normalizer_iff.mpr
    intro t ht a ha
    exact (hn ht (a : G)).mp ha
  have hgen : (A ⊔ A) ⊔ B = ⊤ := by
    rw [sup_idem]
    dsimp [A, B]
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  rw [pResidual_eq_sup_of_normalized_generators A A B hA hA hB hBA hBA hgen,
    sup_idem, map_subgroupOf_eq_of_le le_sup_left]

private theorem sylow_index_three {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) :
    (S : Subgroup H).index = 3 := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 H := by
    ext x
    change e ((QuotientGroup.mk' (pCore 2 H)) x) = 1 ↔ _
    rw [← e.map_one, e.injective.eq_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hker : f.ker ≤ S := hk ▸ pCore_isPGroup.le_sylow_of_normal S
  let R := S.mapSurjective hf
  have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  have hr : Nat.card R = 2 := by
    rw [R.card_eq_multiplicity, hc]
    change 2 ^ (Nat.factorization (3 * 2) 2) = 2
    rw [Nat.factorization_mul (by decide) (by decide)]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  have hi := (R : Subgroup (Equiv.Perm (Fin 3))).card_mul_index
  rw [hc, hr] at hi
  have hindex : (R : Subgroup (Equiv.Perm (Fin 3))).index = 3 := by omega
  change ((S : Subgroup H).map f).index = 3 at hindex
  rwa [Subgroup.index_map_eq _ hf hker] at hindex

namespace CFSG.Quasithin.Chapter15.Section04.Source
variable {G : Type*} [Group G] {d : Geometry G} (h : LocalData d)
include h

theorem LocalData.residual_G₁ (i : Bool) :
    (pResidual 2 (d.G₁ i)).map (d.G₁ i).subtype = d.X i :=
  residual_join _ _ (h.X_perfect i)
    (d.T.isPGroup'.of_injective (inclusion d.T₀_le_T) (inclusion_injective d.T₀_le_T))
    (h.X_normalized i)

theorem LocalData.residual_G₂ (j : Bool) :
    (pResidual 2 (d.G₂ j)).map (d.G₂ j).subtype = d.Y j :=
  residual_join _ _ (h.Y_perfect j)
    (d.T.isPGroup'.of_injective (inclusion d.T₀_le_T) (inclusion_injective d.T₀_le_T))
    (h.Y_normalized j)

end CFSG.Quasithin.Chapter15.Section04.Source

private theorem relIndex_sylow_image {G : Type*} [Group G] [Finite G]
    (I H : Subgroup G) (hHI : H ≤ I) (S : Sylow 2 I)
    (hSH : (S : Subgroup I).map I.subtype ≤ H)
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) :
    ((S : Subgroup I).map I.subtype).relIndex H = 3 := by
  let f := inclusion hHI
  have hSf : (S : Subgroup I) ≤ f.range := by
    intro x hx
    exact ⟨⟨x, hSH ⟨x, hx, rfl⟩⟩, rfl⟩
  let R := S.comapOfInjective f (inclusion_injective hHI) hSf
  have heq : (R : Subgroup H) = ((S : Subgroup I).map I.subtype).subgroupOf H := by
    ext x
    change f x ∈ (S : Subgroup I) ↔ (x : G) ∈ (S : Subgroup I).map I.subtype
    constructor
    · intro hx
      exact ⟨f x, hx, rfl⟩
    · rintro ⟨y, hy, he⟩
      have he' : f x = y := Subtype.ext he.symm
      exact he' ▸ hy
  rw [relIndex, ← heq]
  exact sylow_index_three R e

namespace CFSG.Quasithin.Chapter15.Section04.Source
variable {G : Type*} [Group G] [Finite G] {d : Geometry G} (h : LocalData d)
include h

theorem LocalData.relIndex_T₀_G₁ (i : Bool) : d.T₀.relIndex (d.G₁ i) = 3 := by
  obtain ⟨e⟩ := h.quotient₁ i
  rw [← h.sylow_image i false]
  exact relIndex_sylow_image (d.I i false) (d.G₁ i) le_sup_left (h.sylow i false)
    (by rw [h.sylow_image]; exact le_sup_right) e

theorem LocalData.relIndex_T₀_G₂ (j : Bool) : d.T₀.relIndex (d.G₂ j) = 3 := by
  obtain ⟨e⟩ := h.quotient₂ j
  rw [← h.sylow_image false j]
  exact relIndex_sylow_image (d.I false j) (d.G₂ j) le_sup_right (h.sylow false j)
    (by rw [h.sylow_image]; exact le_sup_right) e

end CFSG.Quasithin.Chapter15.Section04.Source
