module

public import Theory.GroupTheory.PResidual.PrimeSection
/-!
# A cubic index after adjoining the intrinsic two-core

If J = CX, C is normal in J, and X/O₂(X) has order three, then the
index of C O₂(J) divides three when O₂(X) lies in O₂(J). If J is
two-perfect, index one would give J = C: the remaining quotient is a
two-group. Thus C ≠ J makes the index exactly three.

All normality is relative to J; no ambient normality is required.
Source application: the sufficient two-kernel replacement calculation for
Aschbacher–Smith 13.8.20, printed p.954/PDF p.971.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- Cubic quotient and two-perfectness determine the enlarged-kernel index. -/
theorem cubic_relIndex_sup_pCoreIn (C X J : Subgroup G)
    (hgen : C ⊔ X = J) (hn : J ≤ normalizer (C : Set G))
    (hp : IsPPerfect 2 J) (hc : Nat.card (X ⧸ pCore 2 X) = 3)
    (hcore : X.pCoreIn 2 ≤ J.pCoreIn 2) (hne : C ≠ J) :
    (C ⊔ J.pCoreIn 2).relIndex J = 3 := by
  let N := C ⊔ J.pCoreIn 2
  have hCJ : C ≤ J := hgen ▸ le_sup_left
  have hXJ : X ≤ J := hgen ▸ le_sup_right
  have hNJ : N ≤ J := sup_le hCJ (pCoreIn_le 2 J)
  let _ : (C.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer hCJ).mpr hn
  have hJn : J ≤ normalizer (N : Set G) :=
    (le_inf hn (J.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  let _ : (N.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer hNJ).mpr hJn
  have hN : N ⊔ X = J := le_antisymm (sup_le hNJ hXJ)
    (hgen ▸ sup_le_sup le_sup_left le_rfl)
  have hs : N.subgroupOf J ⊔ X.subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup hNJ hXJ, hN, subgroupOf_self]
  have he : N.relIndex J = N.relIndex X := by
    change (N.subgroupOf J).index = _
    rw [← relIndex_top_right, ← hs, relIndex_sup_left, relIndex_subgroupOf hXJ]
  have hci : (X.pCoreIn 2).relIndex X = 3 := by
    change (((pCore 2 X).map X.subtype).comap X.subtype).index = 3
    rw [comap_map_eq_self_of_injective X.subtype_injective, index_eq_card]
    exact hc
  have hd : N.relIndex J ∣ 3 := by
    rw [he, ← hci]
    exact relIndex_dvd_of_le_left X (hcore.trans le_sup_right)
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with h | h
  · have ht : J ≤ N := relIndex_eq_one.mp h
    have htop : IsPPerfect 2 (⊤ : Subgroup J) :=
      hp.of_surjective topEquiv.symm.toMonoidHom topEquiv.symm.surjective
    have hP : IsPGroup 2 ((J.pCoreIn 2).subgroupOf J) :=
      (isPGroup_pCoreIn 2 J).comap_subtype
    have hle : (⊤ : Subgroup J) ≤ C.subgroupOf J ⊔ (J.pCoreIn 2).subgroupOf J := by
      rw [← subgroupOf_sup hCJ (pCoreIn_le 2 J)]
      intro j _
      exact ht j.property
    have hh := le_normal_of_isPPerfect_of_le_sup_pGroup
      (⊤ : Subgroup J) (C.subgroupOf J) ((J.pCoreIn 2).subgroupOf J) htop hP hle
    exact (hne (le_antisymm hCJ (fun x hx => hh (show (⟨x, hx⟩ : J) ∈ ⊤ from trivial)))).elim
  · exact h

end Subgroup
