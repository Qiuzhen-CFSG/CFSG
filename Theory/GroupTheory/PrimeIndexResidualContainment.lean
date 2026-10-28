module
public import Theory.GroupTheory.PResidual.PrimeSection

/-!
# Normal intersections at prime index

Let a p-perfect subgroup Y and a p-subgroup S generate P, with S of prime
index in P. If P normalizes L but Y is not contained in L, then P∩L lies
in O_p(P). Indeed, a normal subgroup not contained in S would supplement
S by the prime-index argument. P-perfectness would then put Y inside L.

Source application: Aschbacher--Smith, original15.2.4, printed p.1106.
-/

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

public theorem inf_le_pCore_of_prime_index_of_not_le {p q : ℕ} [Fact p.Prime]
    {Y S L : Subgroup G} (hY : IsPPerfect p Y) (hS : IsPGroup p S)
    (hq : q.Prime) (hi : S.relIndex (Y ⊔ S) = q)
    (hn : Y ⊔ S ≤ normalizer (L : Set G)) (hout : ¬ Y ≤ L) :
    (Y ⊔ S) ⊓ L ≤ (Y ⊔ S).pCoreIn p := by
  let P := Y ⊔ S
  let D := P ⊓ L
  have hSP : S ≤ P := le_sup_right
  have hDP : D ≤ P := inf_le_left
  have hjoin : D ⊔ S ≤ P := sup_le hDP hSP
  have hm := relIndex_mul_relIndex S (D ⊔ S) P le_sup_right hjoin
  rw [hi] at hm
  have hd : S.relIndex (D ⊔ S) ∣ q := ⟨_, hm.symm⟩
  have hDS : D ≤ S := by
    rcases (Nat.dvd_prime hq).mp hd with hh | hh
    · exact le_sup_left.trans (relIndex_eq_one.mp hh)
    · have he : (D ⊔ S).relIndex P = 1 := by
        rw [hh] at hm
        exact Nat.eq_of_mul_eq_mul_left hq.pos (by simpa using hm)
      have hcover : P ≤ D ⊔ S := relIndex_eq_one.mp he
      let : (L.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hn
      have hYP : IsPPerfect p (Y.subgroupOf P) :=
        hY.of_surjective (subgroupOfEquivOfLe (show Y ≤ P from le_sup_left)).symm.toMonoidHom
          (subgroupOfEquivOfLe (show Y ≤ P from le_sup_left)).symm.surjective
      have hle : Y.subgroupOf P ≤ L.subgroupOf P ⊔ S.subgroupOf P := by
        have he' : D.subgroupOf P = L.subgroupOf P := by
          ext x
          exact ⟨fun h => h.2,fun h => ⟨x.property,h⟩⟩
        rw [←he',←subgroupOf_sup hDP hSP]
        exact comap_mono ((show Y ≤ P from le_sup_left).trans hcover)
      have hh' := le_normal_of_isPPerfect_of_le_sup_pGroup
        (Y.subgroupOf P) (L.subgroupOf P) (S.subgroupOf P) hYP hS.comap_subtype hle
      exact (hout (fun x hx => hh' (show (⟨x,(show Y ≤ P from le_sup_left) hx⟩ : P) ∈ Y.subgroupOf P from hx))).elim
  exact le_pCoreIn_of_normalizes (hS.to_le hDS) hDP
    ((le_inf P.le_normalizer hn).trans inf_normalizer_le_normalizer_inf)
end Subgroup
