module

public import Mathlib.GroupTheory.Sylow

/-!
# Sylow subgroups and normal coprime supplements

Let `D` be a normal subgroup of a finite group whose order is not divisible
by a prime `p`.  If `S` is a Sylow `p`-subgroup of `P`, then its ambient
image remains Sylow after adjoining `D` to `P`.

The proof compares indices in the subgroup diamond formed by `D`, `P`, and
`D ⊔ P`.  Normality shows that the relative index of `P` in `D ⊔ P`
divides the order of `D`, hence is prime to `p`.  Multiplicativity of
relative indices then shows that the image of `S` has index prime to `p` in
the join.

This standard finite-group transfer is used for the normal odd Fitting
supplement in Stellmacher (5.2), and exposes the reusable form of a private
special case in the proof of (3.9).  Source: B. Stellmacher, Journal of
Algebra 190 (1997), pp. 23 and 29.
-/

private theorem prime_not_dvd_index_of_normal_sup
    {G : Type*} [Group G] [Finite G]
    {D P : Subgroup G} [D.Normal] {p : ℕ}
    (hDcard : ¬ p ∣ Nat.card D) (hDP : D ⊔ P = ⊤) :
    ¬ p ∣ P.index := by
  intro hpP
  have hrel_eq : P.relIndex (P ⊔ D) = (P ⊓ D).relIndex D := by
    have hDrel : D.relIndex (P ⊔ D) = (P ⊓ D).relIndex P := by
      calc
        D.relIndex (P ⊔ D) = D.relIndex P := by simp
        _ = (P ⊓ D).relIndex P := by
          symm
          simpa [inf_comm] using
            (Subgroup.inf_relIndex_left (H := P) (K := D))
    have hmul :
        (P ⊓ D).relIndex P * P.relIndex (P ⊔ D) =
          (P ⊓ D).relIndex D * (P ⊓ D).relIndex P := by
      calc
        (P ⊓ D).relIndex P * P.relIndex (P ⊔ D) =
            (P ⊓ D).relIndex (P ⊔ D) :=
          Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left le_sup_left
        _ = (P ⊓ D).relIndex D * D.relIndex (P ⊔ D) := by
          symm
          exact Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_right
        _ = (P ⊓ D).relIndex D * (P ⊓ D).relIndex P := by rw [hDrel]
    have hpos : 0 < (P ⊓ D).relIndex P := by
      exact Nat.pos_of_ne_zero (by
        dsimp [Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite)
    have hmul' :
        (P ⊓ D).relIndex P * P.relIndex (P ⊔ D) =
          (P ⊓ D).relIndex P * (P ⊓ D).relIndex D := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
    exact Nat.eq_of_mul_eq_mul_left hpos hmul'
  have hidx : P.relIndex (P ⊔ D) = P.index := by
    rw [show P ⊔ D = ⊤ by simpa [sup_comm] using hDP]
    exact Subgroup.relIndex_top_right (H := P)
  have hdvd : P.index ∣ Nat.card D := by
    rw [← hidx, hrel_eq]
    exact Subgroup.relIndex_dvd_card (H := P ⊓ D) (K := D)
  exact hDcard (hpP.trans hdvd)

/-- Adjoining a normal subgroup of order prime to `p` preserves the ambient
image of a Sylow `p`-subgroup. -/
public theorem Sylow.exists_map_eq_map_of_normal_coprime_sup
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (D P : Subgroup G) [D.Normal]
    (hDcard : ¬ p ∣ Nat.card D) (S : Sylow p P) :
    ∃ T : Sylow p ↑(D ⊔ P),
      (T : Subgroup ↑(D ⊔ P)).map (D ⊔ P : Subgroup G).subtype =
        (S : Subgroup P).map P.subtype := by
  classical
  let L : Subgroup G := D ⊔ P
  let SG : Subgroup G := (S : Subgroup P).map P.subtype
  have hDL : D ≤ L := le_sup_left
  have hPL : P ≤ L := le_sup_right
  have hSL : SG ≤ L := (Subgroup.map_subtype_le _).trans hPL
  let DL : Subgroup L := D.subgroupOf L
  let PL : Subgroup L := P.subgroupOf L
  let SL : Subgroup L := SG.subgroupOf L
  have hDLnormal : DL.Normal := (inferInstance : D.Normal).subgroupOf L
  let _ : DL.Normal := hDLnormal
  have hDLcard : Nat.card DL = Nat.card D := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDL).toEquiv
  have hDLcop : ¬ p ∣ Nat.card DL := by simpa [hDLcard] using hDcard
  have hsup : DL ⊔ PL = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hDL hPL]
    exact Subgroup.subgroupOf_self L
  have hPindex : ¬ p ∣ PL.index :=
    prime_not_dvd_index_of_normal_sup hDLcop hsup
  have hSP : SG.subgroupOf P = (S : Subgroup P) := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le _)]
  have hSindexP : ¬ p ∣ SG.relIndex P := by
    change ¬ p ∣ (SG.subgroupOf P).index
    rw [hSP]
    exact S.not_dvd_index
  have hSrel : SG.relIndex P * P.relIndex L = SG.relIndex L :=
    Subgroup.relIndex_mul_relIndex SG P L (Subgroup.map_subtype_le _) hPL
  have hPindex' : ¬ p ∣ P.relIndex L := by
    change ¬ p ∣ (P.subgroupOf L).index
    exact hPindex
  have hSindexL : ¬ p ∣ SL.index := by
    change ¬ p ∣ SG.relIndex L
    intro hdvd
    have hprod : p ∣ SG.relIndex P * P.relIndex L := by
      rwa [hSrel]
    rcases (Fact.out : p.Prime).dvd_mul.mp hprod with hdvd | hdvd
    · exact hSindexP hdvd
    · exact hPindex' hdvd
  have hSGp : IsPGroup p SG := S.isPGroup'.map P.subtype
  have hSLp : IsPGroup p SL :=
    hSGp.of_equiv (Subgroup.subgroupOfEquivOfLe hSL).symm
  let T : Sylow p L := hSLp.toSylow hSindexL
  refine ⟨T, ?_⟩
  have hT : (T : Subgroup L) = SL := IsPGroup.toSylow_coe hSLp hSindexL
  rw [hT]
  exact Subgroup.map_subgroupOf_eq_of_le hSL
