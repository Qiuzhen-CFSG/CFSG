module

public import Stellmacher.SectionOne.SL2FamilySylowCard

/-!
# Indexed Sylow coordinates in a normal SL₂(2) product

For a finite family of `SL₂(2)` factors generating a normal subgroup `E`,
an ambient Sylow two-subgroup meets `E` in the join of its intersections
with the individual factors, each of order two.

Each factor is normal in `E`: it normalizes itself, while the other factors
centralize it. Restricting the ambient Sylow first to `E` and then to each
order-six factor gives the order-two coordinate intersections. The factors
are centerless and pairwise commute, which supplies genuine supremum
independence. Product cardinality then gives the coordinate join the same
order as the Sylow intersection with `E`, proving equality.

This is the existing indexed Sylow calculation from the generating-coordinate
argument, shared with the actual coordinate residual and natural-line steps.
It concerns group factors, without asserting independence of arbitrary
modules. Source: Stellmacher (2.2), journal p.20, and its applications in
(4.6) and (6.3); `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionOne
universe u

public theorem sl2_family_sylow_coordinates
    {G : Type u} [Group G] [Finite G]
    (T : Sylow 2 G) (E : Subgroup G) (hEnormal : E.Normal)
    {n : ℕ} (D : Fin n → Subgroup G)
    (hprod : IsInternalDirectProductFamily E D)
    (hSL : ∀ i, IsSL2Two (D i)) :
    ((T : Subgroup G) ⊓ E) = ⨆ i, (T : Subgroup G) ⊓ D i ∧
      ∀ i, Nat.card (↑((T : Subgroup G) ⊓ D i)) = 2 := by
  classical
  have hDiE (i : Fin n) : D i ≤ E := by
    rw [hprod.1]
    exact le_iSup D i
  have hDinormal (i : Fin n) : ((D i).subgroupOf E).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer (hDiE i)).2
    rw [hprod.1]
    apply iSup_le
    intro j
    by_cases hji : j = i
    · subst j
      exact (D i).le_normalizer
    · have hcent : D j ≤ Subgroup.centralizer (D i : Set G) := by
        rw [Subgroup.le_centralizer_iff]
        intro x hx y hy
        exact (hprod.2.2 i j (Ne.symm hji) x hx y hy).symm
      exact hcent.trans (Subgroup.centralizer_le_normalizer (D i : Set G))
  let _ : E.Normal := hEnormal
  obtain ⟨TE, hTE⟩ := T.exists_subgroupOf_eq_of_normal E
  have hQcard (i : Fin n) :
      Nat.card (↑((T : Subgroup G) ⊓ D i)) = 2 := by
    have hDicard : Nat.card ((D i).subgroupOf E) = 6 := by
      rw [natCard_subgroupOf_eq (D i) E (hDiE i)]
      exact
        Stellmacher.SectionOne.RankOneThreeGroupAssembly.isSL2Two_card
          (hSL i)
    let _ : ((D i).subgroupOf E).Normal := hDinormal i
    have hc := Stellmacher.SectionOne.natCard_inf_sylow_normal_card_six
      TE ((D i).subgroupOf E) hDicard
    have hinf : (TE : Subgroup E) ⊓ (D i).subgroupOf E =
        ((T : Subgroup G) ⊓ D i).subgroupOf E := by
      rw [hTE]
      rfl
    rw [hinf,
      natCard_subgroupOf_eq _ E (inf_le_right.trans (hDiE i))] at hc
    exact hc
  have hcomm : Pairwise fun i j => ∀ x y : G,
      x ∈ D i → y ∈ D j → Commute x y := by
    intro i j hij x y hx hy
    exact hprod.2.2 i j hij x hx y hy
  have hind : iSupIndep D :=
    Subgroup.iSupIndep_of_centerless_of_pairwise_commute D
      (fun i =>
        Stellmacher.SectionOne.RankOneThreeGroupAssembly.center_eq_bot_of_isSL2Two
          (hSL i)) hcomm
  let Q : Fin n → Subgroup G := fun i => (T : Subgroup G) ⊓ D i
  have hQcomm : Pairwise fun i j => ∀ x y : G,
      x ∈ Q i → y ∈ Q j → Commute x y := by
    intro i j hij x y hx hy
    exact hcomm hij x y hx.2 hy.2
  have hRcard : Nat.card (↑(⨆ i, Q i)) = 2 ^ n := by
    have hc := Subgroup.natCard_iSup_of_iSupIndep Q hQcomm
      (hind.mono fun i => inf_le_right)
    have hQcard' : ∀ i, Nat.card (Q i) = 2 := by
      intro i
      exact hQcard i
    simp only [hQcard'] at hc
    simpa using hc
  have hinj : Function.Injective D := by
    intro i j hij
    by_contra hne
    have hdisj : Disjoint (D i) (D j) := hprod.2.1 i j hne
    have hbot : D i = ⊥ := by
      rw [← hij] at hdisj
      exact (disjoint_self.mp hdisj)
    have hcardOne : Nat.card (D i) = 1 :=
      (Subgroup.eq_bot_iff_card (D i)).mp hbot
    have hcardSix :=
      Stellmacher.SectionOne.RankOneThreeGroupAssembly.isSL2Two_card (hSL i)
    omega
  have hTEcard : Nat.card (↑((T : Subgroup G) ⊓ E)) = 2 ^ n :=
    Stellmacher.SectionOne.sl2_family_sylow_inf_card T E hEnormal D hinj
      hprod hSL hDinormal
  have hRle : (⨆ i, Q i) ≤ (T : Subgroup G) ⊓ E := by
    apply iSup_le
    intro i
    exact le_inf inf_le_left (inf_le_right.trans (hDiE i))
  have hReq : (⨆ i, Q i) = (T : Subgroup G) ⊓ E :=
    Subgroup.eq_of_le_of_card_ge hRle (by rw [hRcard, hTEcard])
  exact ⟨hReq.symm, hQcard⟩

end Stellmacher.SectionOne
