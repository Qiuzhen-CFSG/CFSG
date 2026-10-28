module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.EndpointReduction.Order21
public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis
public import BenderSuzuki.External.Huppert.XI.theorem_3_6

/-!
# Excluding the exceptional central cover at degree two

The degree-two actor has order three and lies in L. If the component center
is a two-group, L/Z(L) consequently has order divisible by three. It cannot
be the actual Sz(8), whose checked order is prime to three. Thus the genuine
rank-one cover datum forces Z(L) to be trivial. Source (E1) supplies the
center's two-group property through the proved center = O₂(L) theorem.

The restricted cover datum is explicit: a nontrivial center gives an actual
isomorphism of the quotient with Sz(8). This is the covering-group input used
in the first paragraph of Proposition 16.5.1, not a conclusion asserted by
this module from the full mixed-family list in 16.1.2.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1170 and 1194, Lemma 16.1.2 and Proposition 16.5.1; Huppert–Blackburn,
XI.3.6, for the Suzuki order being prime to three.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter16.Intersections.Bender
variable {G : Type*} [Group G] [Finite G]

theorem Geometry.center_eq_bot_of_suzuki_cover {T : Sylow 2 G} {L R : Subgroup G} {n : ℕ}
    (d : Geometry T L R n)
    (hUC : Nat.card (omegaOneAmbient (commutingSylow T L)) = 2)
    (hV : Nat.card (benderSpace T L) = 8)
    (hZ : IsPGroup 2 (center L))
    (hcover : center L ≠ ⊥ →
      Nonempty ((L ⧸ center L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) :
    center L = ⊥ := by
  by_contra hne
  obtain ⟨e⟩ := hcover hne
  have hX : Nat.card d.actor = 3 := by
    rw [d.actor_card, d.degree_eq_two hUC hV]
    decide
  have hdiv : 3 ∣ Nat.card L := hX ▸ card_dvd_of_le (d.actor_le.trans inf_le_left)
  rw [card_eq_card_quotient_mul_card_subgroup (center L)] at hdiv
  rcases Nat.prime_three.dvd_mul.mp hdiv with hq | hz
  · have he := Nat.card_congr e.toEquiv
    rw [he] at hq
    exact (BenderSuzuki.External.huppert_blackburn_XI_3_6 1 (by decide)).2 hq
  · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ
    rw [hk] at hz
    exact (by decide : ¬ 3 ∣ 2) (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hz)

theorem Geometry.center_eq_bot_of_source_cover {T : Sylow 2 G} {z : G}
    {L R : Subgroup G} {n : ℕ} (d : Geometry T L R n)
    (h : StandardSetup T z L) (heven : HasEvenTypeCentralizers G)
    (hUC : Nat.card (omegaOneAmbient (commutingSylow T L)) = 2)
    (hV : Nat.card (benderSpace T L) = 8)
    (hcover : center L ≠ ⊥ →
      Nonempty ((L ⧸ center L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) :
    center L = ⊥ := by
  apply d.center_eq_bot_of_suzuki_cover hUC hV _ hcover
  rw [heven.component_center_eq_twoCore h.involution h.component]
  exact pCore_isPGroup

end CFSG.Quasithin.Chapter16.Intersections.Bender
