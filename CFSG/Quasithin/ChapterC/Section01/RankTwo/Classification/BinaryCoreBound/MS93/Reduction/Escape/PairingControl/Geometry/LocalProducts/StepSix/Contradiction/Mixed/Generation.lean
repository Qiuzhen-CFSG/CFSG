module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Contradiction.Mixed.Geometry

/-!
# Generating the mixed-commutator plane

The nonzero critical commutator R_4 escapes the chosen order-four edge
plane at alpha'-4. They therefore generate its natural eight-group.
R_4 centralizes Z_(alpha-4), so commuting this supplement equality shows
that R_4 is contained in [Z_(alpha-4),Z_mu]. The given noncontainment in
Z_(alpha'-4) supplies a second direction. The containing fourth/backward
edge plane has order four, so the commutator is the entire plane.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(6), printed p.885.
The hypotheses R_mu = 1 and the opposite commutator noncontainment are
explicit; this module does not assert their source-theorem assembly.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}
namespace EscapingWitness
variable {p : Counterexample geometry} {d : Vertex R} (w : EscapingWitness p d)

private theorem supplement_eq_eight {G : Type*} [Group G]
    (A E K : Subgroup G) [Finite A] (hE : E ≤ A) (hK : K ≤ A)
    (hEcard : Nat.card E = 4) (hAcard : Nat.card A = 8) (hnot : ¬ K ≤ E) :
    K ⊔ E = A := by
  let J := K ⊔ E
  have hJA : J ≤ A := sup_le hK hE
  let : Finite J := Finite.of_injective (inclusion hJA) (inclusion_injective _)
  have hlarge : 4 ≤ Nat.card J := hEcard ▸ card_le_of_le (show E ≤ J from le_sup_right)
  have hne : Nat.card J ≠ 4 := by
    intro hj
    have hEJ : E = J := eq_of_le_of_card_ge le_sup_right (by rw [hEcard, hj])
    exact hnot ((show K ≤ J from le_sup_left).trans hEJ.ge)
  have hdvd : Nat.card J ∣ 8 := hAcard ▸ card_dvd_of_le hJA
  have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  change J = A
  exact eq_of_le_of_card_ge hJA (by omega)


/-- The escaping critical commutator supplements the chosen edge plane. -/
theorem Rfour_sup_chosen_edge (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (hd : Before p.a p.a' d 4) :
    w.toRadiusWitness.Rfour ⊔ edgeDisplacement d w.lam = U R d := by
  have hcard := modules.natural.card_at d (endpoint_color hd)
  let : Finite (U R d) := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  exact supplement_eq_eight _ _ _
    (Initial.edge_le_natural source d w.lam (endpoint_color hd) w.lam_adjacent)
    ((w.toRadiusWitness.Rfour_le_naturals source modules).trans inf_le_right)
    (FirstPairing.StepThree.edge_card p (by omega) initial d w.lam
      (endpoint_color hd) w.lam_adjacent) hcard w.escapes

/-- Commuting the natural supplement puts R_4 inside the mu commutator. -/
theorem Rfour_le_mu_commutator (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (hd : Before p.a p.a' d 4) :
    w.toRadiusWitness.Rfour ≤ ⁅Z R w.fourth, Z R w.mu⁆ := by
  let s : BinaryNaturalStructure source :=
    ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
  obtain ⟨hfour, hdlocal⟩ := source.critical_Z_le_stabilizer geometry
    w.fourth w.fourth_color d w.critical
  have hreduce : ⁅Z R w.fourth, U R d⁆ = w.toRadiusWitness.Rfour :=
    commutator_eq_of_centralizing_sup
      ((sup_comm _ _).trans (s.decomposition_at d (endpoint_color hd)).symm)
      (inf_le_right.trans (centralizer_le hfour))
      ((U_le_Z d).trans (hdlocal.trans (Z_normalized R w.fourth)))
  have hE : edgeDisplacement d w.lam ≤ U R d :=
    Initial.edge_le_natural source d w.lam (endpoint_color hd) w.lam_adjacent
  have hcentral : w.toRadiusWitness.Rfour ≤
      centralizer (Z R w.fourth : Set (FreeAmalgam R)) := by
    let := geometry.Z_elementary (by omega) w.fourth w.fourth_color
    exact ((w.toRadiusWitness.Rfour_le_naturals source modules).trans
      (inf_le_left.trans (U_le_Z w.fourth))).trans (le_centralizer _)
  have heq := commutator_eq_of_centralizing_sup
    (w.Rfour_sup_chosen_edge source hb modules initial hd) hcentral
    (hE.trans ((U_le_Z d).trans (hdlocal.trans (Z_normalized R w.fourth))))
  rw [hreduce] at heq
  rw [← heq]
  apply commutator_mono le_rfl
  rw [← facts.edge_eq d w.lam w.mu (endpoint_color hd)
    w.lam_adjacent w.mu_adjacent w.mu_moving]
  exact (Initial.edge_le_natural source w.mu w.lam (w.mu_color hd) w.mu_adjacent).trans
    (U_le_Z w.mu)

/-- The mu commutator already fills the plane: it contains the nonzero
R_4 in Z_d and also an element outside Z_d. -/
theorem mu_commutator_eq_fourth_intersection (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hd : Before p.a p.a' d 4) (hzero : w.Rmu = ⊥)
    (hnon : ¬ ⁅Z R w.mu, Z R w.fourth⁆ ≤ Z R d) :
    ⁅Z R w.fourth, Z R w.mu⁆ = U R w.choice.back ⊓ U R w.fourth := by
  let K := ⁅Z R w.fourth, Z R w.mu⁆
  let E := U R w.choice.back ⊓ U R w.fourth
  have hKE : K ≤ E := (commutator_mono le_rfl le_sup_left).trans
    (w.mixed_commutator_le_fourth_intersection source hb modules facts initial bad hd hzero)
  have hfour : Nat.card E = 4 :=
    w.fourth_natural_intersection_card source hb modules facts initial bad hd
  let : Finite E := Nat.finite_of_card_ne_zero (by rw [hfour]; decide)
  let : Finite K := Finite.of_injective (inclusion hKE) (inclusion_injective _)
  have hRK : w.toRadiusWitness.Rfour ≤ K :=
    w.Rfour_le_mu_commutator source hb modules facts initial hd
  let : Finite w.toRadiusWitness.Rfour :=
    Finite.of_injective (inclusion hRK) (inclusion_injective _)
  have hRnon := (one_lt_card_iff_ne_bot _).mpr (w.toRadiusWitness.Rfour_ne_bot source)
  have hlarge : 2 < Nat.card K := by
    by_contra! hsmall
    have heq : w.toRadiusWitness.Rfour = K := eq_of_le_of_card_ge hRK (by omega)
    apply hnon
    rw [commutator_comm]
    change K ≤ Z R d
    rw [← heq]
    exact (w.toRadiusWitness.Rfour_le_naturals source modules).trans
      (inf_le_right.trans (U_le_Z d))
  have hdvd : Nat.card K ∣ 4 := hfour ▸ card_dvd_of_le hKE
  have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 4 ≠ 0)⟩
  rw [show Nat.divisors 4 = ({1, 2, 4} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  have hsize : Nat.card K = 4 := by omega
  exact eq_of_le_of_card_ge hKE (hfour.le.trans hsize.ge)

end EscapingWitness
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix
