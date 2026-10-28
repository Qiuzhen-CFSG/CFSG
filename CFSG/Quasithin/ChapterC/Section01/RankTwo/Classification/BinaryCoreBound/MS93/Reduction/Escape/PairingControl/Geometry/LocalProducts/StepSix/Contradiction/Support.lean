module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Contradiction.Intersections

/-!
# The support deduction in the R_4 argument

A subgroup of U_back outside Z_start supplements the common edge plane,
since the latter has order four in the natural group of order eight.
The fixed summand of Z_back lies in Z_start. Thus any such subgroup
centralizing the critical endpoint would make Z_back normalize Z_endpoint.

The opposite-module obstruction to that normalization is kept explicit.
It is the first use of step (2) on p.885 and must still be proved from the
source hypotheses before the full step-(6) contradiction is assembled.
The zero branch likewise retains its mixed-intersection calculation.

Source: MS93 (4.3.2)(6), printed p.885.
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

/-- The fixed summand at the backward vertex lies in the original Z-layer. -/
theorem fixed_back_le_start_Z (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry) :
    Z R w.choice.back ⊓ centralizer (stabilizer R w.choice.back : Set (FreeAmalgam R)) ≤
      Z R p.a := by
  rw [← modules.X_eq_Z p.a p.color_a]
  intro x hx
  apply mem_omegaCenter_iff.mpr
  have hZQ : Z R w.choice.back ≤ Q R p.a :=
    (moving_Z_le_V w.choice.moving).trans (geometry.V_le_Q hb p.a p.color_a)
  let := geometry.Z_elementary (by omega) w.choice.back w.toRadiusWitness.back_color
  exact ⟨hZQ hx.1, elemPow_eq_one_of_isElementaryAbelian x hx.1,
    fun y hy => hx.2 y
      (Q_le_stabilizer_of_dist_two R p.a w.choice.back p.color_a w.choice.moving.1 hy)⟩

/-- The literal product decomposition in the first R_mu branch. -/
theorem back_Z_eq_sup_of_not_le (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (K : Subgroup (FreeAmalgam R)) (hK : K ≤ U R w.choice.back)
    (hnot : ¬ K ≤ Z R p.a) :
    Z R w.choice.back = K ⊔ (Z R w.choice.back ⊓ Z R p.a) := by
  let E := edgeDisplacement p.a w.choice.edge
  have he := w.back_natural_inf_start_Z source hb modules facts initial bad
  have hEU : E ≤ U R w.choice.back := he.ge.trans inf_le_left
  have hEZ : E ≤ Z R p.a := he.ge.trans inf_le_right
  have hEcard : Nat.card E = 4 := FirstPairing.StepThree.edge_card p (by omega)
    initial p.a w.choice.edge p.color_a w.choice.adjacent_start
  have hUcard := modules.natural.card_at w.choice.back w.toRadiusWitness.back_color
  let : Finite (U R w.choice.back) := Nat.finite_of_card_ne_zero (by rw [hUcard]; decide)
  have hJ : K ⊔ E = U R w.choice.back :=
    supplement_eq_eight _ _ _ hEU hK hEcard hUcard (fun h => hnot (h.trans hEZ))
  let s : BinaryNaturalStructure source :=
    ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
  apply le_antisymm _ (sup_le (hK.trans (U_le_Z _)) inf_le_left)
  conv_lhs => rw [s.decomposition_at w.choice.back w.toRadiusWitness.back_color]
  apply sup_le
  · conv_lhs => rw [← hJ]
    have hE : E ≤ Z R w.choice.back ⊓ Z R p.a :=
      le_inf (hEU.trans (U_le_Z _)) hEZ
    exact sup_le le_sup_left (hE.trans le_sup_right)
  · have hF : Z R w.choice.back ⊓
        centralizer (stabilizer R w.choice.back : Set (FreeAmalgam R)) ≤
        Z R w.choice.back ⊓ Z R p.a :=
      le_inf inf_le_left (w.fixed_back_le_start_Z source hb modules)
    exact hF.trans le_sup_right

/-- A centralizing subgroup outside Z_start would normalize the endpoint Z. -/
theorem back_commutator_le_endpoint_of_not_le (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (K : Subgroup (FreeAmalgam R)) (hK : K ≤ U R w.choice.back)
    (hC : K ≤ centralizer (Z R p.a' : Set (FreeAmalgam R)))
    (hnot : ¬ K ≤ Z R p.a) : ⁅Z R w.choice.back, Z R p.a'⁆ ≤ Z R p.a' := by
  apply le_normalizer_iff_commutator_le_right.mp
  rw [w.back_Z_eq_sup_of_not_le source hb modules facts initial bad K hK hnot]
  exact sup_le (hC.trans (Subgroup.centralizer_le_normalizer _))
    (inf_le_right.trans ((source.critical_Z_le_stabilizer geometry
      p.a p.color_a p.a' p.critical).1.trans (Z_normalized R p.a')))

/-- This isolates precisely the first, still-required use of source step (2). -/
theorem centralizing_back_natural_le_Z (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (obstruction : ¬ ⁅Z R w.choice.back, Z R p.a'⁆ ≤ Z R p.a')
    (K : Subgroup (FreeAmalgam R)) (hK : K ≤ U R w.choice.back)
    (hC : K ≤ centralizer (Z R p.a' : Set (FreeAmalgam R))) : K ≤ Z R p.a := by
  by_contra hnot
  exact obstruction (w.back_commutator_le_endpoint_of_not_le source hb modules facts
    initial bad K hK hC hnot)

/-- The claimed R_4 support follows from the explicit opposite-module obstruction. -/
theorem Rfour_le_Z_of_obstruction (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hlarge : 6 < geometry.b R) (hd : Before p.a p.a' d 4)
    (obstruction : ¬ ⁅Z R w.choice.back, Z R p.a'⁆ ≤ Z R p.a') :
    w.toRadiusWitness.Rfour ≤ Z R p.a :=
  w.centralizing_back_natural_le_Z source hb modules facts initial bad obstruction _
    (w.toRadiusWitness.Rfour_le_backward_natural source facts hd)
    (w.toRadiusWitness.Rfour_centralizes_endpoint source modules hlarge hd)

/-- The last natural-intersection equality in the trivial branch. -/
theorem fourth_intersection_eq_start_of_card_four (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (obstruction : ¬ ⁅Z R w.choice.back, Z R p.a'⁆ ≤ Z R p.a')
    (hcard : Nat.card (U R w.choice.back ⊓ U R w.fourth : Subgroup (FreeAmalgam R)) = 4)
    (hC : U R w.choice.back ⊓ U R w.fourth ≤
      centralizer (Z R p.a' : Set (FreeAmalgam R))) :
    U R w.choice.back ⊓ U R w.fourth = U R w.choice.back ⊓ U R p.a := by
  have hZ := w.centralizing_back_natural_le_Z source hb modules facts initial bad
    obstruction _ inf_le_left hC
  rw [w.back_natural_inf_start_natural source hb modules facts initial bad]
  have hle : U R w.choice.back ⊓ U R w.fourth ≤ edgeDisplacement p.a w.choice.edge := by
    rw [← w.back_natural_inf_start_Z source hb modules facts initial bad]
    exact le_inf inf_le_left hZ
  let : Finite (U R p.a) := Nat.finite_of_card_ne_zero (by
    rw [modules.natural.card_at p.a p.color_a]; decide)
  let : Finite (edgeDisplacement p.a w.choice.edge) := Finite.of_injective
    (inclusion (Initial.edge_le_natural source p.a w.choice.edge p.color_a w.choice.adjacent_start))
    (inclusion_injective _)
  exact eq_of_le_of_card_ge hle (by
    rw [hcard, FirstPairing.StepThree.edge_card p (by omega) initial
      p.a w.choice.edge p.color_a w.choice.adjacent_start])

/-- The printed equality contradicts the original escaping backward edge. -/
theorem false_of_fourth_intersection (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (obstruction : ¬ ⁅Z R w.choice.back, Z R p.a'⁆ ≤ Z R p.a')
    (hcard : Nat.card (U R w.choice.back ⊓ U R w.fourth : Subgroup (FreeAmalgam R)) = 4)
    (hC : U R w.choice.back ⊓ U R w.fourth ≤
      centralizer (Z R p.a' : Set (FreeAmalgam R))) : False := by
  apply w.choice.escapes
  have he := w.fourth_intersection_eq_start_of_card_four source hb modules facts
    initial bad obstruction hcard hC
  rw [w.back_natural_inf_start_natural source hb modules facts initial bad] at he
  rw [← modules.natural.centralizer p.a' p.end_color]
  exact le_inf
    ((Initial.edge_le_natural source p.a w.choice.edge p.color_a w.choice.adjacent_start).trans
      ((U_le_Z p.a).trans
        (source.critical_Z_le_stabilizer geometry p.a p.color_a p.a' p.critical).1))
    ((he ▸ hC).trans (centralizer_le (U_le_Z p.a')))

end EscapingWitness
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix
