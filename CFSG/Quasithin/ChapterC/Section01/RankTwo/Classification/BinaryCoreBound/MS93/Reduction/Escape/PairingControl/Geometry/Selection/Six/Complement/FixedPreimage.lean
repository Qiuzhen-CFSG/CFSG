module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Six.Complement.Displacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.ImageCases.LargeImage.Geometry

/-!
# The fixed-preimage part of the complementary radius bound

At a moving pair, U at the neighbor meets B at the center in exactly the
common edge plane. The plane has order four in an eight-group. If the
intersection were larger, the whole natural group would be fixed modulo Z;
its kernel commutator would then be a normal subgroup inside the edge plane,
contrary to irreducibility.

The natural-section triple identity puts the radius commutator in B at
the middle vertex. Consequently its containment in U at the starting
vertex implies the initial edge bound used by Displacement. This isolates
the remaining natural-layer containment from the proved fixed-preimage
and cardinal comparisons.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), first display in (4.3.2)(5), printed p.884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Six.Complement
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
    {geometry : MS93.Geometry R} {p : Counterexample geometry}

/-- The fixed preimage cuts out precisely the common natural edge plane
at any moving neighbor, using only the early contrary facts. -/
theorem moving_natural_inf_fixed_eq_edge (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    {a t d : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (hd : d ∈ movingNeighbors geometry a) :
    U R d ⊓ B R a (geometry.Z_normal a) = edgeDisplacement a t := by
  have hdc := moving_color ha hd
  have he := facts.edge_eq a t d ha hat hdt hd
  have hZ : ⁅Z R d, Q R a⁆ = edgeDisplacement a t :=
    (FirstPairing.StepThree.moving_commutator_eq_edge_at p (by omega)
      initial bad a t d ha hat hdt hd).trans he
  have hQG := Q_le_stabilizer_of_dist_two R a d ha hd.1
  have hUQ : U R d ≤ Q R a :=
    (U_le_Z d).trans ((moving_Z_le_V hd).trans (geometry.V_le_Q hb a ha))
  let s : BinaryNaturalStructure source :=
    ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
  have hU : ⁅U R d, Q R a⁆ = edgeDisplacement a t := by
    have h := commutator_eq_of_centralizing_sup
      ((sup_comm _ _).trans (s.decomposition_at d hdc).symm)
      (inf_le_right.trans (centralizer_le hQG)) (hUQ.trans (Q R a).le_normalizer)
    have h' : ⁅U R d, Q R a⁆ = ⁅Z R d, Q R a⁆ := by
      simpa only [commutator_comm] using h
    exact h'.trans hZ
  let K := U R d ⊓ B R a (geometry.Z_normal a)
  have hKU : K ≤ U R d := inf_le_left
  have hcard := FirstPairing.StepThree.edge_card p (by omega) initial a t ha hat
  have hle : edgeDisplacement a t ≤ K := le_inf
    (he ▸ Initial.edge_le_natural source d t hdc hdt)
    (((Initial.edge_le_natural source a t ha hat).trans (U_le_Z a)).trans
      (EdgeTransfer.Z_le_B hb a ha))
  let : Finite (U R d) := Nat.finite_of_card_ne_zero (by
    rw [modules.natural.card_at d hdc]; decide)
  let : Finite K := Finite.of_injective (inclusion hKU) (inclusion_injective _)
  have hge : 4 ≤ Nat.card K := hcard ▸ card_le_of_le hle
  have hdvd : Nat.card K ∣ 8 := modules.natural.card_at d hdc ▸ card_dvd_of_le hKU
  have hne : Nat.card K ≠ 8 := by
    intro hsize
    have hK : K = U R d := eq_of_le_of_card_ge hKU
      (by rw [hsize, modules.natural.card_at d hdc])
    have hfixed : U R d ≤ B R a (geometry.Z_normal a) :=
      hK ▸ (show K ≤ B R a (geometry.Z_normal a) from inf_le_right)
    have hzero := edge_normal_subgroup_eq_bot source hb modules facts ha hat
      ⁅U R d, Q R a⁆ hU.le
      (FirstPairing.StepThree.fixed_subgroup_commutator_normalized source hb ha hfixed)
    rw [hU] at hzero
    rw [hzero, card_bot] at hcard
    omega
  have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  have hsize : Nat.card K = 4 := by omega
  exact (eq_of_le_of_card_ge hle (by rw [hcard, hsize])).symm

/-- The particular fixed-preimage comparison in the first display of (5). -/
theorem start_natural_inf_middle_fixed (source : LocalSource L R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (path : Selection.SixPath p) :
    U R p.a ⊓ B R path.middle (geometry.Z_normal path.middle) =
      edgeDisplacement path.middle path.first :=
  moving_natural_inf_fixed_eq_edge source (by rw [path.six]; decide) modules initial facts bad
    path.middle_color (adjacent_symm R path.first_middle_adjacent)
    path.start_first_adjacent (path.start_moving source modules)

/-- The actual natural-section triple clause supplies the middle fixed
preimage bound for the radius commutator. -/
theorem radius_commutator_le_middle_fixed (source : LocalSource L R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (path : Selection.SixPath p) :
    ⁅radiusCommutator p.a p.a', Q R path.middle⁆ ≤
      B R path.middle (geometry.Z_normal path.middle) := by
  obtain ⟨ip⟩ := initial p
  obtain ⟨q, hqa, _⟩ := FirstPairing.contrary_at p bad path.middle path.middle_color
  obtain ⟨iq⟩ := initial q
  have s : NaturalSectionAt path.middle (V R path.middle) (Z R path.middle) := by
    simpa only [hqa] using iq.natural_section
  have hb : 2 < geometry.b R := by rw [path.six]; decide
  have hRV := ((Six.radius_le_predecessor_U source hb modules facts p ip).trans
    (U_le_Z p.c)).trans (predecessor_Z_le_middle_V path)
  exact (commutator_mono hRV le_rfl).trans
    (FirstPairing.Orientation.ImageCases.commutator_le_fixed_preimage hb path.middle_color s)

/-- The only remaining part of the initial radius estimate is containment
in the starting natural group. Both the fixed bound and its intersection
with that group have been discharged. -/
theorem radius_bound_of_start_natural_bound (source : LocalSource L R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (path : Selection.SixPath p)
    (hnatural : ⁅radiusCommutator p.a p.a', Q R path.middle⁆ ≤ U R p.a) :
    ⁅radiusCommutator p.a p.a', Q R path.middle⁆ ≤
      edgeDisplacement path.middle path.first := by
  rw [← start_natural_inf_middle_fixed source modules initial facts bad path]
  exact le_inf hnatural (radius_commutator_le_middle_fixed source modules initial facts bad path)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Six.Complement
