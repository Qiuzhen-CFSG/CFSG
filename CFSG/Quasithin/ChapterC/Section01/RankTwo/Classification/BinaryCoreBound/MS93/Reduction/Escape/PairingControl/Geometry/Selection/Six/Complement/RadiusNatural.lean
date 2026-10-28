module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Six.Complement.FixedPreimage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Continuation.DualQuadratic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.ImageCases.Representation.Kernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.DualGeometry.Transport

/-!
# The starting natural-group bound for the six-step radius commutator

The critical endpoint acts faithfully on the actual opposite section
Vcirc_alpha/U_alpha. Its commutator on Vcirc_alpha therefore escapes U_alpha.
It also contains [Z_alpha,Z_alpha'], of order two: the central summand in
Z_alpha contributes no displacement. Since the full radius commutator has
order four, it equals [Vcirc_alpha,Z_alpha'].

At distance six, Z_alpha' lies in Q at the middle vertex. The common edge
plane makes that kernel quadratic on U_alpha; the checked dual-coordinate
argument makes it quadratic on Vcirc_alpha/U_alpha. The preceding equality
therefore puts [R₀,Q_middle] in U_alpha. Combining this with the existing
fixed-preimage calculation proves the first displayed edge bound in (5).
Neither the centralizer choice nor the complementary noncontainment is needed.

Only the early-input quadratic lemma from LocalProducts.Continuation is
used; no later local-control or propagation conclusion enters this argument.
The fixed-cover comparison and complementary-branch assembly remain separate.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.3.1)(i)--(iii), (4.3.2)(3), and the first display in (4.3.2)(5),
printed pp.882--884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Six.Complement
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
    {geometry : MS93.Geometry R} {p : Counterexample geometry}

private theorem endpoint_moving_commutator_not_le_natural (source : LocalSource L R)
    (hb : 2 < geometry.b R) (facts : ContraryLocalFacts geometry) :
    ¬ ⁅Vcirc R p.a, Z R p.a'⁆ ≤ U R p.a := by
  intro h
  obtain ⟨o⟩ := facts.opposite p.a p.color_a
  let S := stabilizer R p.a
  have hC : Vcirc R p.a ≤ S := (Vcirc_le_V p.a).trans
    ((geometry.V_le_Q hb p.a p.color_a).trans (fun _ hx => hx.1))
  have hJ : Z R p.a' ≤ S := p.end_Z_le_start_stabilizer
  have hc : ⁅(Z R p.a').subgroupOf S, (Vcirc R p.a).subgroupOf S⁆ ≤
      (U R p.a).subgroupOf S := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator, map_subgroupOf_eq_of_le hC, map_subgroupOf_eq_of_le hJ,
      commutator_comm]
    exact h
  have hk := FirstPairing.Orientation.ImageCases.natural_actor_le_kernel
    o.dual.graphNatural ((Z R p.a').subgroupOf S) hc
  rw [o.kernel] at hk
  apply (source.critical_reverse geometry p.a p.color_a p.a' p.end_color p.critical).2
  intro x hx
  exact hk (show (⟨x, hJ hx⟩ : S) ∈ (Z R p.a').subgroupOf S from hx)

/-- The endpoint displacement already comes from the moving subgroup.
Faithfulness on its actual dual quotient and the critical two-group exhaust
the radius group of order four. -/
theorem radius_eq_moving_commutator (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry) (ip : InitialFacts p) :
    radiusCommutator p.a p.a' = ⁅Vcirc R p.a, Z R p.a'⁆ := by
  let K := ⁅Vcirc R p.a, Z R p.a'⁆
  let C := criticalCommutator p.a p.a'
  have hK : K ≤ radiusCommutator p.a p.a' := commutator_mono (Vcirc_le_V p.a) le_rfl
  have hU : U R p.a ≤ Vcirc R p.a := commutator_mono (Z_le_VBall R p.a 2) le_rfl
  let natural : BinaryNaturalStructure source :=
    ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
  have hlocal : U R p.a ≤ stabilizer R p.a' :=
    ((U_le_Z p.a).trans (Z_le_VBall R p.a 2)).trans
      (p.trapped.trans (Q_le_stabilizer_of_dist_two R p.c p.a' p.before_color p.before.1))
  have hZU : C = ⁅U R p.a, Z R p.a'⁆ := by
    have h := commutator_eq_of_centralizing_sup
      ((sup_comm _ _).trans (natural.decomposition_at p.a p.color_a).symm)
      (inf_le_right.trans (centralizer_le p.end_Z_le_start_stabilizer))
      (hlocal.trans (Z_normalized R p.a'))
    simpa only [commutator_comm, C, criticalCommutator] using h.symm
  have hCK : C ≤ K := hZU ▸ commutator_mono hU le_rfl
  have hCU : C ≤ U R p.a :=
    (commutator_mono le_rfl p.end_Z_le_start_stabilizer).trans
      (Initial.Z_commutator_stabilizer source p.a p.color_a).le
  let : Finite (radiusCommutator p.a p.a') := p.radius_finite
  let : Finite K := Finite.of_injective (inclusion hK) (inclusion_injective _)
  have hc : Nat.card C = 2 := ip.critical_card
  have hge : 2 ≤ Nat.card K := hc ▸ card_le_of_le hCK
  have hne : Nat.card K ≠ 2 := by
    intro htwo
    have he : C = K := eq_of_le_of_card_ge hCK (by rw [hc, htwo])
    exact endpoint_moving_commutator_not_le_natural source hb facts (he ▸ hCU)
  have hdvd : Nat.card K ∣ 4 := ip.radius_card ▸ card_dvd_of_le hK
  have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 4 ≠ 0)⟩
  rw [show Nat.divisors 4 = ({1, 2, 4} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  have hsize : Nat.card K = 4 := by omega
  exact (eq_of_le_of_card_ge hK (by rw [hsize, ip.radius_card])).symm

/-- The natural-group containment in the first display of (4.3.2)(5),
valid before the contained/complementary split. -/
theorem radius_commutator_le_start_natural (source : LocalSource L R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (path : Selection.SixPath p) :
    ⁅radiusCommutator p.a p.a', Q R path.middle⁆ ≤ U R p.a := by
  obtain ⟨ip⟩ := initial p
  have hb : 2 < geometry.b R := by rw [path.six]; decide
  have hend : Z R p.a' ≤ Q R path.middle := by
    apply Z_le_Q_of_dist_lt R p.a' (geometry.exists_critical p.a' p.end_color)
    rw [geometry.distance_constant p.a' p.end_color, SimpleGraph.dist_comm,
      path.middle_before.1]
    change 4 < geometry.b R
    rw [path.six]
    decide
  rw [radius_eq_moving_commutator source hb modules facts ip]
  exact (commutator_mono (commutator_mono le_rfl hend) le_rfl).trans
    (LocalProducts.Continuation.moving_triple_le_natural hb facts p initial bad
      path.middle_color (adjacent_symm R path.first_middle_adjacent)
      path.start_first_adjacent (path.start_moving source modules))

/-- The complete first display bound, combining natural containment with
the already proved middle fixed-preimage and intersection comparisons. -/
theorem radius_commutator_le_first_edge (source : LocalSource L R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (path : Selection.SixPath p) :
    ⁅radiusCommutator p.a p.a', Q R path.middle⁆ ≤
      edgeDisplacement path.middle path.first :=
  radius_bound_of_start_natural_bound source modules initial facts bad path
    (radius_commutator_le_start_natural source modules initial facts bad path)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Six.Complement
