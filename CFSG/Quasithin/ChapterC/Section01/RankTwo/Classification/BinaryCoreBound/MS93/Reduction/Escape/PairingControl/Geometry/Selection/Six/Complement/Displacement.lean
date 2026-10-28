module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Six.Preliminaries
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.Consequences

/-!
# Displacement reductions in the complementary six-step case

The radius group is an elementary subgroup of the predecessor natural
eight-group. Outside Z at the middle vertex, it has a nontrivial middle
kernel commutator. If this commutator lies in the first middle displacement,
the radius cannot lie in the middle fixed preimage: otherwise its commutator
would be a normal subgroup of a proper natural subspace.

Consequently the predecessor moves at the middle vertex. Its natural
eight-group has a central commutator plane of order four. Every noncentral
subgroup supplements that plane, so the radius has the whole same
commutator plane. This identifies the two middle displacements and proves
the predecessor bound, conditional only on the initial radius bound.

The initial radius bound and the opposite-module fixed-cover comparison
are separate obligations. No completion of the complementary case is
asserted here.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.3.2)(5), printed pp.884--885.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Six.Complement

private theorem commutator_eq_of_eight_four {G : Type*} [Group G]
    (U Q A : Subgroup G) [Finite U]
    (hUQ : U ≤ Q) (hAU : A ≤ U)
    (hU : Nat.card U = 8) (hD : Nat.card (⁅U, Q⁆ : Subgroup G) = 4)
    (hDU : ⁅U, Q⁆ ≤ U) (hcentral : ⁅U, Q⁆ ≤ centralizer (Q : Set G))
    (hne : ⁅A, Q⁆ ≠ ⊥) : ⁅A, Q⁆ = ⁅U, Q⁆ := by
  let D := ⁅U, Q⁆
  let K := D ⊔ A
  have hKU : K ≤ U := sup_le hDU hAU
  let : Finite K := Finite.of_injective (inclusion hKU) (inclusion_injective _)
  have hge : 4 ≤ Nat.card K := hD ▸ card_le_of_le (show D ≤ K from le_sup_left)
  have hdvd : Nat.card K ∣ 8 := hU ▸ card_dvd_of_le hKU
  have hnefour : Nat.card K ≠ 4 := by
    intro hfour
    have heq : D = K := eq_of_le_of_card_ge le_sup_left (by rw [hfour, hD])
    have hAD : A ≤ D := heq.symm ▸ (show A ≤ K from le_sup_right)
    exact hne (commutator_eq_bot_iff_le_centralizer.mpr (hAD.trans hcentral))
  have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  have hsize : Nat.card K = 8 := by omega
  have hK : K = U := eq_of_le_of_card_ge hKU (by rw [hsize, hU])
  have h := commutator_eq_of_centralizing_sup (show D ⊔ A = U from hK)
    hcentral ((hAU.trans hUQ).trans Q.le_normalizer)
  simpa only [commutator_comm] using h

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
    {geometry : MS93.Geometry R} {p : Counterexample geometry}

omit [Finite M] in
/-- The original predecessor Z-layer is in the radius layer at position two. -/
theorem predecessor_Z_le_middle_V (path : Selection.SixPath p) :
    Z R p.c ≤ V R path.middle := by
  apply le_iSup_of_le p.c
  apply le_iSup_of_le
    (show (cosetGraph R).dist p.c path.middle ≤ 2 by
      rw [SimpleGraph.dist_comm, path.middle_predecessor_distance])
  exact le_rfl

/-- Noncontainment in Z means a nonzero actual kernel commutator; the
involution condition comes from the predecessor natural group. -/
theorem radius_commutator_ne_bot (source : LocalSource L R)
    (modules : ModuleFacts source geometry) (facts : ContraryLocalFacts geometry)
    (ip : InitialFacts p) (path : Selection.SixPath p)
    (hout : ¬ radiusCommutator p.a p.a' ≤ Z R path.middle) :
    ⁅radiusCommutator p.a p.a', Q R path.middle⁆ ≠ ⊥ := by
  intro hzero
  apply hout
  rw [← modules.X_eq_Z path.middle path.middle_color]
  have hRU := Six.radius_le_predecessor_U source (by rw [path.six]; decide) modules facts p ip
  have hRQ := (hRU.trans (U_le_Z p.c)).trans
    ((predecessor_Z_le_middle_V path).trans
      (geometry.V_le_Q (by rw [path.six]; decide) path.middle path.middle_color))
  let := geometry.U_elementary (by rw [path.six]; decide) p.c p.before_color
  intro x hx
  exact mem_omegaCenter_iff.mpr ⟨hRQ hx,
    elemPow_eq_one_of_isElementaryAbelian x (hRU hx),
    commutator_eq_bot_iff_le_centralizer.mp hzero hx⟩

/-- The source's initial displacement bound excludes the fixed preimage,
using its actual residual normalization, rather than an order comparison alone. -/
theorem radius_not_le_middle_fixed_of_bound (source : LocalSource L R)
    (modules : ModuleFacts source geometry) (facts : ContraryLocalFacts geometry)
    (ip : InitialFacts p) (path : Selection.SixPath p)
    (hout : ¬ radiusCommutator p.a p.a' ≤ Z R path.middle)
    (hbound : ⁅radiusCommutator p.a p.a', Q R path.middle⁆ ≤
      edgeDisplacement path.middle path.first) :
    ¬ radiusCommutator p.a p.a' ≤ B R path.middle (geometry.Z_normal path.middle) := by
  intro hfixed
  exact radius_commutator_ne_bot source modules facts ip path hout
    (edge_normal_subgroup_eq_bot source (by rw [path.six]; decide) modules facts
      path.middle_color (adjacent_symm R path.first_middle_adjacent) _ hbound
      (FirstPairing.StepThree.fixed_subgroup_commutator_normalized source
        (by rw [path.six]; decide) path.middle_color hfixed))

/-- The missing initial bound also proves predecessor movement; it is not
an extra hypothesis supplied to the source branch. -/
theorem predecessor_moving_of_bound (source : LocalSource L R)
    (modules : ModuleFacts source geometry) (facts : ContraryLocalFacts geometry)
    (ip : InitialFacts p) (path : Selection.SixPath p)
    (hout : ¬ radiusCommutator p.a p.a' ≤ Z R path.middle)
    (hbound : ⁅radiusCommutator p.a p.a', Q R path.middle⁆ ≤
      edgeDisplacement path.middle path.first) :
    p.c ∈ movingNeighbors geometry path.middle := by
  refine ⟨path.middle_predecessor_distance, ?_⟩
  intro hfixed
  apply radius_not_le_middle_fixed_of_bound source modules facts ip path hout hbound
  exact ((Six.radius_le_predecessor_U source (by rw [path.six]; decide)
    modules facts p ip).trans (U_le_Z p.c)).trans hfixed

/-- Remove the globally fixed summand of Z at the predecessor. -/
theorem predecessor_natural_commutator (source : LocalSource L R)
    (modules : ModuleFacts source geometry) (path : Selection.SixPath p) :
    ⁅U R p.c, Q R path.middle⁆ = ⁅Z R p.c, Q R path.middle⁆ := by
  let s : BinaryNaturalStructure source :=
    ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
  have hQG := Q_le_stabilizer_of_dist_two R path.middle p.c path.middle_color
    path.middle_predecessor_distance
  have hUQ : U R p.c ≤ Q R path.middle :=
    (U_le_Z p.c).trans ((Z_le_VBall R p.c 2).trans path.predecessor_V_le_middle_kernel)
  have h := commutator_eq_of_centralizing_sup
    ((sup_comm _ _).trans (s.decomposition_at p.c p.before_color).symm)
    (inf_le_right.trans (centralizer_le hQG)) (hUQ.trans (Q R path.middle).le_normalizer)
  simpa only [commutator_comm] using h

/-- In the complementary case the initial bound forces the full source
identity, including the displacement toward the selected position-three vertex. -/
theorem radius_commutator_eq_edges_of_bound (source : LocalSource L R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (choice : CentralizerChoice p) (path : Selection.SixPath p)
    (hout : ¬ radiusCommutator p.a p.a' ≤ Z R path.middle)
    (hbound : ⁅radiusCommutator p.a p.a', Q R path.middle⁆ ≤
      edgeDisplacement path.middle path.first) :
    ⁅radiusCommutator p.a p.a', Q R path.middle⁆ = edgeDisplacement path.middle choice.t ∧
      edgeDisplacement path.middle choice.t = edgeDisplacement path.middle path.first := by
  obtain ⟨ip⟩ := initial p
  have hb : 2 < geometry.b R := by rw [path.six]; decide
  have hmov := predecessor_moving_of_bound source modules facts ip path hout hbound
  have hadj := path.middle_choice_adjacent choice
  have hcadj := adjacent_symm R (SixPath.choice_predecessor_adjacent choice)
  have hZ : ⁅Z R p.c, Q R path.middle⁆ = edgeDisplacement path.middle choice.t := by
    rw [FirstPairing.StepThree.moving_commutator_eq_edge_at p (by omega) initial bad
      path.middle choice.t p.c path.middle_color hadj hcadj hmov]
    exact facts.edge_eq path.middle choice.t p.c path.middle_color hadj hcadj hmov
  have hU := (predecessor_natural_commutator source modules path).trans hZ
  have hcentral : ⁅U R p.c, Q R path.middle⁆ ≤
      centralizer (Q R path.middle : Set (FreeAmalgam R)) := by
    rw [hU]
    exact ((Initial.edge_le_natural source _ _ path.middle_color hadj).trans
      (U_le_Z path.middle)).trans
        (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes _ path.middle_color))
  have hcard := FirstPairing.StepThree.edge_card p (by omega) initial
    path.middle choice.t path.middle_color hadj
  let : Finite (U R p.c) := Nat.finite_of_card_ne_zero (by
    rw [modules.natural.card_at p.c p.before_color]; decide)
  have hRU := Six.radius_le_predecessor_U source hb modules facts p ip
  have heq : ⁅radiusCommutator p.a p.a', Q R path.middle⁆ =
      edgeDisplacement path.middle choice.t := by
    rw [← hU]
    apply commutator_eq_of_eight_four _ _ _
      ((U_le_Z p.c).trans ((Z_le_VBall R p.c 2).trans path.predecessor_V_le_middle_kernel))
      hRU (modules.natural.card_at p.c p.before_color)
    · rwa [hU]
    · exact le_normalizer_iff_commutator_le_left.mp
        ((Q_le_stabilizer_of_dist_two R path.middle p.c path.middle_color
          path.middle_predecessor_distance).trans (U_normalized p.c))
    · exact hcentral
    · exact radius_commutator_ne_bot source modules facts ip path hout
  refine ⟨heq, ?_⟩
  have hedgeU := Initial.edge_le_natural source path.middle path.first path.middle_color
    (adjacent_symm R path.first_middle_adjacent)
  let : Finite (U R path.middle) := Nat.finite_of_card_ne_zero (by
    rw [modules.natural.card_at path.middle path.middle_color]; decide)
  let : Finite (edgeDisplacement path.middle path.first) :=
    Finite.of_injective (inclusion hedgeU) (inclusion_injective _)
  apply eq_of_le_of_card_ge (heq ▸ hbound)
  rw [hcard, FirstPairing.StepThree.edge_card p (by omega) initial
    path.middle path.first path.middle_color (adjacent_symm R path.first_middle_adjacent)]

/-- The predecessor containment follows from the initial radius bound,
without a separate predecessor commutator or movement premise. -/
theorem predecessor_bound_of_radius_bound (source : LocalSource L R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (choice : CentralizerChoice p) (path : Selection.SixPath p)
    (hout : ¬ radiusCommutator p.a p.a' ≤ Z R path.middle)
    (hbound : ⁅radiusCommutator p.a p.a', Q R path.middle⁆ ≤
      edgeDisplacement path.middle path.first) :
    ⁅Z R p.c, Q R path.middle⁆ ≤ edgeDisplacement path.middle path.first := by
  obtain ⟨ip⟩ := initial p
  have hmov := predecessor_moving_of_bound source modules facts ip path hout hbound
  have hadj := path.middle_choice_adjacent choice
  have hcadj := adjacent_symm R (SixPath.choice_predecessor_adjacent choice)
  rw [FirstPairing.StepThree.moving_commutator_eq_edge_at p
    (by rw [path.six]; decide) initial bad
    path.middle choice.t p.c path.middle_color hadj hcadj hmov,
    facts.edge_eq path.middle choice.t p.c path.middle_color hadj hcadj hmov,
    (radius_commutator_eq_edges_of_bound source modules initial facts bad choice path hout hbound).2]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Six.Complement
