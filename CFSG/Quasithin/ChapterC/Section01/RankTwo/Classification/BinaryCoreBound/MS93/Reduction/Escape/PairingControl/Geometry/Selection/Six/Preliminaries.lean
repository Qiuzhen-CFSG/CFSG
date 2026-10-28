module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Factorization.Forward
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.Edges

/-!
# Movement and displacement on the six-step critical path

Forward nonnormality of a critical pair forces its starting Z-layer outside
B at the second vertex. Apply this to the reversed critical pair to discharge
the endpoint movement required by the earlier radius/edge identities. Thus
R₀ lies in the actual U at the distance-two predecessor, and is its last-edge
displacement. The same argument at the start, together with the transported
initial identities and step (3), identifies [Z_alpha,Q_(alpha+2)] with the
middle vertex's first-edge displacement.

For a centralizer-selected path, R₀ ≤ Z_(alpha+2) forces Q_(alpha+2) =
Q_(alpha+4): the first kernel is in the selected edge centralizer, and the
finite kernels have equal order. X = Z then identifies their Z-layers.
These are reductions for the two branches of (5), not its completed proof.
The actual (1.7)(ii) application and the complementary fixed-cover and
predecessor-commutator bounds remain to be established.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (2.2)(iv), pp.856--857, and (4.3.2)(4)--(5), pp.884--885.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

namespace Six
private theorem fixed_neighbor_normal (source : LocalSource L R)
    (hb : 2 < geometry.b R) {a d : Vertex R} (ha : color R a = false)
    (had : (cosetGraph R).dist a d = 2)
    (hfixed : Z R d ≤ B R a (geometry.Z_normal a)) :
    ((Z R d ⊔ Z R a).subgroupOf (stabilizer R a)).Normal := by
  have hV : V R a ≤ stabilizer R a := (geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1)
  apply normal_subgroupOf_of_le_normalizer
  rw [← source.local_generation a ha]
  apply sup_le
  · apply le_normalizer_iff.mpr
    intro l hl x hx
    have hm : (Z R d ⊔ Z R a).map (MulAut.conj l).toMonoidHom ≤ Z R d ⊔ Z R a := by
      rw [Subgroup.map_sup]
      apply sup_le
      · rintro _ ⟨y, hy, rfl⟩
        change l * y * l⁻¹ ∈ Z R d ⊔ Z R a
        have hc := ((mem_B_iff R a _ hV y).mp (hfixed hy)).2 l hl
        rw [show l * y * l⁻¹ = ⁅l, y⁆ * y by simp [commutatorElement_def, mul_assoc]]
        exact (Z R d ⊔ Z R a).mul_mem (mem_sup_right hc) (mem_sup_left hy)
      · rintro _ ⟨y, hy, rfl⟩
        exact mem_sup_right ((Z_normalized R a (Ltilde_le_stabilizer a hl) y).mp hy)
    exact hm (mem_map_of_mem (MulAut.conj l).toMonoidHom hx)
  · exact (le_inf
      ((Q_le_stabilizer_of_dist_two R a d ha had).trans (Z_normalized R d))
      ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans (Z_normalized R a))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- The forward critical product cannot be normal in its second vertex group;
containment in the fixed preimage would give precisely that relative normality. -/
theorem critical_start_moving_at_second (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    {a a' d : Vertex R} (ha : color R a = false) (hd : color R d = false)
    (hcrit : CriticalPair R a a' (geometry.exists_critical a ha))
    (had : (cosetGraph R).dist a d = 2)
    (hpath : (cosetGraph R).dist d a' + 2 = (cosetGraph R).dist a a') :
    a ∈ movingNeighbors geometry d := by
  refine ⟨by rwa [SimpleGraph.dist_comm], ?_⟩
  have hn := (critical_nonnormal_forward R geometry (source.adjacent_centralizer geometry.radical_ne_bot)
    a ha (by rw [geometry.distance_constant a ha]; exact lt_trans (by decide : 0 < 2) hb)
    a' hcrit d had hpath).2
  rw [modules.X_eq_Z d hd] at hn
  exact fun h => hn (fixed_neighbor_normal source hb hd (by rwa [SimpleGraph.dist_comm]) h)

/-- Reversing the critical pair proves endpoint movement without a later
escape theorem or any hypothesis on the reversed radius group. -/
theorem endpoint_moving (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (p : Counterexample geometry) : p.a' ∈ movingNeighbors geometry p.c := by
  apply critical_start_moving_at_second source hb modules p.end_color p.before_color
    (source.critical_reverse geometry p.a p.color_a p.a' p.end_color p.critical)
  · rw [SimpleGraph.dist_comm]
    exact p.before.1
  · simpa only [SimpleGraph.dist_comm] using p.before.2

/-- The endpoint movement premise in the radius-to-natural bound is discharged. -/
theorem radius_le_predecessor_U (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    (ip : InitialFacts p) : radiusCommutator p.a p.a' ≤ U R p.c :=
  radius_le_predecessor_natural source p ip facts (endpoint_moving source hb modules p)

end Six
namespace SixPath
open Six
variable {p : Counterexample geometry} (path : Selection.SixPath p)

/-- The original starting vertex moves the quotient at position two. -/
theorem start_moving (source : LocalSource L R) (modules : ModuleFacts source geometry) :
    p.a ∈ movingNeighbors geometry path.middle := by
  apply critical_start_moving_at_second source (by rw [path.six]; decide) modules
    p.color_a path.middle_color p.critical path.start_middle_distance
  rw [path.middle_before.1, p.distance_eq_b, path.six]

/-- Step (3) reverses that movement, keeping the actual middle vertex. -/
theorem middle_moving (source : LocalSource L R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry) : path.middle ∈ movingNeighbors geometry p.a :=
  facts.moving_symmetric path.middle p.a path.middle_color (start_moving path source modules)

/-- The first complementary-case commutator bound holds as an equality. -/
theorem start_commutator_eq_edge (source : LocalSource L R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) :
    ⁅Z R p.a, Q R path.middle⁆ = edgeDisplacement path.middle path.first := by
  have hmov := start_moving path source modules
  rw [FirstPairing.StepThree.moving_commutator_eq_edge_at p (by rw [path.six]; decide)
    initial bad path.middle path.first p.a path.middle_color
    (adjacent_symm R path.first_middle_adjacent) path.start_first_adjacent hmov]
  exact facts.edge_eq path.middle path.first p.a path.middle_color
    (adjacent_symm R path.first_middle_adjacent) path.start_first_adjacent hmov

/-- R₀ is the actual predecessor-side displacement on the final edge. -/
theorem radius_eq_last_edge (source : LocalSource L R)
    (modules : ModuleFacts source geometry) (facts : ContraryLocalFacts geometry)
    (ip : InitialFacts p) : radiusCommutator p.a p.a' = edgeDisplacement p.c path.last :=
  radius_eq_predecessor_edge p ip facts
    (endpoint_moving source (by rw [path.six]; decide) modules p) path.last_before

/-- The contained case and the selected relative centralizer identify the
two kernels by containment and equality of their finite orders. -/
theorem middle_kernel_eq_predecessor (source : LocalSource L R)
    (choice : CentralizerChoice p)
    (hcontained : radiusCommutator p.a p.a' ≤ Z R path.middle) :
    Q R path.middle = Q R p.c := by
  have hadj := path.middle_choice_adjacent choice
  have ht : color R choice.t = true := by
    have hn := adjacent_color_ne R hadj
    cases h : color R choice.t <;> simp_all [path.middle_color]
  have hle : Q R path.middle ≤ Q R p.c := by
    rw [← choice.centralizer_eq]
    refine le_inf (Q_le_adjacent_h R ht hadj) ?_
    exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes path.middle path.middle_color))).trans (centralizer_le hcontained)
  let := finite_stabilizer R p.c
  let : Finite (Q R p.c) := Finite.of_injective
    (inclusion (show Q R p.c ≤ stabilizer R p.c from fun _ hx => hx.1))
    (inclusion_injective _)
  exact eq_of_le_of_card_ge hle (by
    rw [source.Q_card path.middle path.middle_color, source.Q_card p.c p.before_color])

/-- X = Z transfers the kernel equality to the actual Z-layers. -/
theorem middle_Z_eq_predecessor (source : LocalSource L R)
    (modules : ModuleFacts source geometry) (choice : CentralizerChoice p)
    (hcontained : radiusCommutator p.a p.a' ≤ Z R path.middle) :
    Z R path.middle = Z R p.c := by
  rw [← modules.X_eq_Z path.middle path.middle_color, ← modules.X_eq_Z p.c p.before_color]
  change omegaCenter (Q R path.middle) = omegaCenter (Q R p.c)
  rw [middle_kernel_eq_predecessor path source choice hcontained]

/-- The complementary contradiction now requires only the fixed cover and
the predecessor bound; the starting commutator premise has been proved. -/
theorem false_of_cover_and_predecessor_bound (source : LocalSource L R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hcover : Z R p.a ≤ Z R p.c ⊔ B R path.middle (geometry.Z_normal path.middle))
    (hpredecessor : ⁅Z R p.c, Q R path.middle⁆ ≤ edgeDisplacement path.middle path.first) :
    False :=
  path.false_of_fixed_cover source modules facts hcover
    (path.start_commutator_eq_edge source modules initial facts bad).le hpredecessor

end SixPath
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection
