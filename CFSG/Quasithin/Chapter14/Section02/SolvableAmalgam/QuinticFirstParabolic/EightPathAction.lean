module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.CentralKernel
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.EightPathAction.Inputs
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.EightPathAction.EvenActors
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.EightPathAction.OddEscape
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.EightPathAction.KernelIntersections
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.EightPathAction.SecondKernel
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.EightPathAction.CorePairing
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.EightPathAction.MiddleLayers
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.EightPathAction.SecondKernelSeparation
public import Theory.GroupAction.RankTwoCosetGeometry.FourPathCore
public import Theory.GroupAction.RankTwoCosetGeometry.FourPathMiddleKernel
public import Theory.GroupAction.RankTwoCosetGeometry.QuinticShortPaths
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.RootedExtensions
public import Theory.GroupAction.RankTwoCosetGeometry.ExtensionActors
public import Theory.GroupAction.RankTwoCosetGeometry.QuinticFivePathEscape

/-!
# Initial path transitivity and the remaining quintic extension actors

For the literal source graph, false is X=YT and true is H. The cubic
quotient and common Sylow prove transitivity on two-edge paths rooted at H.
Two explicit families of local actors then suffice for eight-edge transitivity:
local order-four images at even lengths, and cubic kernel escape at odd lengths.
The fixed-root induction never asks for eight-path transitivity at X.

The first even actor is proved in the Sz(2) quotient case and gives
three-edge transitivity. The first odd escape is now unconditional and
extends that Sz(2) action to four edges. The four-path kernel intersection
has order |T|/16. The imported kernel analysis identifies the four- and
six-path fixers and generates the crossing core using two moved conjugates.
The second-ball kernel is the centralizer of the elementary neighbor span;
its order bound gives at least four cosets of each four-path fixer modulo
their intersection, at any quintic vertex. Binary commutator duality now
makes the core action elementary of order sixteen or thirty-two. Thus the
middle second-ball kernel is normal of index four or eight in every
four-path fixer. The fixer itself is normal of index four in the middle
first-ball kernel; its quotient by the second kernel is elementary abelian
of order four or eight. These are literal kernels in the source graph.
The original span centralizer has exactly T as its normalizer in the cubic
parabolic, separating second-ball kernels at distinct quintic neighbors.
The length-five odd extension is proved using this separation: failed
escape would identify two such kernels. Counting four-path fixers first
shows that transitivity at any length at least four already forces the
Suzuki row, so the five-to-six extension has only the preceding path
transitivity as its induction premise.

The even actors at lengths four and six, the odd escape at length seven,
and the unconditional D₁₀ exclusion remain source obligations of
qt-e-quintic-sylow-lower. This module does not assert the unconditional
`source_quintic_eight_path_transitive`. The actor-family induction below
retains their literal consumer without an endpoint model, presentation,
enumeration or Sylow-order assumption.

Source: Aschbacher--Smith F.1.11--12, pp.262--264; F.3.3--4, p.270;
F.4.6(2), p.276 (root convention only); F.7.10--11, pp.313--314;
and 14.2.20--21, pp.988--989.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.Section07 SimpleGraph SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry.RankTwo Theory.GroupAction.CubicTree
variable {G : Type*} [Group G] [Finite G]

/-- The original quintic root is transitive on its ten two-edge paths.
Both index-five quotient alternatives are retained in the source inputs. -/
theorem source_quintic_two_path_transitive
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    RootPathTransitive (Geometry.graph X H) (X ⊔ H : Subgroup G)
      (Geometry.base X H true) 2 := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L := X ⊔ H
  let F := Geometry.family X H
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hTL : (T : Subgroup G) ≤ L := hTX.trans le_sup_left
  let SL := T.subtype hTL
  have hSA : (SL : Subgroup L) ≤ F false := fun x hx => hTX hx
  let S := SL.subtype hSA
  obtain ⟨hthree, hfive, hmap⟩ := source_quintic_graph_indices
    hG T hempty hM hu hmany hcard e H hH hi
  have hS : (S : Subgroup (F false)).map (F false).subtype = F false ⊓ F true := by
    apply map_injective L.subtype_injective
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hSA]
    change ((T.subtype hTL : Sylow 2 L) : Subgroup L).map L.subtype = _
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTL, hmap]
  obtain ⟨_, ⟨eX⟩⟩ := source_residualSylow_quotient hG T hempty hM hu hmany hcard e
  let eA : F false ≃* X := subgroupOfEquivOfLe (show X ≤ L from le_sup_left)
  let qA : (F false ⧸ pCore 2 (F false)) ≃* Equiv.Perm (Fin 3) :=
    (QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).trans eX
  exact quintic_two_path_transitive F S hS qA hthree hfive


/-- The first local four-cycle extends the original two-path action to three.
The Suzuki quotient is retained explicitly until the dihedral branch is excluded. -/
theorem source_quintic_three_path_transitive_of_suzuki
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (eH : (H ⧸ pCore 2 H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    RootPathTransitive (Geometry.graph X H) (X ⊔ H : Subgroup G)
      (Geometry.base X H true) 3 := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let F := Geometry.family X H
  have htwo := source_quintic_two_path_transitive hG T hempty hM hu hmany hcard e H hH hi
  have hact : GraphAction (Geometry.graph X H) (X ⊔ H : Subgroup G) :=
    ⟨fun g _ _ h => (Subgroup.CosetGeometry.translationGraphIso F g).toHom.map_adj h⟩
  obtain ⟨hthree, hfive, _⟩ := source_quintic_graph_indices
    hG T hempty hM hu hmany hcard e H hH hi
  have hindices (i : Bool) : ((F (!i)).subgroupOf (F i)).index = (if i then 5 else 3) := by
    cases i
    · exact hthree
    · exact hfive
  have hdegree := card_neighbors_of_indices F (fun i => if i then 5 else 3) hindices
  apply htwo.succ_of_rightRegular hact
  intro p hp
  obtain ⟨a, ha, hfour, hsquare⟩ := source_quintic_two_path_extension_actor
    hG T hempty hM hu hmany hcard e H hH hi eH p hp
  have he := (even_walk_iff F p.toWalk).mp (by
    simpa only [BasedWalk.length_toWalk] using (show Even 2 by decide))
  have hc : Nat.card ((graph F).neighborSet p.endpoint) = 5 := by
    rw [hdegree, ←he]
    rfl
  exact rightRegular_of_quintic_kernel_actor F p hc a ha hfour hsquare

/-- The cubic kernel escape extends the original three-path action to four.
The Suzuki quotient is retained explicitly until the dihedral branch is excluded. -/
theorem source_quintic_four_path_transitive_of_suzuki
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (eH : (H ⧸ pCore 2 H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    RootPathTransitive (Geometry.graph X H) (X ⊔ H : Subgroup G)
      (Geometry.base X H true) 4 := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let F := Geometry.family X H
  have hthreePaths := source_quintic_three_path_transitive_of_suzuki
    hG T hempty hM hu hmany hcard e H hH hi eH
  have hact : GraphAction (Geometry.graph X H) (X ⊔ H : Subgroup G) :=
    ⟨fun g _ _ h => (Subgroup.CosetGeometry.translationGraphIso F g).toHom.map_adj h⟩
  obtain ⟨hthree, hfive, _⟩ := source_quintic_graph_indices
    hG T hempty hM hu hmany hcard e H hH hi
  have hindices (i : Bool) : ((F (!i)).subgroupOf (F i)).index = (if i then 5 else 3) := by
    cases i
    · exact hthree
    · exact hfive
  have hdegree := card_neighbors_of_indices F (fun i => if i then 5 else 3) hindices
  apply hthreePaths.succ_of_rightRegular hact
  intro p hp
  have hescape := source_quintic_three_path_kernel_escape
    hG T hempty hM hu hmany hcard e H hH hi p hp
  have he := (even_walk_iff F p.toWalk)
  have htype : p.endpoint.type = false := by
    have hne : (base F true).type ≠ p.endpoint.type := by
      intro heq
      have hh := he.mpr heq
      simp only [BasedWalk.length_toWalk] at hh
      exact (by decide : ¬ Even 3) hh
    change true ≠ p.endpoint.type at hne
    cases ht : p.endpoint.type <;> simp_all
  have hc : Nat.card ((graph F).neighborSet p.endpoint) = 3 := by
    rw [hdegree, htype]
    rfl
  exact rightRegular_of_cubic_kernel_escape F p hc hescape

/-- Exact order of the intersection in the next even extension step. -/
theorem source_quintic_four_path_kernel_intersection_card
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (eH : (H ⧸ pCore 2 H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let F := Geometry.family X H
    ∀ p : BasedWalk (graph F) 4 (base F true), p.Nonbacktracking →
      16 * Nat.card (ballKernel F (p.1 : Vertex F) 1 ⊓ ballKernel F (p.2.2.1 : Vertex F) 1 : Subgroup (X ⊔ H : Subgroup G)) = Nat.card (T : Subgroup G) := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let F := Geometry.family X H
  obtain ⟨hthree,hfive,_⟩ := source_quintic_graph_indices
    hG T hempty hM hu hmany hcard e H hH hi
  have hi' (i : Bool) : ((F (!i)).subgroupOf (F i)).index = (if i then 5 else 3) := by
    cases i
    · exact hthree
    · exact hfive
  have hdegree := card_neighbors_of_indices F (fun i => if i then 5 else 3) hi'
  have (v : Vertex F) : Finite ((graph F).neighborSet v) :=
    Nat.finite_of_card_ne_zero (by rw [hdegree]; cases v.type <;> decide)
  have hflip {a b : Vertex F} (hab : (graph F).Adj a b) : b.type = !a.type := by
    have hh := hab.1
    cases ha : a.type <;> cases hb : b.type <;> simp_all
  have hcount : Nat.card {p : BasedWalk (graph F) 4 (base F true) // p.Nonbacktracking} = 80 :=
    BasedWalk.card_nonbacktracking_succ (graph F)
      (fun v : Vertex F => v.type) (fun i => if i then 5 else 3) hflip hdegree 3 (base F true)
  change ∀ p : BasedWalk (graph F) 4 (base F true), p.Nonbacktracking →
    16 * Nat.card (ballKernel F (p.1 : Vertex F) 1 ⊓ ballKernel F (p.2.2.1 : Vertex F) 1 : Subgroup (X ⊔ H : Subgroup G)) = Nat.card (T : Subgroup G)
  intro p hp
  have ht := source_quintic_four_path_transitive_of_suzuki hG T hempty hM hu hmany hcard e H hH hi eH
  have hc := card_paths_mul_card_fixer F ht p hp
  rw [hcount,stabilizer,Subgroup.CosetGeometry.stabilizer_base,
    source_quintic_four_path_fixer hG T hempty hM hu hmany hcard e H hH hi p hp] at hc
  have hHcard : Nat.card (F true) = Nat.card H :=
    Nat.card_congr (subgroupOfEquivOfLe (show H ≤ X ⊔ H from le_sup_right)).toEquiv
  rw [hHcard] at hc
  change 80 * Nat.card (ballKernel F (p.1 : Vertex F) 1 ⊓
    ballKernel F (p.2.2.1 : Vertex F) 1 : Subgroup (X ⊔ H : Subgroup G)) = Nat.card H at hc
  have hT := ((T : Subgroup G).subgroupOf H).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hH.1.1.2).toEquiv] at hT
  change (T : Subgroup G).relIndex H * Nat.card (T : Subgroup G) = Nat.card H at hT
  rw [hi] at hT
  omega


/-- The four-path fixer has at least four cosets modulo its intersection
with the second-ball kernel at any quintic vertex, including its endpoint. -/
theorem source_quintic_four_path_second_kernel_index
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (eH : (H ⧸ pCore 2 H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let F := Geometry.family X H
    ∀ p : BasedWalk (graph F) 4 (base F true), p.Nonbacktracking →
      ∀ v : Vertex F, v.type = true →
        4 ≤ (pathStabilizer F p ⊓ ballKernel F v 2).relIndex (pathStabilizer F p) := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let F := Geometry.family X H
  change ∀ p : BasedWalk (graph F) 4 (base F true), p.Nonbacktracking →
    ∀ v : Vertex F, v.type = true →
      4 ≤ (pathStabilizer F p ⊓ ballKernel F v 2).relIndex (pathStabilizer F p)
  intro p hp v hv
  have hP : 16 * Nat.card (pathStabilizer F p) = Nat.card (T : Subgroup G) := by
    rw [source_quintic_four_path_fixer hG T hempty hM hu hmany hcard e H hH hi p hp]
    exact source_quintic_four_path_kernel_intersection_card
      hG T hempty hM hu hmany hcard e H hH hi eH p hp
  have hC := source_quintic_second_ball_kernel_card_of_suzuki
    hG T hempty hM hu hmany hcard e H hH hi eH v hv
  let P := pathStabilizer F p
  let C := ballKernel F v 2
  have hPC : Nat.card (P ⊓ C : Subgroup (X ⊔ H : Subgroup G)) ≤ Nat.card C :=
    card_le_of_le inf_le_right
  have hidx := ((P ⊓ C).subgroupOf P).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe
    (show P ⊓ C ≤ P from inf_le_left)).toEquiv] at hidx
  change (P ⊓ C).relIndex P * Nat.card (P ⊓ C : Subgroup (X ⊔ H : Subgroup G)) = Nat.card P at hidx
  have hpos : 0 < Nat.card (P ⊓ C : Subgroup (X ⊔ H : Subgroup G)) := Nat.card_pos
  change 4 ≤ (P ⊓ C).relIndex P
  change 64 * Nat.card C ≤ Nat.card (T : Subgroup G) at hC
  change 16 * Nat.card P = Nat.card (T : Subgroup G) at hP
  nlinarith

/-- In particular the four-path fixer escapes the second-ball kernel at
its own quintic endpoint. This does not assert escape at radius one. -/
theorem source_quintic_four_path_second_kernel_escape
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (eH : (H ⧸ pCore 2 H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let F := Geometry.family X H
    ∀ p : BasedWalk (graph F) 4 (base F true), p.Nonbacktracking →
      ¬ pathStabilizer F p ≤ ballKernel F p.endpoint 2 := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let F := Geometry.family X H
  change ∀ p : BasedWalk (graph F) 4 (base F true), p.Nonbacktracking →
    ¬ pathStabilizer F p ≤ ballKernel F p.endpoint 2
  intro p hp hle
  have ht : p.endpoint.type = true := by
    have hh := (even_walk_iff F p.toWalk).mp (by
      simp only [BasedWalk.length_toWalk]; decide)
    exact hh.symm
  have hh := source_quintic_four_path_second_kernel_index
    hG T hempty hM hu hmany hcard e H hH hi eH p hp p.endpoint ht
  rw [inf_eq_left.mpr hle,relIndex_self] at hh
  omega


/-- The middle second-ball kernel is normal in a four-path fixer and has index four or eight. -/
theorem source_quintic_four_path_middle_kernel
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (eH : (H ⧸ pCore 2 H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let F := Geometry.family X H
    ∀ p : BasedWalk (graph F) 4 (base F true), p.Nonbacktracking →
      let C := ballKernel F (p.2.1 : Vertex F) 2
      C ≤ pathStabilizer F p ∧
      (C.subgroupOf (pathStabilizer F p)).Normal ∧
      (C.relIndex (pathStabilizer F p) = 4 ∨ C.relIndex (pathStabilizer F p) = 8) := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let F := Geometry.family X H
  change ∀ p : BasedWalk (graph F) 4 (base F true), p.Nonbacktracking → _
  intro p hp
  let C := ballKernel F (p.2.1 : Vertex F) 2
  let P := pathStabilizer F p
  have hCP : C ≤ P := middle_ballKernel_le_four_path_stabilizer F p
  refine ⟨hCP,middle_ballKernel_normal_four_path_stabilizer F p,?_⟩
  have hmid : (p.2.1 : Vertex F).type = true := by
    have h1 := p.1.property.1
    have h2 := p.2.1.property.1
    change true ≠ (p.1 : Vertex F).type at h1
    cases ht : (p.1 : Vertex F).type <;>
      cases hu : (p.2.1 : Vertex F).type <;> simp_all
  have hP : 16 * Nat.card P = Nat.card (T : Subgroup G) := by
    dsimp only [P]
    rw [source_quintic_four_path_fixer hG T hempty hM hu hmany hcard e H hH hi p hp]
    exact source_quintic_four_path_kernel_intersection_card
      hG T hempty hM hu hmany hcard e H hH hi eH p hp
  have hC := source_quintic_second_kernel_exact_card_of_suzuki
    hG T hempty hM hu hmany hcard e H hH hi eH (p.2.1 : Vertex F) hmid
  change 64 * Nat.card C = Nat.card (T : Subgroup G) ∨
    128 * Nat.card C = Nat.card (T : Subgroup G) at hC
  have hcpos : 0 < Nat.card C := Nat.card_pos
  have hiC := (C.subgroupOf P).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hCP).toEquiv] at hiC
  change C.relIndex P * Nat.card C = Nat.card P at hiC
  change C.relIndex P = 4 ∨ C.relIndex P = 8
  rcases hC with hC | hC
  · left
    nlinarith
  · right
    nlinarith

/-- The literal four-path fixer is normal of index four in the middle first kernel. -/
theorem source_quintic_four_path_core_layers
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (eH : (H ⧸ pCore 2 H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let F := Geometry.family X H
    ∀ p : BasedWalk (graph F) 4 (base F true), p.Nonbacktracking →
      let Q := ballKernel F (p.2.1 : Vertex F) 1
      let C := ballKernel F (p.2.1 : Vertex F) 2
      C ≤ pathStabilizer F p ∧ pathStabilizer F p ≤ Q ∧
      ((pathStabilizer F p).subgroupOf Q).Normal ∧
      (pathStabilizer F p).relIndex Q = 4 := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let F := Geometry.family X H
  change ∀ p : BasedWalk (graph F) 4 (base F true), p.Nonbacktracking → _
  intro p hp
  have hmid : (p.2.1 : Vertex F).type = true := by
    have h1 := p.1.property.1
    have h2 := p.2.1.property.1
    change true ≠ (p.1 : Vertex F).type at h1
    cases ht : (p.1 : Vertex F).type <;>
      cases hu : (p.2.1 : Vertex F).type <;> simp_all
  have hfirst : (p.1 : Vertex F).type = false := by
    have hh := p.1.property.1
    change true ≠ (p.1 : Vertex F).type at hh
    cases ht : (p.1 : Vertex F).type <;> simp_all
  have hthird : (p.2.2.1 : Vertex F).type = false := by
    have hh := p.2.2.1.property.1
    rw [hmid] at hh
    cases ht : (p.2.2.1 : Vertex F).type <;> simp_all
  obtain ⟨hthree,hfive,_⟩ := source_quintic_graph_indices
    hG T hempty hM hu hmany hcard e H hH hi
  have hindices (i : Bool) : ((F (!i)).subgroupOf (F i)).index = (if i then 5 else 3) := by
    cases i
    · exact hthree
    · exact hfive
  have hdegree := card_neighbors_of_indices F (fun i => if i then 5 else 3) hindices
  have hP : 16 * Nat.card (pathStabilizer F p) = Nat.card (T : Subgroup G) := by
    rw [source_quintic_four_path_fixer hG T hempty hM hu hmany hcard e H hH hi p hp]
    exact source_quintic_four_path_kernel_intersection_card
      hG T hempty hM hu hmany hcard e H hH hi eH p hp
  have hQ := source_quintic_first_kernel_card_of_suzuki
    hG T hempty hM hu hmany hcard e H hH hi eH (p.2.1 : Vertex F) hmid
  have hb := source_quintic_neighbor_kernel_index hG T hempty hM hu hmany hcard e H hH hi
    (p.2.1 : Vertex F) (p.1 : Vertex F) hmid p.2.1.property.symm
  have hd := source_quintic_neighbor_kernel_index hG T hempty hM hu hmany hcard e H hH hi
    (p.2.1 : Vertex F) (p.2.2.1 : Vertex F) hmid p.2.2.1.property
  refine ⟨middle_ballKernel_le_four_path_stabilizer F p, ?_⟩
  apply four_path_middle_core F p hp
    (by rw [hdegree,hfirst]; rfl) (by rw [hdegree,hthird]; rfl) hb.le hd.le
  change 4 * Nat.card (ballKernel F (p.2.1 : Vertex F) 1) = Nat.card (T : Subgroup G) at hQ
  omega

/-- The middle second kernel gives an elementary quotient of order four or eight
in every four-path fixer, under the original source hypotheses and Suzuki row. -/
theorem source_quintic_four_path_middle_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (eH : (H ⧸ pCore 2 H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let F := Geometry.family X H
    ∀ p : BasedWalk (graph F) 4 (base F true), p.Nonbacktracking →
      let C := ballKernel F (p.2.1 : Vertex F) 2
      ∃ hC : (C.subgroupOf (pathStabilizer F p)).Normal,
        let _ := hC
        IsElementaryAbelian 2 (pathStabilizer F p ⧸ C.subgroupOf (pathStabilizer F p)) ∧
        (Nat.card (pathStabilizer F p ⧸ C.subgroupOf (pathStabilizer F p)) = 4 ∨
          Nat.card (pathStabilizer F p ⧸ C.subgroupOf (pathStabilizer F p)) = 8) := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let F := Geometry.family X H
  change ∀ p : BasedWalk (graph F) 4 (base F true), p.Nonbacktracking → _
  intro p hp
  have hmid : (p.2.1 : Vertex F).type = true := by
    have h1 := p.1.property.1
    have h2 := p.2.1.property.1
    change true ≠ (p.1 : Vertex F).type at h1
    cases ht : (p.1 : Vertex F).type <;>
      cases hu : (p.2.1 : Vertex F).type <;> simp_all
  have hlayers := source_quintic_four_path_core_layers
    hG T hempty hM hu hmany hcard e H hH hi eH p hp
  have hsquare := source_quintic_first_kernel_squares
    hG T hempty hM hu hmany hcard e H hH hi (p.2.1 : Vertex F) hmid
  let hC := middle_ballKernel_normal_four_path_stabilizer F p
  let _ := hC
  refine ⟨hC, four_path_middle_quotient_elementary F p hlayers.2.1 hsquare, ?_⟩
  exact (source_quintic_four_path_middle_kernel
    hG T hempty hM hu hmany hcard e H hH hi eH p hp).2.2

/-- The two local actor families extend the proved two-path action to eight.
Neither family is yet asserted unconditionally from the original source. -/
theorem source_quintic_eight_path_transitive_of_extension_actors
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (heven : QuinticEvenExtensionActors (sourceResidual M Mc ⊔ (T : Subgroup G)) H)
    (hodd : QuinticOddExtensionEscape (sourceResidual M Mc ⊔ (T : Subgroup G)) H) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    RootPathTransitive (Geometry.graph X H) (X ⊔ H : Subgroup G)
      (Geometry.base X H true) 8 := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  have htwo := source_quintic_two_path_transitive hG T hempty hM hu hmany hcard e H hH hi
  have hact : GraphAction (Geometry.graph X H) (X ⊔ H : Subgroup G) :=
    ⟨fun g _ _ h => (Subgroup.CosetGeometry.translationGraphIso (Geometry.family X H) g).toHom.map_adj h⟩
  let F := Geometry.family X H
  obtain ⟨hthree, hfive, _⟩ := source_quintic_graph_indices
    hG T hempty hM hu hmany hcard e H hH hi
  have hindices (i : Bool) : ((F (!i)).subgroupOf (F i)).index = (if i then 5 else 3) := by
    cases i
    · exact hthree
    · exact hfive
  have hdegree := card_neighbors_of_indices F (fun i => if i then 5 else 3) hindices
  apply htwo.extend_of_rightRegular hact ?_ (by decide : 2 ≤ 8)
  intro n hn hN ht p hp
  cases n with
  | zero => omega
  | succ k =>
    rcases Nat.even_or_odd (k + 1) with hnpar | hnpar
    · obtain ⟨a, ha, hfour, hsquare⟩ := heven (k + 1) hn hN hnpar ht p hp
      have he := (even_walk_iff F p.toWalk).mp (by
        simpa only [BasedWalk.length_toWalk] using hnpar)
      have hc : Nat.card ((graph F).neighborSet p.endpoint) = 5 := by
        rw [hdegree, ← he]
        rfl
      exact rightRegular_of_quintic_kernel_actor F p hc a ha hfour hsquare
    · have he : p.endpoint.type = false := by
        have hh := (even_walk_iff F p.toWalk)
        rw [BasedWalk.length_toWalk] at hh
        have hne : (base F true).type ≠ p.endpoint.type :=
          mt hh.mpr (Nat.not_even_iff_odd.mpr hnpar)
        change true ≠ p.endpoint.type at hne
        cases htype : p.endpoint.type
        · rfl
        · exact (hne htype.symm).elim
      have hc : Nat.card ((graph F).neighborSet p.endpoint) = 3 := by
        rw [hdegree, he]
        rfl
      exact rightRegular_of_cubic_kernel_escape F p hc (hodd (k + 1) hn hN hnpar ht p hp)

private theorem source_first_kernel_card
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let F := Geometry.family X H
    ∀ v : Vertex F, v.type = true →
      Nat.card (H ⧸ pCore 2 H) * Nat.card (ballKernel F v 1) =
        5 * Nat.card (T : Subgroup G) := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L := X ⊔ H
  let F := Geometry.family X H
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hTL : (T : Subgroup G) ≤ L := hTH.trans le_sup_right
  let SL := T.subtype hTL
  have hSL : (SL : Subgroup L) ≤ F true := fun x hx => hTH hx
  let S := SL.subtype hSL
  obtain ⟨_,_,hmap⟩ := source_quintic_graph_indices
    hG T hempty hM hu hmany hcard e H hH hi
  have hS : ((S : Subgroup (F true))).map (F true).subtype = F false ⊓ F true := by
    apply map_injective L.subtype_injective
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hSL]
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTL,hmap]
  have hk := base_kernel_eq_core F true S hS
  let d : F true ≃* H := subgroupOfEquivOfLe (show H ≤ L from le_sup_right)
  have hquot : Nat.card (F true ⧸ pCore 2 (F true)) = Nat.card (H ⧸ pCore 2 H) :=
    Nat.card_congr (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).toEquiv
  have hHcard : Nat.card (F true) = Nat.card H := Nat.card_congr d.toEquiv
  have hc := (pCore 2 (F true)).index_mul_card
  change Nat.card (F true ⧸ pCore 2 (F true)) * Nat.card (pCore 2 (F true)) = _ at hc
  rw [hquot,hHcard] at hc
  have hb : Nat.card (ballKernel F (base F true) 1) = Nat.card (pCore 2 (F true)) := by
    rw [hk,card_map_of_injective (F true).subtype_injective]
  have ht := ((T : Subgroup G).subgroupOf H).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hTH).toEquiv] at ht
  change (T : Subgroup G).relIndex H * Nat.card (T : Subgroup G) = Nat.card H at ht
  rw [hi] at ht
  change ∀ v : Vertex F, v.type = true → _
  intro v hv
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  rw [hv] at hg
  rw [←hg,ballKernel_translate,card_map_of_injective (MulAut.conj g).injective,hb]
  exact hc.trans ht.symm


/-- Four-path transitivity already excludes the dihedral quotient: the
middle kernel would be too large for the counted path fixer. This uses
path transitivity as a premise, not as an unconditional source conclusion. -/
theorem source_quintic_suzuki_of_long_path_transitive
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (n : ℕ) (hn : 4 ≤ n)
    (ht : let X := sourceResidual M Mc ⊔ (T : Subgroup G)
      RootPathTransitive (Geometry.graph X H) (X ⊔ H : Subgroup G)
        (Geometry.base X H true) n) :
    Nonempty ((H ⧸ pCore 2 H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L := X ⊔ H
  let F := Geometry.family X H
  obtain ⟨hthree,hfive,_⟩ := source_quintic_graph_indices
    hG T hempty hM hu hmany hcard e H hH hi
  have hindices (i : Bool) : ((F (!i)).subgroupOf (F i)).index = (if i then 5 else 3) := by
    cases i
    · exact hthree
    · exact hfive
  have hdegree := card_neighbors_of_indices F (fun i => if i then 5 else 3) hindices
  have (v : Vertex F) : Finite ((graph F).neighborSet v) :=
    Nat.finite_of_card_ne_zero (by rw [hdegree]; cases v.type <;> decide)
  have hdeg : BasedWalk.HasTwoNeighbors (graph F) := by
    intro v w
    exact Set.exists_ne_of_one_lt_ncard
      (show 1 < ((graph F).neighborSet v).ncard from by
        change 1 < Nat.card ((graph F).neighborSet v)
        rw [hdegree]; cases v.type <;> decide) w
  have ht4 := ht.mono hdeg hn
  obtain ⟨p,hp,_⟩ := BasedWalk.exists_extension hdeg (by decide : 0 ≤ 4) (x := base F true)
    (PUnit.unit : BasedWalk (graph F) 0 (base F true)) trivial
  have hfirst : (p.1 : Vertex F).type = false := by
    have hh := p.1.property.1
    change true ≠ (p.1 : Vertex F).type at hh
    cases h : (p.1 : Vertex F).type <;> simp_all
  have hmid : (p.2.1 : Vertex F).type = true := by
    have hh := p.2.1.property.1
    rw [hfirst] at hh
    cases h : (p.2.1 : Vertex F).type <;> simp_all
  have hthird : (p.2.2.1 : Vertex F).type = false := by
    have hh := p.2.2.1.property.1
    rw [hmid] at hh
    cases h : (p.2.2.1 : Vertex F).type <;> simp_all
  have hbound := four_path_middle_card_le F p hp
    (by rw [hdegree,hfirst]; rfl) (by rw [hdegree,hthird]; rfl)
    (source_quintic_neighbor_kernel_index hG T hempty hM hu hmany hcard e H hH hi
      (p.2.1 : Vertex F) (p.1 : Vertex F) hmid p.2.1.property.symm).le
    (source_quintic_neighbor_kernel_index hG T hempty hM hu hmany hcard e H hH hi
      (p.2.1 : Vertex F) (p.2.2.1 : Vertex F) hmid p.2.2.1.property).le
  have hflip {a b : Vertex F} (hab : (graph F).Adj a b) : b.type = !a.type := by
    have hh := hab.1
    cases ha : a.type <;> cases hb : b.type <;> simp_all
  have hcount : Nat.card {q : BasedWalk (graph F) 4 (base F true) // q.Nonbacktracking} = 80 :=
    BasedWalk.card_nonbacktracking_succ (graph F)
      (fun v : Vertex F => v.type) (fun i => if i then 5 else 3) hflip hdegree 3 (base F true)
  have hc := card_paths_mul_card_fixer F ht4 p hp
  rw [hcount,stabilizer,Subgroup.CosetGeometry.stabilizer_base] at hc
  have hHcard : Nat.card (F true) = Nat.card H :=
    Nat.card_congr (subgroupOfEquivOfLe (show H ≤ L from le_sup_right)).toEquiv
  rw [hHcard] at hc
  have hT := ((T : Subgroup G).subgroupOf H).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hH.1.1.2).toEquiv] at hT
  change (T : Subgroup G).relIndex H * Nat.card (T : Subgroup G) = Nat.card H at hT
  rw [hi] at hT
  have hQ := source_first_kernel_card hG T hempty hM hu hmany hcard e H hH hi
    (p.2.1 : Vertex F) hmid
  rcases source_index_five_models hG T hempty hM hu hmany hcard e H hH.1 hi with hd | hs
  · have hquot : Nat.card (H ⧸ pCore 2 H) = 10 :=
      (Nat.card_congr hd.some.toEquiv).trans DihedralGroup.nat_card
    rw [hquot] at hQ
    change 10 * Nat.card (ballKernel F (p.2.1 : Vertex F) 1) =
      5 * Nat.card (T : Subgroup G) at hQ
    have hpos : 0 < Nat.card (pathStabilizer F p) := Nat.card_pos
    omega
  · exact hs


private theorem source_four_path_middle_kernel_at
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (eH : (H ⧸ pCore 2 H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let F := Geometry.family X H
    ∀ {a : Vertex F}, a.type = true →
      ∀ p : BasedWalk (graph F) 4 a, p.Nonbacktracking →
        pathStabilizer F p ≤ ballKernel F (p.2.1 : Vertex F) 1 := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let F := Geometry.family X H
  change ∀ {a : Vertex F}, a.type = true →
    ∀ p : BasedWalk (graph F) 4 a, p.Nonbacktracking → _
  intro a ha p hp
  obtain ⟨q,hq,g,hg⟩ := exists_base_path_translate F ha p hp
  have hm : g • (q.2.1 : Vertex F) = (p.2.1 : Vertex F) := by
    have hh := congrArg (fun l : List (Vertex F) => l[2]?) hg
    simpa [BasedWalk.vertices] using hh
  exact pathStabilizer_le_ballKernel_of_vertices F q p g hg hm 1
    (source_quintic_four_path_core_layers hG T hempty hM hu hmany hcard e H hH hi eH q hq).2.1

/-- In the Suzuki row, the five-path induction hypothesis makes every
pointwise fixer escape the cubic endpoint kernel. -/
theorem source_quintic_five_path_kernel_escape_of_suzuki
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (eH : (H ⧸ pCore 2 H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)
    (ht : let X := sourceResidual M Mc ⊔ (T : Subgroup G)
      RootPathTransitive (Geometry.graph X H) (X ⊔ H : Subgroup G)
        (Geometry.base X H true) 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let F := Geometry.family X H
    ∀ p : BasedWalk (graph F) 5 (base F true), p.Nonbacktracking →
      ¬ pathStabilizer F p ≤ ballKernel F p.endpoint 1 := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L := X ⊔ H
  let F := Geometry.family X H
  have hact : GraphAction (graph F) L :=
    ⟨fun g _ _ h => (Subgroup.CosetGeometry.translationGraphIso F g).toHom.map_adj h⟩
  obtain ⟨hthree,hfive,_⟩ := source_quintic_graph_indices
    hG T hempty hM hu hmany hcard e H hH hi
  have hindices (i : Bool) : ((F (!i)).subgroupOf (F i)).index = (if i then 5 else 3) := by
    cases i
    · exact hthree
    · exact hfive
  have hdegree := card_neighbors_of_indices F (fun i => if i then 5 else 3) hindices
  have (v : Vertex F) : Finite ((graph F).neighborSet v) :=
    Nat.finite_of_card_ne_zero (by rw [hdegree]; cases v.type <;> decide)
  have hdeg : BasedWalk.HasTwoNeighbors (graph F) := by
    intro v w
    obtain ⟨z,hz,hzw⟩ := Set.exists_ne_of_one_lt_ncard
      (show 1 < ((graph F).neighborSet v).ncard from by
        change 1 < Nat.card ((graph F).neighborSet v)
        rw [hdegree]; cases v.type <;> decide) w
    exact ⟨z,hz,hzw⟩
  have hflip {a b : Vertex F} (hab : (graph F).Adj a b) : b.type = !a.type := by
    have hh := hab.1
    cases ha : a.type <;> cases hb : b.type <;> simp_all
  have hcard' : ∀ {a : Vertex F}, a.type = true →
      ∀ p : BasedWalk (graph F) 5 a, p.Nonbacktracking →
        Nat.card (ballKernel F p.penultimate 2) ≤ Nat.card (pathStabilizer F p) := by
    intro a ha p hp
    obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F a
    rw [ha] at hg
    have hta : RootPathTransitive (graph F) L a 5 :=
      hg ▸ ht.smul hact g
    have hcount : Nat.card {q : BasedWalk (graph F) 5 a // q.Nonbacktracking} = 320 := by
      have hh := BasedWalk.card_nonbacktracking_succ (graph F)
        (fun v : Vertex F => v.type) (fun i => if i then 5 else 3) hflip hdegree 4 a
      rw [ha] at hh
      exact hh
    have hc := card_paths_mul_card_fixer F hta p hp
    have hs : Nat.card (stabilizer F a) = Nat.card (F true) := by
      rw [←hg,stabilizer_translate,card_map_of_injective (MulAut.conj g).injective,
        stabilizer,Subgroup.CosetGeometry.stabilizer_base]
    rw [hcount,hs] at hc
    have hHcard : Nat.card (F true) = Nat.card H :=
      Nat.card_congr (subgroupOfEquivOfLe (show H ≤ L from le_sup_right)).toEquiv
    rw [hHcard] at hc
    have hT := ((T : Subgroup G).subgroupOf H).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hH.1.1.2).toEquiv] at hT
    change (T : Subgroup G).relIndex H * Nat.card (T : Subgroup G) = Nat.card H at hT
    rw [hi] at hT
    have he : p.penultimate.type = true := by
      have hh := (even_walk_iff F (p.take 4 (by decide)).toWalk).mp (by
        simp only [BasedWalk.length_toWalk]; decide)
      simpa only [BasedWalk.endpoint_take_penultimate,ha] using hh.symm
    have hC := source_quintic_second_ball_kernel_card_of_suzuki
      hG T hempty hM hu hmany hcard e H hH hi eH p.penultimate he
    change 64 * Nat.card (ballKernel F p.penultimate 2) ≤ Nat.card (T : Subgroup G) at hC
    omega
  change ∀ p : BasedWalk (graph F) 5 (base F true), p.Nonbacktracking → _
  intro p hp
  exact five_path_kernel_escape_of_transitive F hdeg
    (fun v hv => by rw [hdegree,hv]; rfl)
    (source_four_path_middle_kernel_at hG T hempty hM hu hmany hcard e H hH hi eH)
    hcard' (source_quintic_second_kernel_separation hG T hempty hM hu hmany hcard e H hH hi)
    ht p hp

/-- The length-five odd escape supplies the actual next path action. -/
theorem source_quintic_six_path_transitive_of_suzuki_and_five_paths
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (eH : (H ⧸ pCore 2 H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)
    (ht : let X := sourceResidual M Mc ⊔ (T : Subgroup G)
      RootPathTransitive (Geometry.graph X H) (X ⊔ H : Subgroup G)
        (Geometry.base X H true) 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    RootPathTransitive (Geometry.graph X H) (X ⊔ H : Subgroup G)
      (Geometry.base X H true) 6 := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let F := Geometry.family X H
  have hact : GraphAction (graph F) (X ⊔ H : Subgroup G) :=
    ⟨fun g _ _ h => (Subgroup.CosetGeometry.translationGraphIso F g).toHom.map_adj h⟩
  obtain ⟨hthree,hfive,_⟩ := source_quintic_graph_indices
    hG T hempty hM hu hmany hcard e H hH hi
  have hindices (i : Bool) : ((F (!i)).subgroupOf (F i)).index = (if i then 5 else 3) := by
    cases i
    · exact hthree
    · exact hfive
  have hdegree := card_neighbors_of_indices F (fun i => if i then 5 else 3) hindices
  apply ht.succ_of_rightRegular hact
  intro p hp
  have he : p.endpoint.type = false := by
    have hh := (even_walk_iff F p.toWalk)
    rw [BasedWalk.length_toWalk] at hh
    have hne : (base F true).type ≠ p.endpoint.type := mt hh.mpr (by decide : ¬ Even 5)
    change true ≠ p.endpoint.type at hne
    cases htype : p.endpoint.type
    · rfl
    · exact (hne htype.symm).elim
  exact rightRegular_of_cubic_kernel_escape F p (by rw [hdegree,he]; rfl)
    (source_quintic_five_path_kernel_escape_of_suzuki
      hG T hempty hM hu hmany hcard e H hH hi eH ht p hp)

/-- The length-five case of the original odd actor contract. Its only
induction premise is five-path transitivity; the quotient row is derived. -/
theorem source_quintic_five_path_kernel_escape
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (ht : let X := sourceResidual M Mc ⊔ (T : Subgroup G)
      RootPathTransitive (Geometry.graph X H) (X ⊔ H : Subgroup G)
        (Geometry.base X H true) 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let F := Geometry.family X H
    ∀ p : BasedWalk (graph F) 5 (base F true), p.Nonbacktracking →
      ¬ pathStabilizer F p ≤ ballKernel F p.endpoint 1 := by
  obtain ⟨eH⟩ := source_quintic_suzuki_of_long_path_transitive
    hG T hempty hM hu hmany hcard e H hH hi 5 (by decide) ht
  exact source_quintic_five_path_kernel_escape_of_suzuki
    hG T hempty hM hu hmany hcard e H hH hi eH ht

/-- Original five-path transitivity extends to six, with no model or
stabilizer-order premise. Final assembly must still establish the
five-path induction hypothesis from the length-four even actor. -/
theorem source_quintic_six_path_transitive_of_five_paths
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (ht : let X := sourceResidual M Mc ⊔ (T : Subgroup G)
      RootPathTransitive (Geometry.graph X H) (X ⊔ H : Subgroup G)
        (Geometry.base X H true) 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    RootPathTransitive (Geometry.graph X H) (X ⊔ H : Subgroup G)
      (Geometry.base X H true) 6 := by
  obtain ⟨eH⟩ := source_quintic_suzuki_of_long_path_transitive
    hG T hempty hM hu hmany hcard e H hH hi 5 (by decide) ht
  exact source_quintic_six_path_transitive_of_suzuki_and_five_paths
    hG T hempty hM hu hmany hcard e H hH hi eH ht

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
