module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.FiniteGeometry.Planes

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.LocalAction
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction

/-!
# The incident edge inside its relative normalizer orbit

The nonzero edge commutator E is a normal subgroup of the incident edge
two-group, so E meets its center nontrivially. This intersection lies in
the opposite Z-layer. The marked natural action identifies E with a line
or plane in the binary three-space. Its full setwise stabilizer acts
transitively on its nonzero elements, so any relative-normalizer invariant
subgroup containing that opposite Z-layer contains E.

At the first edge of a critical path, the opposite Z-layer lies in the
next vertex's Z-layer. Its prescribed P-orbit therefore contains E.
The proof covers both possible edge orders and does not assert that the
whole starting Z-layer lies in the prescribed span. The only finite
calculation checks the three-cycle on the three nonzero points of the
standard binary plane.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the natural action in (4.1) and the initial R₀ calculation in
(4.4.4), printed pp.881--882,894.
-/

public section

open Subgroup Matrix Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open Escape.Propagation.Backward.Products.Selection.Choices
open Escape.Propagation.Backward.Products.Selection.Choices.FiniteGeometry

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Seed.CriticalInclusion

private def cyclePlane : SL := ⟨!![0,1,0; 1,1,0; 0,0,1], by decide⟩

private theorem cyclePlane_mem : cyclePlane ∈ planeStabilizer standardPlane := by
  rw [mem_planeStabilizer_iff]
  intro v hv
  change (!![0,1,0; 1,1,0; 0,0,1].mulVec v.toAdd) 2 = 0
  change v.toAdd 2 = 0 at hv
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hv

private theorem plane_generated (A : Subgroup Space) (hA : Nat.card A = 4)
    (B : Subgroup Space)
    (hB : ∀ g ∈ planeStabilizer A, ∀ v ∈ B, modelAction g v ∈ B)
    {u : Space} (huA : u ∈ A) (huB : u ∈ B) (hu : u ≠ 1) : A ≤ B := by
  obtain ⟨g, hg⟩ := plane_transitive A hA
  subst A
  obtain ⟨v, hv, rfl⟩ := huA
  have hvne : v ≠ 1 := by
    intro h
    subst v
    exact hu (map_one _)
  have hc : MulAut.conj g cyclePlane ∈ planeStabilizer (move g standardPlane) := by
    rw [planeStabilizer_move]
    exact mem_map_of_mem _ cyclePlane_mem
  have h1 : modelAction g (modelAction cyclePlane v) ∈ B := by
    rw [← action_conj]
    exact hB _ hc _ huB
  have h2 : modelAction g (modelAction cyclePlane (modelAction cyclePlane v)) ∈ B := by
    rw [← action_conj]
    exact hB _ hc _ h1
  have shape : ∀ v w : Space, v ∈ standardPlane → v ≠ 1 → w ∈ standardPlane →
      w = 1 ∨ w = v ∨ w = modelAction cyclePlane v ∨
        w = modelAction cyclePlane (modelAction cyclePlane v) := by decide +kernel
  rintro _ ⟨w, hw, rfl⟩
  rcases shape v w hv hvne hw with rfl | rfl | rfl | rfl
  · exact (map_one (modelAction g)) ▸ B.one_mem
  · exact huB
  · exact h1
  · exact h2

private theorem small_generated (A : Subgroup Space) (hA : Nat.card A = 2 ∨ Nat.card A = 4)
    (B : Subgroup Space)
    (hB : ∀ g ∈ planeStabilizer A, ∀ v ∈ B, modelAction g v ∈ B)
    {u : Space} (huA : u ∈ A) (huB : u ∈ B) (hu : u ≠ 1) : A ≤ B := by
  rcases hA with hA | hA
  · have hne : A ⊓ B ≠ ⊥ := by
      intro h
      have hh : u ∈ A ⊓ B := ⟨huA, huB⟩
      rw [h, mem_bot] at hh
      exact hu hh
    have hc : 1 < Nat.card ↥(A ⊓ B) := (one_lt_card_iff_ne_bot _).mpr hne
    have he : A ⊓ B = A := eq_of_le_of_card_ge inf_le_left (by omega)
    exact he ▸ (show A ⊓ B ≤ B from inf_le_right)
  · exact plane_generated A hA B hB huA huB hu


variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem edge_meets_opposite_Z (common : CommonFacts R source geometry)
    {a t : Vertex R} (ha : color R a = false) (ht : Adjacent R a t) :
    ∃ x : FreeAmalgam R, x ∈ edgeCommutator R a t ∧ x ∈ Z R t ∧ x ≠ 1 := by
  let E := edgeCommutator R a t
  have hEZ : E ≤ Z R a := (Escape.EdgeTransfer.edge_commutator_le_natural
    common.large_distance (moduleFacts common) a t ha ht).trans (U_le_Z R a)
  have hEQ : E ≤ Q R t := hEZ.trans
    (Escape.EdgeTransfer.edge_Z_le_Q common.large_distance a t ha ht)
  let := finite_stabilizer R t
  let : Finite (Q R t) := Finite.of_injective
    (inclusion (show Q R t ≤ stabilizer R t from fun _ hx => hx.1)) (inclusion_injective _)
  let D := E.subgroupOf (Q R t)
  let : D.Normal := normal_subgroupOf_of_le_normalizer
    (normalizer_commutator_ge_right (Z R a) (Q R t))
  have hD : D ≠ ⊥ := by
    intro h
    have hh := congrArg (Subgroup.map (Q R t).subtype) h
    rw [map_subgroupOf_eq_of_le hEQ, Subgroup.map_bot] at hh
    exact Escape.EdgeTransfer.edge_commutator_ne_bot (moduleFacts common) a t ha ht hh
  have hmeet := center_inf_ne_bot_of_normal
    (Escape.EdgeTransfer.edge_kernel_two source a t ha ht) D hD
  obtain ⟨x, hx, hxne⟩ := (center (Q R t) ⊓ D).bot_or_exists_ne_one.resolve_left hmeet
  refine ⟨x, hx.2, ?_, fun h => hxne (Subtype.ext h)⟩
  rw [Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance (moduleFacts common) a t ha ht]
  refine ⟨hEZ hx.2, ?_⟩
  intro q hq
  exact congrArg Subtype.val (mem_center_iff.mp hx.1 ⟨q, hq⟩)

/-- A relative-normalizer invariant group containing the opposite omega-center
contains the whole incident edge commutator. -/
theorem edge_le_of_normalized (common : CommonFacts R source geometry)
    {a t : Vertex R} (ha : color R a = false) (ht : Adjacent R a t)
    (W : Subgroup (FreeAmalgam R))
    (hW : stabilizer R a ⊓ normalizer (edgeCommutator R a t : Set (FreeAmalgam R)) ≤
      normalizer (W : Set (FreeAmalgam R))) (hZW : Z R t ≤ W) :
    edgeCommutator R a t ≤ W := by
  obtain ⟨model⟩ := localModel_nonempty source (moduleFacts common) a ha
  let E := edgeCommutator R a t
  let D := U R a ⊓ W
  have hEU : E ≤ U R a := Escape.EdgeTransfer.edge_commutator_le_natural
    common.large_distance (moduleFacts common) a t ha ht
  have hcard : Nat.card E = 2 ∨ Nat.card E = 4 := by
    have hdiv := card_dvd_of_le hEU
    rw [common.natural.card_at a ha] at hdiv
    have hh := Nat.mem_divisors.mpr ⟨hdiv, (by decide : 8 ≠ 0)⟩
    rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hh
    have hone : Nat.card E ≠ 1 := fun h =>
      Escape.EdgeTransfer.edge_commutator_ne_bot (moduleFacts common) a t ha ht
        (Subgroup.card_eq_one.mp h)
    have hsmall := Escape.EdgeTransfer.edge_displacement_card_le_four
      common.large_distance (moduleFacts common) a t ha ht
    change Nat.card E ≤ 4 at hsmall
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    omega
  have hstable : ∀ s ∈ planeStabilizer (model.coordinates E),
      ∀ v ∈ model.coordinates D, modelAction s v ∈ model.coordinates D := by
    intro s hs
    obtain ⟨k, rfl⟩ := model.surjective s
    have hmap : E.map (MulAut.conj (k : FreeAmalgam R)).toMonoidHom = E := by
      refine model.coordinates_injective ?_ hEU ?_
      · exact (map_mono hEU).trans
          (mem_normalizer_iff_map_conj_eq.mp (U_normalized a k.property)).le
      · rw [model.coordinates_conjugate k E hEU]
        exact hs
    have hkE : (k : FreeAmalgam R) ∈ normalizer (E : Set (FreeAmalgam R)) :=
      mem_normalizer_iff_map_conj_eq.mpr hmap
    have hkW := hW ⟨k.property, hkE⟩
    rintro v ⟨u, hu, rfl⟩
    let u' : U R a := ⟨k * (u : FreeAmalgam R) * (k : FreeAmalgam R)⁻¹,
      (mem_normalizer_iff.mp (U_normalized a k.property) u).mp u.property⟩
    refine ⟨u', ⟨u'.property, (mem_normalizer_iff.mp hkW u).mp hu.2⟩, ?_⟩
    exact model.action k u u' rfl
  obtain ⟨x, hxE, hxZ, hxne⟩ := edge_meets_opposite_Z common ha ht
  let u : U R a := ⟨x, hEU hxE⟩
  have hu : model.equiv u ≠ 1 := by
    intro h
    exact hxne (congrArg Subtype.val (model.equiv.map_eq_one_iff.mp h))
  have hcoord := small_generated (model.coordinates E)
    (by rw [model.coordinates_card E hEU]; exact hcard) (model.coordinates D) hstable
    (show model.equiv u ∈ model.coordinates E from ⟨u, hxE, rfl⟩)
    (show model.equiv u ∈ model.coordinates D from ⟨u, ⟨u.property, hZW hxZ⟩, rfl⟩) hu
  intro y hy
  obtain ⟨v, hv, he⟩ := hcoord
    (show model.equiv ⟨y, hEU hy⟩ ∈ model.coordinates E from ⟨⟨y, hEU hy⟩, hy, rfl⟩)
  have hvy := model.equiv.injective he
  have hval := congrArg Subtype.val hvy
  change (v : FreeAmalgam R) = y at hval
  rw [← hval]
  exact hv.2

/-- The prescribed relative P-orbit contains its forward edge displacement. -/
theorem first_edge_le_prescribedSpan (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') :
    edgeCommutator R a (p.walk.getVert 1) ≤ prescribedSpan p := by
  have hb := common.large_distance
  have hl := p.length_eq_b
  have hat : Adjacent R a (p.walk.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero, Nat.zero_add] using
      (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i := 0) (by omega))
  apply edge_le_of_normalized common p.start_color hat
  · let P := stabilizer R a ⊓
      normalizer (edgeCommutator R a (p.walk.getVert 1) : Set (FreeAmalgam R))
    have he : prescribedSpan p =
        NormalizerTransfer.conjugatesIn (Z R (p.walk.getVert 2)) P := by
      simp only [prescribedSpan, NormalizerTransfer.conjugatesIn,
        NormalizerTransfer.rightConjugate, Z_act, P]
    rw [he]
    exact NormalizerTransfer.conjugatesIn_normalized _ _
  · have hcol : color R (p.walk.getVert 2) = false :=
      (p.vertex_color (by omega)).mpr (by decide)
    have hdt : Adjacent R (p.walk.getVert 2) (p.walk.getVert 1) := by
      exact adjacent_symm R ((cosetGraph_adj R _ _).mp
        (p.walk.adj_getVert_succ (i := 1) (by omega)))
    apply (Escape.EdgeTransfer.edge_Z_le _ _ hcol hdt).trans
    have hh := le_iSup (fun g : ↥(stabilizer R a ⊓
        normalizer (edgeCommutator R a (p.walk.getVert 1) : Set (FreeAmalgam R))) =>
      Z R (Stellmacher.PushingUp.AmalgamGraph.act R g (p.walk.getVert 2))) 1
    simpa only [prescribedSpan, Subgroup.coe_one, act_one] using hh

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Seed.CriticalInclusion
