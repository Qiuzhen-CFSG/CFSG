module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.LocalAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.FiniteGeometry.Planes
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalAction

/-!
# Maximality of the normalizer of an incident edge displacement

The actual natural-module marking identifies every nonzero edge commutator
with a subgroup of order two or four in the binary three-space. Its setwise
stabilizer is a maximal parabolic in either case. Pulling that stabilizer back
through the same marked local projection proves maximality inside G_a, and
hence generation with every actor outside the relative normalizer.

The order-four case reuses the checked plane geometry. For order two, complete
the nonzero vector to a basis and transport the standard point parabolic.
No exact edge order, contrary escape configuration, or later index formula is
used. The consumer is the P-orbit growth argument for MS93 (4.4.4).

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), initial R₀ calculation in (4.4.4), printed p.894.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Seed.OrbitGrowth
open Escape.Propagation.Backward.Products.Selection.Choices
open Escape.Propagation.Backward.Products.Selection.Choices.FiniteGeometry

private def standardLine : Subgroup Space where
  carrier := {v | v.toAdd 1 = 0 ∧ v.toAdd 2 = 0}
  one_mem' := ⟨rfl, rfl⟩
  mul_mem' := by
    rintro v w ⟨hv1, hv2⟩ ⟨hw1, hw2⟩
    exact ⟨by change v.toAdd 1 + w.toAdd 1 = 0; rw [hv1, hw1, add_zero],
      by change v.toAdd 2 + w.toAdd 2 = 0; rw [hv2, hw2, add_zero]⟩
  inv_mem' := by
    rintro v ⟨hv1, hv2⟩
    exact ⟨by change -v.toAdd 1 = 0; rw [hv1, neg_zero],
      by change -v.toAdd 2 = 0; rw [hv2, neg_zero]⟩

private instance : DecidablePred (· ∈ standardLine) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

private theorem standardLine_card : Nat.card standardLine = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem standardLine_stabilizer :
    planeStabilizer standardLine = Matrix.PSL3Two.pointParabolicSL := by
  ext g
  rw [mem_planeStabilizer_iff, Matrix.PSL3Two.pointParabolicSL,
    MulAction.mem_stabilizer_set' (Set.toFinite _)]
  rfl

private theorem line_transitive (A : Subgroup Space) (hA : Nat.card A = 2) :
    ∃ g : SL, move g standardLine = A := by
  classical
  have : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨u, hu⟩ := exists_ne (1 : A)
  have hu0 : u.val.toAdd ≠ 0 := fun h => hu (Subtype.ext h)
  have other : ∀ u : Fin 3 → ZMod 2, ∃ v : Fin 3 → ZMod 2, v ≠ 0 ∧ u ≠ v := by
    decide
  obtain ⟨v, hv, huv⟩ := other u.val.toAdd
  obtain ⟨w, hw⟩ := complete_pair u.val.toAdd v hu0 hv huv
  let g : SL := ⟨(fun i => ![u.val.toAdd i, v i, w i]), hw⟩
  have hg0 : modelAction g e0 = u.val := by
    change g.val.mulVec ![1, 0, 0] = u.val.toAdd
    ext i
    simp [g, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have shape : ∀ z : Space, z ∈ standardLine → z = 1 ∨ z = e0 := by decide
  refine ⟨g, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    rcases shape z hz with rfl | rfl
    · simpa only [map_one] using A.one_mem
    · change modelAction g e0 ∈ A
      rw [hg0]
      exact u.property
  · rw [move_card, standardLine_card, hA]

private theorem lineStabilizer_isCoatom (A : Subgroup Space) (hA : Nat.card A = 2) :
    IsCoatom (planeStabilizer A) := by
  obtain ⟨g, rfl⟩ := line_transitive A hA
  rw [planeStabilizer_move]
  apply ((MulAut.conj g).mapSubgroup.isCoatom_iff _).mpr
  rw [standardLine_stabilizer]
  exact Matrix.PSL3Two.isCoatom_pointParabolicSL

variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

private theorem normalizer_comap {a : Vertex R} (model : LocalModel a)
    {E : Subgroup (FreeAmalgam R)} (hE : E ≤ U R a) :
    (planeStabilizer (model.coordinates E)).comap model.projection =
      (normalizer (E : Set (FreeAmalgam R))).subgroupOf (stabilizer R a) := by
  ext g
  change (model.coordinates E).map (modelAction (model.projection g)).toMonoidHom =
    model.coordinates E ↔ (g : FreeAmalgam R) ∈ normalizer (E : Set (FreeAmalgam R))
  rw [← model.coordinates_conjugate g E hE, mem_normalizer_iff_map_conj_eq]
  constructor
  · intro h
    apply model.coordinates_injective _ hE h
    exact (map_mono hE).trans
      (mem_normalizer_iff_map_conj_eq.mp (U_normalized a g.property)).le
  · intro h
    exact congrArg model.coordinates h

/-- The relative normalizer of an incident edge displacement is maximal in G_a.
Both possible nonzero proper subgroups of the marked natural three-space are covered. -/
theorem edge_normalizer_isCoatom [Finite M] {source : LocalSource L R}
    (common : CommonFacts R source geometry) {a t : Vertex R}
    (ha : color R a = false) (ht : Adjacent R a t) :
    IsCoatom ((normalizer (edgeCommutator R a t : Set (FreeAmalgam R))).subgroupOf
      (stabilizer R a)) := by
  obtain ⟨model⟩ := localModel_nonempty source (moduleFacts common) a ha
  have hE := Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
    (moduleFacts common) a t ha ht
  have hsmall := Escape.EdgeTransfer.edge_displacement_card_le_four common.large_distance
    (moduleFacts common) a t ha ht
  have hne := Escape.EdgeTransfer.edge_commutator_ne_bot (moduleFacts common) a t ha ht
  let E := edgeCommutator R a t
  have hcard : Nat.card E = 2 ∨ Nat.card E = 4 := by
    have hdiv := card_dvd_of_le hE
    rw [common.natural.card_at a ha] at hdiv
    have hh := Nat.mem_divisors.mpr ⟨hdiv, (by decide : 8 ≠ 0)⟩
    rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hh
    have hone : Nat.card E ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    change Nat.card E ≤ 4 at hsmall
    change Nat.card E = 1 ∨ Nat.card E = 2 ∨ Nat.card E = 4 ∨ Nat.card E = 8 at hh
    omega
  change E ≤ U R a at hE
  change IsCoatom ((normalizer (E : Set (FreeAmalgam R))).subgroupOf (stabilizer R a))
  rw [← normalizer_comap model hE]
  apply Subgroup.isCoatom_comap_of_surjective model.surjective
  have he := model.coordinates_card E hE
  rcases hcard with h | h
  · exact lineStabilizer_isCoatom _ (he.trans h)
  · exact planeStabilizer_isCoatom _ (he.trans h)

/-- An actor outside the specified relative edge normalizer generates G_a with it. -/
theorem edge_normalizer_sup_eq [Finite M] {source : LocalSource L R}
    (common : CommonFacts R source geometry) {a t : Vertex R}
    (ha : color R a = false) (ht : Adjacent R a t)
    {A : Subgroup (FreeAmalgam R)} (hA : A ≤ stabilizer R a)
    (hn : ¬ A ≤ stabilizer R a ⊓ normalizer (edgeCommutator R a t : Set (FreeAmalgam R))) :
    (stabilizer R a ⊓ normalizer (edgeCommutator R a t : Set (FreeAmalgam R))) ⊔ A =
      stabilizer R a := by
  let F := stabilizer R a
  let P := F ⊓ normalizer (edgeCommutator R a t : Set (FreeAmalgam R))
  have hmax : IsCoatom (P.subgroupOf F) := by
    simpa only [P, F, inf_subgroupOf_left] using edge_normalizer_isCoatom common ha ht
  have hnot : ¬ A.subgroupOf F ≤ P.subgroupOf F := by
    intro h
    apply hn
    intro x hx
    exact h (show (⟨x, hA hx⟩ : F) ∈ A.subgroupOf F from hx)
  have he : P.subgroupOf F ⊔ A.subgroupOf F = ⊤ :=
    hmax.2 _ (left_lt_sup.mpr hnot)
  have hAF : A ≤ F := hA
  have hh := congrArg (Subgroup.map F.subtype) he
  change P ⊔ A = F
  simpa only [Subgroup.map_sup, map_subgroupOf_eq_of_le (show P ≤ F from inf_le_left),
    map_subgroupOf_eq_of_le hAF, ← MonoidHom.range_eq_map, range_subtype] using hh

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Seed.OrbitGrowth
