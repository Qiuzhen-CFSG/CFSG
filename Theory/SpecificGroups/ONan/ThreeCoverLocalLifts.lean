module

public import Theory.SpecificGroups.ONan.E9A4.Separation
public import Theory.SpecificGroups.Alternating.E9A4CentralLift
public import Theory.SpecificGroups.ONan.LinearCoverKernel

/-!
# The local E₉ construction in O'Nan central three-covers

The four fixed ATLAS words used for E₉ × A₄ in the projective model have
linear lifts x, y, u, t. The matrix transition table implies x³ = t³ = 1
and [x,t] = 1 already in the linear group. Thus a compatible homomorphism
from the linear group into a central cover supplies commuting cubic lifts
of the first cyclic generator and the A₄ three-cycle. The projective E₉ × A₄
embedding proves they are independent modulo the center.

`E9A4CentralLift` constructs the inverse image's characteristic Sylow
two-subgroup above 1 × V₄. It is nontrivial and normalized by these lifts.
Consequently the construction supplies the exact E₉ and two-subgroup needed
by `Theory.Quasithin.CentralThreeLocalRank`.

The final export is conditional on the existing matrix-realization,
matrix-table/projective-embedding, and compatible-cover-lifting contracts.
This module proves the assembly, not the existence of those inputs. In
particular the ATLAS representation alone does not prove universal lifting.

Source: Aschbacher--Smith, A.2.19, printed p.41/PDF p.52, and the E₉ × A₆
construction in I.2.1, printed p.409/PDF p.420. The candidate words and
ATLAS attribution are preserved in `E9A4/source/README.md`. No I.2 theorem,
rank estimate, or conclusion-bearing certificate is assumed here.
-/

namespace ONan.E9A4
open Theory.SpecificGroups.E9A4 (Coord next)

set_option maxRecDepth 4096 in
/-- The matrix table contains a commuting pair of cubic elements in the linear
cover: the first E9 generator and the A4 three-cycle. -/
public theorem linear_cubic_pair_of_matrix_table
    (hgen : ∀ i, (linearGenerators i : Mat) = Data.generatorMatrix i)
    (htable : ∀ c i, Data.table c * Data.generatorMatrix i =
      Data.scalar c i • Data.table (next c i)) :
    (linearGenerators 0) ^ 3 = 1 ∧ (linearGenerators 3) ^ 3 = 1 ∧
      Commute (linearGenerators 0) (linearGenerators 3) := by
  have step (c : Coord) (i : Fin 4) (h : Data.scalar c i = 1) :
      Data.table c * Data.generatorMatrix i = Data.table (next c i) := by
    simpa only [h, one_smul] using htable c i
  have hx2 : Data.gen0 * Data.gen0 = Data.m72 :=
    step ((1, 0), 0) 0 (by decide +kernel)
  have hx3 : Data.m72 * Data.gen0 = 1 :=
    (step ((2, 0), 0) 0 (by decide +kernel)).trans Data.table_zero
  have ht2 : Data.gen3 * Data.gen3 = Data.m5 :=
    step ((0, 0), 2) 3 (by decide +kernel)
  have ht3 : Data.m5 * Data.gen3 = 1 :=
    (step ((0, 0), 5) 3 (by decide +kernel)).trans Data.table_zero
  have hxt : Data.gen0 * Data.gen3 = Data.gen3 * Data.gen0 :=
    (step ((1, 0), 0) 3 (by decide +kernel)).trans
      (step ((0, 0), 2) 0 (by decide +kernel)).symm
  refine ⟨?_, ?_, ?_⟩
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, hgen]
    change Data.gen0 ^ 3 = 1
    simpa only [pow_succ, pow_zero, one_mul] using (congrArg (· * Data.gen0) hx2).trans hx3
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, hgen]
    change Data.gen3 ^ 3 = 1
    simpa only [pow_succ, pow_zero, one_mul] using (congrArg (· * Data.gen3) ht2).trans ht3
  · change _ * _ = _ * _
    apply Units.ext
    change (linearGenerators 0 : Mat) * (linearGenerators 3 : Mat) =
      (linearGenerators 3 : Mat) * (linearGenerators 0 : Mat)
    rw [hgen, hgen]
    exact hxt

end ONan.E9A4


namespace ONan.ThreeCoverLocalLifts
open Theory.SpecificGroups.E9A4 (Source Coord next homOfTransitions)

private def word (i : Fin 4) : Cover.linearSubgroup :=
  E9A4.basis
    ⟨linearA, Subgroup.subset_closure (by simp)⟩
    ⟨linearB, Subgroup.subset_closure (by simp)⟩ i

private theorem word_coe (i : Fin 4) : (word i).val = E9A4.linearGenerators i := by
  exact E9A4.map_basis Cover.linearSubgroup.subtype _ _ i

private theorem word_project (i : Fin 4) : Cover.projection (word i) = E9A4.generators i := by
  apply Subtype.ext
  change Matrix.ProjGenLinGroup.mk (word i).val = _
  rw [word_coe]
  exact E9A4.project_linearGenerators i

private theorem hom_generators
    (hnext : ∀ c i, E9A4.normalForm (next c i) =
      E9A4.normalForm c * E9A4.generators i) (i : Fin 4) :
    homOfTransitions E9A4.generators hnext
      (Theory.SpecificGroups.E9A4.generators i) = E9A4.generators i := by
  have hs : Theory.SpecificGroups.E9A4.generators i =
      Theory.SpecificGroups.E9A4.sourceForm (next ((0, 0), 0) i) := by
    simpa only [show Theory.SpecificGroups.E9A4.sourceForm ((0, 0), 0) = 1 from rfl,
      one_mul] using (Theory.SpecificGroups.E9A4.next_spec ((0, 0), 0) i).symm
  change Theory.SpecificGroups.E9A4.candidate E9A4.generators _ = _
  rw [hs, Theory.SpecificGroups.E9A4.candidate_sourceForm]
  exact (hnext ((0, 0), 0) i).trans (one_mul _)

/-- Transfer the actual first cubic word and three-cycle of the linear model
into a compatible central cover, and construct the lifted normal four-group.
The matrix realization, table and compatible lift must still be supplied. -/
public theorem exists_local_lift_of_linear_lift
    {G : Type*} [Group G] [Finite G]
    (hZ : IsPGroup 3 (Subgroup.center G))
    (e : G ⧸ Subgroup.center G ≃* Model)
    (F : Cover.linearSubgroup →* G)
    (hF : (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G))).comp F =
      Cover.projection)
    (hgen : ∀ i, (E9A4.linearGenerators i : E9A4.Mat) = E9A4.Data.generatorMatrix i)
    (htable : ∀ c i, E9A4.Data.table c * E9A4.Data.generatorMatrix i =
      E9A4.Data.scalar c i • E9A4.Data.table (next c i))
    (hnext : ∀ c i, E9A4.normalForm (next c i) =
      E9A4.normalForm c * E9A4.generators i)
    (hsep : Function.Injective E9A4.normalForm) :
    ∃ (Q : Subgroup G) (f : Multiplicative (ZMod 3 × ZMod 3) →* G),
      Q ≠ ⊥ ∧ IsPGroup 2 Q ∧
        Function.Injective ((QuotientGroup.mk' (Subgroup.center G)).comp f) ∧
        ∀ a, f a ∈ Subgroup.normalizer (Q : Set G) := by
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center G := by
    ext a
    change e (QuotientGroup.mk' (Subgroup.center G) a) = 1 ↔ a ∈ Subgroup.center G
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff a
  let j := homOfTransitions E9A4.generators hnext
  have hj : Function.Injective j :=
    Theory.SpecificGroups.E9A4.homOfTransitions_injective E9A4.generators hnext hsep
  obtain ⟨hx, ht, hxt⟩ := E9A4.linear_cubic_pair_of_matrix_table hgen htable
  have hwx : (word 0) ^ 3 = 1 := by
    apply Subtype.ext
    change (word 0).val ^ 3 = 1
    rw [word_coe]
    exact hx
  have hwt : (word 3) ^ 3 = 1 := by
    apply Subtype.ext
    change (word 3).val ^ 3 = 1
    rw [word_coe]
    exact ht
  have hwxt : Commute (word 0) (word 3) := by
    change _ * _ = _ * _
    apply Subtype.ext
    change (word 0).val * (word 3).val = (word 3).val * (word 0).val
    rw [word_coe, word_coe]
    exact hxt.eq
  have hpw (i : Fin 4) : π (F (word i)) = j (Theory.SpecificGroups.E9A4.generators i) := by
    rw [show π (F (word i)) = Cover.projection (word i) from DFunLike.congr_fun hF _,
      word_project]
    exact (hom_generators hnext i).symm
  obtain ⟨Q, f, hQne, hQp, hfi, hn⟩ :=
    Theory.SpecificGroups.E9A4.local_lift_of_commuting_cubic_lifts π hπ
      (by rw [hker]) (hker.symm ▸ hZ) j hj (F (word 0)) (F (word 3))
      (by rw [← map_pow, hwx, map_one]) (by rw [← map_pow, hwt, map_one])
      (hwxt.map F) (hpw 0) (hpw 3)
  refine ⟨Q, f, hQne, hQp, ?_, hn⟩
  intro a b hab
  apply hfi
  exact congrArg e hab

end ONan.ThreeCoverLocalLifts
