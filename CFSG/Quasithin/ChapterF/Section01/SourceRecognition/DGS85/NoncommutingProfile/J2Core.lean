module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.Basic
public import CFSG.Quasithin.ChapterF.Section01.SourceLocalResidual
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.HallJanko.Assembly
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.CoverSquareOrbit

/-!
# The order-32 core in the Hall--Janko source alternative

A raw parabolic equivalence to the concrete Hall--Janko amalgam identifies
its first parabolic with the perfect involution centralizer. In a genuine
F.1.1 pair the quotient of a parabolic by its original local factor is
solvable. Thus that original factor is the whole first parabolic, and its
intrinsic two-core is the concrete quaternion--dihedral radical of order 32.
The equivalences below retain the original inclusion and the full Borel.

This supplies the mixed A5/S3 consumer of the J2 alternative of DGS (10.9).
It takes the raw parabolic equivalence explicitly: the recognition from
Hypothesis B-prime and D_alpha = Z_alpha remains the Chapter 10 obligation.
No compatibility of the two overlap maps, ambient completion recognition,
or restoration from a reduced pair to an original pair is asserted.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
printed pp.162--163, (10.9); Aschbacher--Smith F.1.1, F.1.3 and F.1.12(I)(10),
printed pp.259--263. The concrete radical and perfection proofs are reused
from the existing ATLAS degree-100 Hall--Janko development.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open GreenBook
open Sporadic.LeechRelated.J2.ExceptionalParabolics

variable {P : Type*} [Group P]

/-- Restrict the given endpoint marking to its intrinsic core and the actual model radical. -/
noncomputable def j2FirstCoreEquiv
    (e : P ≃* HallJanko.j2Model.toMarking.P 0) :
    pCore 2 P ≃* FirstParabolic.radical := by
  have ep : HallJanko.j2Model.toMarking.P 0 = Seed.l₁ := HallJanko.j2Model_P_zero
  let f := e.trans (MulEquiv.subgroupCongr ep)
  exact ((f.subgroupMap (pCore 2 P)).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 2 f))).trans
      FirstParabolic.radicalCoreEquiv.symm

/-- The marked first endpoint has core order 32. -/
theorem j2_first_core_card (e : P ≃* HallJanko.j2Model.toMarking.P 0) :
    Nat.card (pCore 2 P) = 32 :=
  (Nat.card_congr (j2FirstCoreEquiv e).toEquiv).trans FirstParabolic.card_radical

/-- Perfection is transported from the literal Hall--Janko centralizer. -/
theorem j2_first_perfect (e : P ≃* HallJanko.j2Model.toMarking.P 0) :
    Group.IsPerfect P := by
  let := FirstParabolic.CoverSquareOrbit.l₁_isPerfect
  let f := e.trans (MulEquiv.subgroupCongr HallJanko.j2Model_P_zero)
  exact Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The solvable source quotient forces the original local factor to be the whole endpoint. -/
theorem source_local_eq_parabolic_of_j2_first
    (h : HypothesisF11 L S) (i : Fin 2)
    (e : parabolic L S i ≃* HallJanko.j2Model.toMarking.P 0) :
    L i = parabolic L S i := by
  let := j2_first_perfect e
  have hr := h.parabolic_residual_le_local i
  rw [solvableResidual_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hr
  exact le_antisymm (le_sup_left.trans le_sup_left) hr

/-- The endpoint marking restricted to the original source factor. -/
noncomputable def sourceJ2FirstEquiv (h : HypothesisF11 L S) (i : Fin 2)
    (e : parabolic L S i ≃* HallJanko.j2Model.toMarking.P 0) :
    L i ≃* HallJanko.j2Model.toMarking.P 0 :=
  (MulEquiv.subgroupCongr (source_local_eq_parabolic_of_j2_first h i e)).trans e

/-- The restricted map agrees with the original marking on the literal inclusion. -/
theorem sourceJ2FirstEquiv_apply (h : HypothesisF11 L S) (i : Fin 2)
    (e : parabolic L S i ≃* HallJanko.j2Model.toMarking.P 0) (x : L i) :
    sourceJ2FirstEquiv h i e x = e ⟨x, (show L i ≤ parabolic L S i from le_sup_left.trans le_sup_left) x.property⟩ := by
  rfl

/-- The original source core, rather than a substitute subgroup, is the model radical. -/
noncomputable def sourceJ2CoreEquiv (h : HypothesisF11 L S) (i : Fin 2)
    (e : parabolic L S i ≃* HallJanko.j2Model.toMarking.P 0) :
    pCore 2 (L i) ≃* FirstParabolic.radical :=
  j2FirstCoreEquiv (sourceJ2FirstEquiv h i e)

/-- The order-32 fact on the original F.1.1 local factor. -/
theorem source_j2_core_card (h : HypothesisF11 L S) (i : Fin 2)
    (e : parabolic L S i ≃* HallJanko.j2Model.toMarking.P 0) :
    Nat.card (pCore 2 (L i)) = 32 := by
  rw [source_local_eq_parabolic_of_j2_first h i e]
  exact j2_first_core_card e

/-- Both cores agree as subgroups of the original ambient group. -/
theorem source_j2_embedded_core_eq (h : HypothesisF11 L S) (i : Fin 2)
    (e : parabolic L S i ≃* HallJanko.j2Model.toMarking.P 0) :
    twoCore (L i) = twoCore (parabolic L S i) :=
  congrArg twoCore (source_local_eq_parabolic_of_j2_first h i e)

/-- Either selected source endpoint, with the whole Borel and its original inclusions. -/
theorem source_j2_core_of_parabolic_equiv
    (h : HypothesisF11 L S) (i : Fin 2)
    (e : RankTwoAmalgam.ParabolicEquiv
      (RankTwoAmalgam.ofSubgroups (parabolic L S i) (commonBorel L S)
        (parabolic L S (other i)) (commonBorel_le_parabolic i)
        (commonBorel_le_parabolic (other i))) HallJanko.j2Model.toMarking.amalgam) :
    L i = parabolic L S i ∧
      twoCore (L i) = twoCore (parabolic L S i) ∧
      Nat.card (pCore 2 (L i)) = 32 ∧
      Nat.card (commonBorel L S) = 384 ∧ MixedBorelModel (commonBorel L S) := by
  exact ⟨source_local_eq_parabolic_of_j2_first h i e.left,
    source_j2_embedded_core_eq h i e.left, source_j2_core_card h i e.left,
    (Nat.card_congr e.middle.toEquiv).trans HallJanko.card_j2Model_B,
    MixedBorelModel.hallJanko ⟨e.middle⟩⟩

/-- The mixed A5/S3 consumer: retain the original first factor and the Borel recognition witness. -/
theorem mixed_j2_original_core (K U S : Subgroup G)
    (h : HypothesisF11 ![K, U] S)
    (e : RankTwoAmalgam.ParabolicEquiv
      (RankTwoAmalgam.ofSubgroups (parabolic ![K, U] S 0) (commonBorel ![K, U] S)
        (parabolic ![K, U] S 1) (commonBorel_le_parabolic 0)
        (commonBorel_le_parabolic 1)) HallJanko.j2Model.toMarking.amalgam) :
    K = parabolic ![K, U] S 0 ∧
      twoCore K = twoCore (parabolic ![K, U] S 0) ∧
      Nat.card (pCore 2 K) = 32 ∧
      Nat.card (commonBorel ![K, U] S) = 384 ∧ MixedBorelModel (commonBorel ![K, U] S) :=
  source_j2_core_of_parabolic_equiv h 0 e

/-- The same consumer for the literal intersection amalgam used in generic recognition. -/
theorem mixed_j2_original_core_of_intersection (K U S : Subgroup G)
    (h : HypothesisF11 ![K, U] S)
    (e : RankTwoAmalgam.ParabolicEquiv
      (RankTwoAmalgam.ofSubgroups (parabolic ![K, U] S 0)
        (parabolic ![K, U] S 0 ⊓ parabolic ![K, U] S 1)
        (parabolic ![K, U] S 1) inf_le_left inf_le_right)
      HallJanko.j2Model.toMarking.amalgam) :
    K = parabolic ![K, U] S 0 ∧
      twoCore K = twoCore (parabolic ![K, U] S 0) ∧
      Nat.card (pCore 2 K) = 32 ∧
      Nat.card (commonBorel ![K, U] S) = 384 ∧ MixedBorelModel (commonBorel ![K, U] S) := by
  apply mixed_j2_original_core K U S h
  exact { left := e.left
          middle := (MulEquiv.subgroupCongr (lemma_F_1_3_6 h).symm).trans e.middle
          right := e.right }

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
