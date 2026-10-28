module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.FourGeometry.Core
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ZeroClosure.Normalization
public import Theory.SpecificGroups.BinaryLinear.AutomorphismTwoRank
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.FourCore
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.Five

/-!
# The degree-four second weak-closure bound on the chosen orbit

The compatible H.9 action transports the seven-dimensional core estimate
to the literal ambient automizer. Quotient-rank additivity gives core
corank at most one, contradicting E.3.32 and the reverse-normalizer
corank at least two. This discharges the finite geometric premise of
`doubledFour_globalW_gt_two_of_many_of_core_bound`.

The final theorem combines degrees four and five. Construction of the
compatible marked model and both first-stage branches remain with the
weak-closure assembly owner, qt-d-double-natural-weak-closure; the final
source exclusion is owned by qt-d-1222-double-natural.
Source: Aschbacher--Smith,12.1.10, printed p.794 (PDF p.811).
-/

public noncomputable section
open BinaryNaturalDual BinaryNaturalDual.FourActors BinaryLinear.OuterCyclic
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.FourGeometry
open Theory.GroupTheory Representation.BinaryOffender
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterH.NaturalDual
open BinaryNaturalDual.ModelOrbits
variable {K E : Type*} [Group K] [Finite K] [AddCommGroup E] [Module (ZMod 2) E]

/-- H.9.3 gives the dimension bound on the original source action. -/
theorem source_core_finrank (S : SourceSetup 4 K E) (I : Subgroup K)
    (hI : IsElementaryAbelian 2 I) (hr : 4 ≤ rank I) :
    7 ≤ Module.finrank (ZMod 2) (generatedCore (S.representation.comp I.subtype) 3) := by
  let : Finite (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2))) :=
    Finite.of_equiv K S.projective.toEquiv
  have hb : primeRank 2 K ≤ 4 :=
    (primeRank_equiv 2 S.projective).trans_le BinaryLinear.AutomorphismTwoRank.psl4_two_rank_le
  have hc : Nat.card I = 16 := le_antisymm
    ((primeRank_le_iff_elementary_card_le K).mp hb I hI)
    (Nat.pow_le_of_le_log Nat.card_pos.ne' hr)
  let A := I.map S.model.group.toMonoidHom
  let : IsElementaryAbelian 2 A := hI.map S.model.group.toMonoidHom
  have hA : Nat.card A = 16 :=
    (Subgroup.card_map_of_injective S.model.group.injective).trans hc
  have hd := (Submodule.equivMapOfInjective S.model.coordinates.toLinearMap
    S.model.coordinates.injective (generatedCore (S.representation.comp I.subtype) 3)).finrank_eq
  rw [S.core_map] at hd
  rw [hd]
  exact coordinate_core_finrank (AutomorphismModel.coordinateAction S.degree) A hA

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.FourGeometry

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure
open Theory.GroupTheory Representation.BinaryOffender
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterH.NaturalDual
variable {K : Type*} [Group K] [Finite K] {W : Subgroup K} [IsElementaryAbelian 2 W]

/-- The H.9.3 bound for the literal ambient automizer core used by E.3.32. -/
theorem four_core_corank_le_one
    (S : SourceSetup 4 (Automizer W) (Additive W))
    (hρ : S.representation = automizerRepresentation W)
    (I : Subgroup (Automizer W)) (hI : IsElementaryAbelian 2 I) (hr : 4 ≤ rank I) :
    subgroupCorank W (automizerDualCore W I 3) ≤ 1 := by
  let U := generatedCore ((automizerRepresentation W).comp I.subtype) 3
  have hdim : 7 ≤ Module.finrank (ZMod 2) U := by
    change 7 ≤ Module.finrank (ZMod 2)
      (generatedCore ((automizerRepresentation W).comp I.subtype) 3)
    rw [← hρ]
    exact FourGeometry.source_core_finrank S I hI hr
  let e : U ≃ automizerDualCore W I 3 := {
    toFun := fun u => ⟨u.val.toMul, (ZeroClosure.mem_core_iff I 3 u.val).mpr u.property⟩
    invFun := fun u => ⟨Additive.ofMul ⟨u.val, automizerDualCore_le W I 3 u.property⟩,
      (ZeroClosure.mem_core_iff I 3 _).mp u.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hcard : Nat.card (automizerDualCore W I 3) = 2 ^ Module.finrank (ZMod 2) U := by
    rw [← Nat.card_congr e, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hdimW : Module.finrank (ZMod 2) (Additive W) = 8 := by
    rw [S.model.coordinates.finrank_eq]
    norm_num [CoordinateSpace, BinaryNaturalDual.Space, BinaryLinear.OuterCyclic.Space, Module.finrank_prod]
  have hcardW : Nat.card W = 2 ^ 8 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    rw [Nat.card_congr (Additive.toMul : Additive W ≃ W), hdimW, Nat.card_zmod] at hh
    exact hh
  have hs := offender_corank_add
    (bot_le : (⊥ : Subgroup K) ≤ automizerDualCore W I 3) (automizerDualCore_le W I 3)
  simp only [subgroupCorank, Subgroup.relIndex_bot_left, hcard, hcardW,
    Nat.log_pow (by decide : 1 < 2)] at hs
  change Nat.log 2 ((automizerDualCore W I 3).relIndex W) ≤ 1
  omega

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure

open Subgroup Theory.GroupTheory Representation.BinaryOffender
open CFSG.Quasithin.ChapterE
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)

/-- The degree-four implication in 12.1.10, with the compatible actual action
as its only extra model premise. The finite core estimate is discharged. -/
theorem doubledFour_globalW_gt_two_of_many_of_model
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    B.MarkedAutomizerModel →
    1 < globalW (componentOrbit V (T : Subgroup G)) T →
    (6 : ℕ∞) ≤ globalR (componentOrbit V (T : Subgroup G)) →
    2 < globalW (componentOrbit V (T : Subgroup G)) T := by
  let := D.doubledOrbit_elementary h
  intro M hw hr
  apply D.doubledFour_globalW_gt_two_of_many_of_core_bound h hmany B _ hw hr
  exact four_core_corank_le_one M.setup M.representation_eq

/-- Both degree-four and degree-five second-stage branches for the original orbit.
The weak-closure owner must still construct the marked model. -/
theorem doubled_globalW_gt_two_of_many_of_model {n : ℕ}
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    B.MarkedAutomizerModel →
    1 < globalW (componentOrbit V (T : Subgroup G)) T →
    ((n + 2 : ℕ) : ℕ∞) ≤ globalR (componentOrbit V (T : Subgroup G)) →
    2 < globalW (componentOrbit V (T : Subgroup G)) T := by
  rcases B.degree with rfl | rfl
  · exact D.doubledFour_globalW_gt_two_of_many_of_model h hmany B
  · exact D.doubledFive_globalW_gt_two_of_many_of_model h hmany B

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
