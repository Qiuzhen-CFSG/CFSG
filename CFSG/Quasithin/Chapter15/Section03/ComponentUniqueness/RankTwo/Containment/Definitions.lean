module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Definitions
public import CFSG.Quasithin.ClassicalModels
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# The residual factors in 15.3.39--40

The component factor is `O²(Y₊ ∩ L)` and the centralizing factor is
`O²(C_{Y₊}(L))`. The same centralizing-factor construction gives the actor
associated with the other definite plane. These are actual subgroup
residuals. For finite groups their index definition agrees with the
p-group-quotient definition, proving their 2-perfectness.

`componentOrbit L S`, imported from component calculus, is the join of the
actual S-conjugates of L. The rank-one alternatives below use concrete
projective classical-group equivalences, and `planeAction` is conjugation.
No containment, model restriction, or product decomposition is asserted.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.12 and 15.3.37--40, printed pp.1124--1125 and 1135--1138.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo

open Subgroup

variable {G : Type*} [Group G]

/-- The source's `Y_L`, also denoted `X` in 15.3.39. -/
noncomputable def componentFactor (Yplus L : Subgroup G) : Subgroup G :=
  Stellmacher.twoResidualAmbient (Yplus ⊓ L)

/-- The source's `Y_C`; for `L = V₂` this is `Y₁` in 15.3.39. -/
noncomputable def centralizingFactor (Yplus L : Subgroup G) : Subgroup G :=
  Stellmacher.twoResidualAmbient (Yplus ⊓ centralizer (L : Set G))

/-- The concrete model list in 15.3.37(2), including the field restrictions. -/
def RankOneAlternative (L : Subgroup G) : Prop :=
  (∃ n : ℕ, 0 < n ∧ Even n ∧ ClassicalGroup.IsPSL L 2 (2 ^ n)) ∨
  (∃ n : ℕ, 0 < n ∧ Even n ∧ ClassicalGroup.IsPSU L 3 (2 ^ n)) ∨
  ClassicalGroup.IsPSL L 3 2

/-- The actual conjugation action on a normalized plane. -/
def planeAction (H W : Subgroup G) (h : H ≤ normalizer (W : Set G)) :
    H →* MulAut W :=
  W.normalizerMonoidHom.comp (Subgroup.inclusion h)

theorem componentFactor_le (Yplus L : Subgroup G) : componentFactor Yplus L ≤ L :=
  (map_subtype_le _).trans inf_le_right

theorem centralizingFactor_le (Yplus L : Subgroup G) :
    centralizingFactor Yplus L ≤ centralizer (L : Set G) :=
  (map_subtype_le _).trans inf_le_right

private theorem twoResidualSubgroup_eq_pResidual [Finite G] (H : Subgroup G) :
    Stellmacher.twoResidualSubgroup H = pResidual 2 H := by
  unfold Stellmacher.twoResidualSubgroup pResidual
  congr 1
  ext N
  constructor
  · rintro ⟨hn, k, hk⟩
    refine ⟨hn, ?_⟩
    exact IsPGroup.iff_card.mpr ⟨k, by simpa only [Subgroup.index_eq_card] using hk⟩
  · rintro ⟨hn, hp⟩
    refine ⟨hn, ?_⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    exact ⟨k, by simpa only [Subgroup.index_eq_card] using hk⟩

private theorem twoResidualAmbient_isPPerfect [Finite G] (H : Subgroup G) :
    IsPPerfect 2 (Stellmacher.twoResidualAmbient H) := by
  rw [Stellmacher.twoResidualAmbient, twoResidualSubgroup_eq_pResidual]
  exact (Subgroup.isPPerfect_pResidual 2).of_surjective
    (H.subtype.subgroupMap _) (H.subtype.subgroupMap_surjective _)

/-- The component factor is genuinely a two-residual. -/
theorem componentFactor_isPPerfect [Finite G] (Yplus L : Subgroup G) :
    IsPPerfect 2 (componentFactor Yplus L) :=
  twoResidualAmbient_isPPerfect _

/-- Both centralizer actors are genuinely two-residuals. -/
theorem centralizingFactor_isPPerfect [Finite G] (Yplus L : Subgroup G) :
    IsPPerfect 2 (centralizingFactor Yplus L) :=
  twoResidualAmbient_isPPerfect _

end CFSG.Quasithin.Chapter15.Section03.RankTwo
