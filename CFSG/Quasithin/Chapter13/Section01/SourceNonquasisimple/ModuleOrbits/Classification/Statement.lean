module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive.Source
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.SymmetricFive
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import CFSG.Quasithin.ChapterB.Section02.Thompson

/-!
# The four literal moved-module rows

This file is the interface between the source classification in 13.1.10 and
the orbit calculations in the rest of Section 01.  It deliberately records
the original subgroup `U = normalizerMoved L`, the original normalizer action,
and the quotient `L/O∞(L)`.  In particular, an abstract copy of a module is
not accepted as a replacement for the moved subgroup.

The four records below are output records.  Their model and module fields are
the source clauses of 13.1.10; they do not silently assert that those clauses
follow from a carrier tag.  `CommonMarking.of_source` supplies the action data proved in
13.1.8, retaining the authorized earlier Thompson movement premise.
These output types do not assert the four-way classification.

Source: Aschbacher--Smith, 13.1.8--10, printed pp.869--872.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02
open CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
open CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive
open CFSG.Quasithin.ChapterB.QuasisimpleSource
universe u v

variable {G : Type u} [Group G] [Finite G]

/-! ## The common literal action data -/

/-- The data shared by all four rows of 13.1.10.

`quotient` is the first-isomorphism map for the actual action of `L` on the
actual moved subgroup.  The `movement` field retains the earlier Thompson
movement conclusion, rather than replacing it with a stronger classification
hypothesis.
-/
structure CommonMarking (T : Sylow 2 G) (L : Subgroup G) where
  ambient_invariant : L ⊔ (T : Subgroup G) ≤ normalizer (L : Set G)
  invariant : L ⊔ (T : Subgroup G) ≤ normalizer (normalizerMoved L : Set G)
  actor : (L ⊔ (T : Subgroup G) : Subgroup G) →* MulAut (normalizerMoved L)
  actor_eq : actor = (action L).comp (inclusion ambient_invariant)
  movement : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆
  moved_ne_bot : normalizerMoved L ≠ ⊥
  moved_commutator : ⁅normalizerMoved L, L⁆ = normalizerMoved L
  component_kernel : (componentAction L).ker = solvableRadical L
  quotient : (L ⧸ solvableRadical L) ≃* componentImage L
  quotient_mk : ∀ l : L,
    (quotient (QuotientGroup.mk' (solvableRadical L) l) :
      MulAut (normalizerMoved L)) = componentAction L l
  component_model : ∃ p : ℕ, p.Prime ∧ 3 < p ∧
    ClassicalGroup.IsPSL (componentImage L) 2 p

namespace CommonMarking

variable {T : Sylow 2 G} {L : Subgroup G}

/-- The common records are constructed from the literal action lemmas.

The only earlier conclusion used here is the authorized Thompson movement
`hmove`; no model classification is used.
-/
def of_source
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆) :
    CommonMarking T L := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hM : L ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    sup_le L.le_normalizer hTL
  have hinv : L ⊔ (T : Subgroup G) ≤
      normalizer (normalizerMoved L : Set G) :=
    hM.trans (normalizer_le_normalizer_moved L)
  have hmoved := (normalizerMoved_commutator_and_card hL.1.1
    (faithful_maximal_normalizer_moved h.simpleQTKE hL hTL).2.1).1
  have hne := (faithful_maximal_normalizer_moved h.simpleQTKE hL hTL).2.1
  exact
    { ambient_invariant := hM
      invariant := hinv
      actor := (action L).comp (inclusion hM)
      actor_eq := by
        apply MonoidHom.ext
        intro a
        rfl
      movement := hmove
      moved_ne_bot := hne
      moved_commutator := hmoved
      component_kernel := componentAction_ker_eq_radical h hmany hL hn
      quotient := radicalEquivMovedImage h hmany hL hn
      quotient_mk := fun l => radicalEquivMovedImage_mk h hmany hL hn l
      component_model := moved_component_pslTwo h hmany hL hn }

@[simp] theorem quotient_mk_apply (d : CommonMarking T L) (l : L) :
    (d.quotient (QuotientGroup.mk' (solvableRadical L) l) :
      MulAut (normalizerMoved L)) = componentAction L l :=
  d.quotient_mk l

theorem actor_apply (d : CommonMarking T L)
    (a : (L ⊔ (T : Subgroup G) : Subgroup G))
    (u : normalizerMoved L) :
    d.actor a u = (action L (inclusion d.ambient_invariant a)) u := by
  rw [d.actor_eq]
  rfl

end CommonMarking

/-! ## The four source rows -/

/-- Case (1): the actual `L₂(4)` image and its natural module quotient.

The existential marking is the `AlternatingFive.Marking` from the literal
natural-module consumer.  Its `naturalCoordinates_kernel` and
`centralQuotientEquiv` fields identify the original `U/C_U(L)` map.
-/
structure PSLTwoFourMarking (T : Sylow 2 G) (L : Subgroup G) (W : Type v)
    [AddCommGroup W] [Module (ZMod 2) W] where
  common : CommonMarking T L
  image_model : ClassicalGroup.IsPSL (componentImage L) 2 4
  natural :
    CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive.Marking T L W

/-- Case (2): the genuine deleted permutation module for the actual `LT`.

The `component` field of `marking` is required to be the alternating image;
the source `S₅` action is not replaced by a carrier-level tag.
-/
structure SymmetricFiveRow (T : Sylow 2 G) (L : Subgroup G) where
  common : CommonMarking T L
  marking : CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.SymmetricFiveMarking T L

namespace PSLTwoFourMarking

variable {T : Sylow 2 G} {L : Subgroup G} {W : Type v}
  [AddCommGroup W] [Module (ZMod 2) W]

theorem natural_kernel_eq_radical (d : PSLTwoFourMarking T L W)
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    d.natural.component.ker = solvableRadical L :=
  d.natural.component_kernel_eq_radical h hmany hL hn

theorem central_quotient_kernel (d : PSLTwoFourMarking T L W) :
    d.natural.naturalCoordinates.ker =
      (centralizer (L : Set G)).subgroupOf (normalizerMoved L) :=
  d.natural.naturalCoordinates_kernel

end PSLTwoFourMarking

namespace SymmetricFiveRow

variable {T : Sylow 2 G} {L : Subgroup G}

theorem component_kernel_eq_radical (d : SymmetricFiveRow T L)
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    (d.marking.quotient.comp (inclusion
      (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left))).ker =
      solvableRadical L :=
  d.marking.component_kernel_eq_radical h hmany hL hn

end SymmetricFiveRow

/-- The component action on the literal elementary abelian subgroup `U`.

This is merely the binary representation attached to the actual image
`componentImage L`; it is used in cases (3) and (4) to state naturality on the
same `U`, rather than on a chosen isomorphic vector space.
-/
@[expose] def componentRepresentation
    {L : Subgroup G} [IsElementaryAbelian 2 (normalizerMoved L)] :
    Representation (ZMod 2) (componentImage L)
      (Additive (normalizerMoved L)) :=
  Representation.elementaryRepresentation (componentImage L).subtype

/-- Case (3): the actual `L₃(2)` image and one or two natural copies on `U`.

The range witness in `actual_component` is the literal image of
`componentAction`; it retains the quotient map from `CommonMarking`.
-/
structure LinearThreeMarking (T : Sylow 2 G) (L : Subgroup G)
    [IsElementaryAbelian 2 (normalizerMoved L)] where
  common : CommonMarking T L
  image_model : ClassicalGroup.IsPSL (componentImage L) 3 2
  copies : ∃ r : ℕ, 0 < r ∧ r ≤ 2 ∧
    IsRepeatedLinearNatural (componentRepresentation (L := L)) BinaryField.two 3 r

/-- Case (4): the rank-four `L₃(2)` row with central `Ω₁ Z(T)`.

`rank` is the repository's binary rank of an elementary abelian subgroup, and
the commutator equality is the literal source clause `[Ω₁ Z(T),L]=1`.
-/
structure LinearThreeRankFourMarking (T : Sylow 2 G) (L : Subgroup G)
    [IsElementaryAbelian 2 (normalizerMoved L)] where
  common : CommonMarking T L
  image_model : ClassicalGroup.IsPSL (componentImage L) 3 2
  rank_four : rank (normalizerMoved L) = 4
  omega_center_central :
    ⁅Stellmacher.omegaOneCenterAmbient (T : Subgroup G), L⁆ = ⊥

/-- The four literal alternatives in 13.1.10. -/
inductive FourWayMarking (T : Sylow 2 G) (L : Subgroup G) : Type (max (u + 1) (v + 1))
  | pslTwoFour {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
      (d : PSLTwoFourMarking T L W)
  | symmetricFive (d : SymmetricFiveRow T L)
  | linearThree [IsElementaryAbelian 2 (normalizerMoved L)]
      (d : LinearThreeMarking T L)
  | linearThreeRankFour [IsElementaryAbelian 2 (normalizerMoved L)]
      (d : LinearThreeRankFourMarking T L)

/-! ## Small, reusable source adapters -/

def symmetricFive_of_marking
    {T : Sylow 2 G} {L : Subgroup G}
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (d : CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.SymmetricFiveMarking T L) :
    FourWayMarking T L :=
    .symmetricFive
    { common := CommonMarking.of_source h hmany hL hn hmove
      marking := d }

def pslTwoFour_of_marking
    {T : Sylow 2 G} {L : Subgroup G}
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (hmodel : ClassicalGroup.IsPSL (componentImage L) 2 4)
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    (hmark : CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive.Marking T L W) :
    FourWayMarking T L :=
  .pslTwoFour
    { common := CommonMarking.of_source h hmany hL hn hmove
      image_model := hmodel
      natural := hmark }

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
