module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieOvergroups.Transport
public import Theory.SpecificGroups.LieType.ExceptionalSplitParabolics
public import Theory.GroupTheory.PCoreOvergroup
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.Quasithin.EvenCharacteristic

/-!
# The remaining split-exceptional parabolic inputs and their B.1.13 application

The parabolics and radicals below are the root-generated subgroups of the
literal exceptional central quotients. Relative normality and the two-group
property put each radical in its parabolic's two-core. Its centralizer bound
makes that two-core self-centralizing. Exhaustive proper Sylow-overgroup
placement then passes characteristic two to the actual local intersection in
B.1.13, using subgroup equivalences and the specified model equivalence.

The two independent geometric inputs are left explicit: exhaustive placement,
and radical normality/two-group/centralizer control. Neither is proved by this
reduction. Final source assembly must produce both for F₄, E₆, E₇ and E₈.
Sources: GLS III, 2.6.4–2.6.7; Aschbacher–Smith B.1.13, printed p.74.
-/

@[expose] public section

noncomputable section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.SplitExceptional

open Subgroup Theory.GroupTheory ExceptionalSplit.Parabolics

variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [P.IsCrystallographic] [P.IsReduced] [P.IsRootSystem]
  (b : P.Base) [Fintype ι] [DecidableEq ι]
  (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- The precise remaining coverage input, on the original Sylow and its
literal conjugate image. The candidate parabolics are fixed root subgroups. -/
def SylowPlacement : Prop :=
  ∀ (S : Sylow 2 (ExceptionalSplit.Model P b F))
    (X : Subgroup (ExceptionalSplit.Model P b F)),
    (S : Subgroup (ExceptionalSplit.Model P b F)) ≤ X → X ≠ ⊤ →
      ∃ (g : ExceptionalSplit.Model P b F) (j : b.support),
        X.map (MulAut.conj g).toMonoidHom ≤ maximal P b F j

/-- The independent radical calculation, with normality and centralization
inside the parabolic, rather than normality in the whole exceptional group. -/
def RadicalControl : Prop :=
  ∀ j : b.support,
    ((radical P b F j).subgroupOf (maximal P b F j)).Normal ∧
    IsPGroup 2 (radical P b F j) ∧
    centralizer ((radical P b F j).subgroupOf (maximal P b F j) :
      Set (maximal P b F j)) ≤
        (radical P b F j).subgroupOf (maximal P b F j)

/-- The radical calculation implies the required two-core centralizer bound. -/
theorem parabolic_centralizer_twoCore_le (hR : RadicalControl P b F)
    (j : b.support) :
    centralizer (pCore 2 (maximal P b F j) : Set (maximal P b F j)) ≤
      pCore 2 (maximal P b F j) := by
  obtain ⟨hn, hp, hc⟩ := hR j
  have hr : (radical P b F j).subgroupOf (maximal P b F j) ≤
      pCore 2 (maximal P b F j) :=
    le_sSup ⟨hn, hp.comap_subtype⟩
  exact (centralizer_le hr).trans (hc.trans hr)

/-- Both geometric inputs give the complete bound on the literal model,
transported through an actual equivalence. -/
theorem properSylowFittingBound_of_geometry
    (hplace : SylowPlacement P b F) (hR : RadicalControl P b F)
    {A : Type*} [Group A] [Finite A] (e : A ≃* ExceptionalSplit.Model P b F) :
    ProperSylowFittingBound A := by
  apply properSylowFittingBound_of_equiv e
  intro S X hSX hX
  obtain ⟨g, j, hXP⟩ := hplace S X hSX hX
  let a := MulAut.conj g
  let T := S.mapSurjective (f := a.toMonoidHom) a.surjective
  let Y := X.map a.toMonoidHom
  have hTY : (T : Subgroup (ExceptionalSplit.Model P b F)) ≤ Y := map_mono hSX
  have hc := centralizer_pCore_le_of_sylow_le (T.subtype (hTY.trans hXP))
    (Y.subgroupOf (maximal P b F j)) (fun _ hx => hTY hx)
    (parabolic_centralizer_twoCore_le P b F hR j)
  have hcY : centralizer (pCore 2 Y : Set Y) ≤ pCore 2 Y :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hXP)).mp hc
  have hcX : centralizer (pCore 2 X : Set X) ≤ pCore 2 X :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (a.subgroupMap X)).mpr hcY
  rw [generalizedFitting_eq_pCore_of_selfCentralizing 2 hcX]
  exact le_sup_left

/-- The actual source consumer: the model equivalence and both independent
geometric inputs discharge the bound on L ∩ (K ∨ T). -/
theorem eq_component_of_geometry
    (hplace : SylowPlacement P b F) (hR : RadicalControl P b F)
    {G : Type*} [Group G] [Finite G]
    (K L : Subgroup G) (T : Sylow 2 G)
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal) (hKL : K ≤ L)
    (e : L ≃* ExceptionalSplit.Model P b F) : K = L :=
  eq_component_of_proper_sylow_fitting_bound K L T hL hLK hkind hK hKL
    (properSylowFittingBound_of_geometry P b F hplace hR e)

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.SplitExceptional

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.SplitExceptional

open Theory.AlgebraicGroup.StandardRootSystem
attribute [local instance] Classical.decEq

local instance : Fintype typeF4Roots := Fintype.ofFinite _
local instance : Fintype typeE6Roots := Fintype.ofFinite _
local instance : Fintype typeE7Roots := Fintype.ofFinite _
local instance : Fintype typeE8Roots := Fintype.ofFinite _

variable (F : Type*) [Field F] [Finite F] [CharP F 2]
  {A : Type*} [Group A] [Finite A]

/-- Conditional F4 application on its specified central quotient. Both
geometric premises remain to be supplied by the source assembly. -/
theorem properSylowFittingBound_f4_of_geometry
    (hplace : SylowPlacement typeF4RootPairing typeF4RootPairing_base F)
    (hR : RadicalControl typeF4RootPairing typeF4RootPairing_base F)
    (e : A ≃* ExceptionalSplit.F4 F) : ProperSylowFittingBound A :=
  properSylowFittingBound_of_geometry typeF4RootPairing typeF4RootPairing_base F
    hplace hR e

/-- Conditional E6 application on its specified central quotient. Both
geometric premises remain to be supplied by the source assembly. -/
theorem properSylowFittingBound_e6_of_geometry
    (hplace : SylowPlacement typeE6RootPairing typeE6RootPairing_base F)
    (hR : RadicalControl typeE6RootPairing typeE6RootPairing_base F)
    (e : A ≃* ExceptionalSplit.E6 F) : ProperSylowFittingBound A :=
  properSylowFittingBound_of_geometry typeE6RootPairing typeE6RootPairing_base F
    hplace hR e

/-- Conditional E7 application on its specified central quotient. Both
geometric premises remain to be supplied by the source assembly. -/
theorem properSylowFittingBound_e7_of_geometry
    (hplace : SylowPlacement typeE7RootPairing typeE7RootPairing_base F)
    (hR : RadicalControl typeE7RootPairing typeE7RootPairing_base F)
    (e : A ≃* ExceptionalSplit.E7 F) : ProperSylowFittingBound A :=
  properSylowFittingBound_of_geometry typeE7RootPairing typeE7RootPairing_base F
    hplace hR e

/-- Conditional E8 application on its specified central quotient. Both
geometric premises remain to be supplied by the source assembly. -/
theorem properSylowFittingBound_e8_of_geometry
    (hplace : SylowPlacement typeE8RootPairing typeE8RootPairing_base F)
    (hR : RadicalControl typeE8RootPairing typeE8RootPairing_base F)
    (e : A ≃* ExceptionalSplit.E8 F) : ProperSylowFittingBound A :=
  properSylowFittingBound_of_geometry typeE8RootPairing typeE8RootPairing_base F
    hplace hR e

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.SplitExceptional
