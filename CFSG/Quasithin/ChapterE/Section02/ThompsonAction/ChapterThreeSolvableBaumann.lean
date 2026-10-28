module

public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.SolvableBaumann
public import CFSG.Quasithin.Chapter3.Section01.E23Input
public import CFSG.Quasithin.Chapter3.Section01.BaumannSylow

/-!
# The solvable E.2.3 Sylow conclusion in the original qrc configuration

The original omega-center orbit supplies a reduced module moved by the
Thompson subgroup. Strong quasithinness bounds its solvable Thompson action
to one or two natural binary factors. The complete solvable Baumann theorem
therefore applies without a module chart or Sylow premise. Baumann heredity
then gives the literal O₂(M₀) Sylow conclusion used in 3.1.7.

Source: Aschbacher–Smith, E.2.3(2) and 3.1.7, printed pp.216–217 and 575–576
(1 March 2004 manuscript).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter3
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

/-- The original solvable qrc branch satisfies the intrinsic E.2.3 Sylow conclusion. -/
theorem QrcHypotheses.baumann_sylow_of_solvable
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE K G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype)
    (hsolv : Group.IsSolvable H) :
    let S := T.subtype h.right_mem.1.1.2
    Chapter1.IsSylowIn 2 (ChapterB.baumann (S : Subgroup H))
      (pResidual 2 H ⊔ ChapterB.baumann (S : Subgroup H)) := by
  obtain ⟨hsq, _, hp, hU, hj⟩ := h.e23_hypotheses hG hM hu hJ hZ
  let := hsolv
  exact (ChapterE.ThompsonAction.source_solvable_baumann_sylow_and_alpha _ hp _ hU hj
    (hsq.stronglyQuasithin 3 (by decide) (by decide)) inferInstance).1

/-- In the original solvable branch of 3.1.7, O₂(M₀) is Sylow in O²(H)O₂(M₀). -/
theorem QrcHypotheses.residual_sylow_of_solvable
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE K G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype)
    (hsolv : Group.IsSolvable H) :
    Chapter1.IsSylowIn 2 (M₀.pCoreIn 2)
      ((pResidual 2 H).map H.subtype ⊔ M₀.pCoreIn 2) :=
  h.residual_sylow_of_baumann_sylow hJ
    (h.baumann_sylow_of_solvable hG hM hu hJ hZ hsolv)

end CFSG.Quasithin.Chapter3
