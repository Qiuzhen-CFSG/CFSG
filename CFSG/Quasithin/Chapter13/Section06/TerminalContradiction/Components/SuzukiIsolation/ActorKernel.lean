module
public import Theory.GroupTheory.GeneralizedFitting.MovedComponent
public import Theory.GroupTheory.GeneralizedFitting.NormalQuasisimpleImage
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The full actor kernel for two normal factors

When F(G)=1 and F*(G)=K D, simultaneous centralization of K and D is
trivial. Thus the kernel of D-conjugation on any subgroup A of G embeds
in Aut(K). The actor is an actual subgroup of G; no lift through a
two-core quotient is assumed. The centralizer of D also has generalized
Fitting subgroup K, provided K is quasisimple and commutes with D.

Source: the generalized Fitting argument in Aschbacher–Smith13.6.27,
printed p.934, applied before component uniqueness.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.ActorKernel
variable {G : Type*} [Group G] [Finite G]

/-- Trivial Fitting makes the generalized Fitting subgroup centerless
and gives a trivial ambient centralizer. -/
theorem centerless_of_fitting_bot (hf : fittingSubgroup G = ⊥) :
    centralizer (generalizedFitting G : Set G) = ⊥ ∧
      center (generalizedFitting G) = ⊥ := by
  have hc : centralizer (generalizedFitting G : Set G) = ⊥ :=
    le_bot_iff.mp (centralizer_generalizedFitting_le_fitting.trans hf.le)
  refine ⟨hc, le_bot_iff.mp ?_⟩
  intro x hx
  have hm : (x : G) ∈ centralizer (generalizedFitting G : Set G) := by
    intro y hy
    exact congrArg Subtype.val ((mem_center_iff.mp hx) ⟨y, hy⟩)
  rw [hc] at hm
  exact Subtype.ext hm

/-- Conjugation on K restricted to the actual kernel of D-conjugation. -/
noncomputable def action (K D A : Subgroup G) [K.Normal] [D.Normal] :
    ((MulAut.conjNormal : G →* MulAut D).comp A.subtype).ker →* MulAut K :=
  (MulAut.conjNormal : G →* MulAut K).comp
    (A.subtype.comp ((MulAut.conjNormal : G →* MulAut D).comp A.subtype).ker.subtype)

/-- The original actor's D-kernel embeds in the automorphisms of K. -/
theorem action_injective (K D A : Subgroup G) [K.Normal] [D.Normal]
    (hf : fittingSubgroup G = ⊥) (hF : generalizedFitting G = K ⊔ D) :
    Function.Injective (action K D A) := by
  apply (action K D A).ker_eq_bot_iff.mp
  apply le_bot_iff.mp
  intro x hx
  have hk : ((x : A) : G) ∈ centralizer (K : Set G) := by
    rw [← MulAut.conjNormal_ker_eq_centralizer]
    exact hx
  have hd : ((x : A) : G) ∈ centralizer (D : Set G) := by
    rw [← MulAut.conjNormal_ker_eq_centralizer]
    exact x.property
  have hc : ((x : A) : G) ∈ centralizer (generalizedFitting G : Set G) := by
    rw [hF, sup_eq_closure, centralizer_closure]
    intro y hy
    exact hy.elim (hk y) (hd y)
  rw [(centerless_of_fitting_bot hf).1] at hc
  exact Subtype.ext (Subtype.ext hc)

/-- The exceptional factor is the generalized Fitting subgroup of the
Suzuki centralizer, with the literal subgroup inclusion retained. -/
theorem centralizer_generalizedFitting (K D : Subgroup G) [K.Normal]
    [IsQuasisimple K] (hKD : K ≤ centralizer (D : Set G))
    (hf : fittingSubgroup G = ⊥) (hF : generalizedFitting G = K ⊔ D) :
    generalizedFitting (centralizer (D : Set G)) =
      K.subgroupOf (centralizer (D : Set G)) := by
  let C := centralizer (D : Set G)
  let B := K.subgroupOf C
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hKD).symm
  apply generalizedFitting_eq_of_quasisimple_centralizer B
  apply le_bot_iff.mp
  intro x hx
  have hk : (x : G) ∈ centralizer (K : Set G) := by
    intro y hy
    exact congrArg Subtype.val (hx ⟨y, hKD hy⟩ hy)
  have hboth : (x : G) ∈ centralizer (generalizedFitting G : Set G) := by
    rw [hF, sup_eq_closure, centralizer_closure]
    intro y hy
    exact hy.elim (hk y) (x.property y)
  rw [(centerless_of_fitting_bot hf).1] at hboth
  exact Subtype.ext hboth

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.ActorKernel
