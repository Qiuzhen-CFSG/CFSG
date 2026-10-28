module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Residual.Actions.Natural
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Residual.Actions.RelativeKernel
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Assembly
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.LocalNormality

/-!
# Actions of the radical normalizer residual

The natural-module alternative supplies the irreducibility and commutator
identities used in Proposition 1.3.8, printed pp.512–513. The transfer module
also proves the commutator lifting argument and compares the actual residual,
local, Sylow-complement and omega actions. The theorem below assembles these
transfers with the nilpotent omega action and the relative kernel comparison,
covering every odd Fitting prime, including the defining prime.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1
open CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.RadicalActions
open CFSG.Quasithin.Chapter1.RadicalNormalizers

namespace CFSG.Quasithin.Chapter1.RadicalNormalizers

universe u

variable {G : Type u} [Group G] [Finite G]

/-- The nilpotent A.3.6 branch supplies the quaternion image needed by the
cross-prime kernel comparison.  The action is the actual omega--Frattini
action on the specified Sylow subgroup of the actual component. -/
private theorem quaternion_image_of_A36_nilpotent
    {𝒦 : GroupClass.{u}}
    {E : Type u} [Group E] [Finite E]
    (hE : IsSQTK 𝒦 E) (hO : pCore 2 E = ⊥)
    {C : Subgroup E} (hC : C.IsCComponent)
    (hnil : A36Nilpotent C) (hcommon : A36Common C)
    {r : ℕ} [Fact r.Prime] (hr : Odd r)
    (hd : r ∣ Nat.card (fittingSubgroup C)) (S : Sylow 2 C) :
    ∃ e : QuaternionGroup 2 →*
      ((omegaFrattiniAction r C).comp (S : Subgroup C).subtype).range,
      Function.Injective e := by
  exact RadicalActions.Nilpotent.nilpotent_sylow_actions hE hO hC hnil hcommon hr hd S |>.2

/-- For every odd prime factor of the Fitting subgroup, the residual
normalizer has the source commutator and irreducibility properties.  The
defining prime uses the Frattini factorization directly; distinct primes use
the actual nilpotent omega action and its relative kernel comparison. -/
theorem XiP_Y_actions_of_A36
    {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Conclusion C)
    (hA38 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → C.Normal ∨ IsQuasisimple C)
    {T L : Subgroup G} (hL : L ∈ LStar G T)
    (hQ : IsSQTK 𝒦 ((L ⊔ T : Subgroup G) ⧸ pCore 2 (L ⊔ T : Subgroup G)))
    (hn : ¬ IsQuasisimple (XiQuotient L))
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hdp : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    ∀ q : ℕ, q.Prime → Odd q →
      q ∣ Nat.card (fittingSubgroup (XiQuotient L)) →
      ⁅XiP q L, normalizerResidual L (radicalCore p L T)⁆ = XiP q L ∧
      ∀ A : Subgroup (XiFrattiniQuotient (XiP q L)),
        (∀ y : normalizerResidual L (radicalCore p L T), ∀ a ∈ A,
          xiFrattiniAction _ _ (Y_normalizes_XiP p q L T) y a ∈ A) →
          A = ⊥ ∨ A = ⊤ := by
  have hT : T ≤ normalizer (L : Set G) :=
    radicalLocal_invariant_of_A38 hA38 hL.1 hQ hn
  have hQuaternion : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Nilpotent C → A36Common C →
      ∀ (r : ℕ) [Fact r.Prime], Odd r →
        r ∣ Nat.card (fittingSubgroup C) → ∀ S : Sylow 2 C,
          ∃ e : QuaternionGroup 2 →*
            ((omegaFrattiniAction r C).comp (S : Subgroup C).subtype).range,
            Function.Injective e := by
    intro E _ _ hE hO C hC hnil hcommon r _ hr hd S
    exact quaternion_image_of_A36_nilpotent hE hO hC hnil hcommon hr hd S
  intro q hqprime hq hdq
  let _ : Fact q.Prime := ⟨hqprime⟩
  have hqshape := XiP_oddQuotient_of_A36 hA36 hL.1 hQ hn hq hdq
  have hirr : ∀ A : Subgroup (XiFrattiniQuotient (XiP q L)),
      (∀ l : L, ∀ a ∈ A,
        xiFrattiniAction L (XiP q L) (XiP_invariant q L.le_normalizer) l a ∈ A) →
        A = ⊥ ∨ A = ⊤ := by
    let P : Sylow q (XiP q L) := Classical.arbitrary _
    exact L_irreducible_of_normalizer_irreducible q hq L P
      (XiP_normalizer_irreducible_of_A36 hA36 hL.1 hQ hn hq hdq P)
  by_cases hqp : q = p
  · subst q
    exact XiP_Y_actions_of_L_irreducible p L T hL.1 hT hqshape.2 hirr
  · have hker := sectionCentralizer_le_cross_frattiniAction_ker_of_A36
      hA36 hQuaternion hL.1 hQ hn hT hp hq (fun h => hqp h.symm) hdp hdq
    exact XiP_Y_actions_of_relative_kernel p q L T hL.1 hT hqshape.2 hker hirr

end CFSG.Quasithin.Chapter1.RadicalNormalizers
