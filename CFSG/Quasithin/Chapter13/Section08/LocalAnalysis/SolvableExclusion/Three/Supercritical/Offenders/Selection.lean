module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Offenders.ModuleAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Offenders.PrimeCoreAction
public import CFSG.Quasithin.ChapterD.Section02.Defs

/-!
# Selecting the cubic offender in the actual odd-by-two subgroup

The quadratic actor Uγ* supplied by 13.8.8(2) lies in J = P*Uγ*. Restriction
to J preserves its exact ratio, so the global cubic minimum for J is at most
two. D.2.1's finite-minimum theorem supplies an inclusion-minimal actor at
that minimum. The faithful complement argument then proves that this actor
moves O_p(J); movement is not part of the selection hypothesis.

`D213PrimeRestriction` is the universal earlier-source implication D.2.13(1),
with a finite acting group, faithful finite binary module, global cubic
minimum, genuine Q-hat-star membership and nontrivial odd-core action.
Its proof remains owned by qt-d-02. The local application discharges every
one of those hypotheses. In particular Q(Uγ*) is not treated as Q-hat-star
membership, and Vα* is never substituted for the quadratic actor.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), D.2.1 and
D.2.13(1), printed pp.178 and 184–185, and 13.8.13, pp.950–951.
-/

@[expose] public section

universe u v
open Subgroup Representation.BinaryOffender
open CFSG.Quasithin.ChapterD
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Supercritical.Offenders

/-- The exact universal prime conclusion of D.2.13, retained as an
earlier-source input rather than asserted as a proved classification theorem. -/
def D213PrimeRestriction : Prop :=
  ∀ (K : Type u) [Group K] [Finite K]
    (W : Type v) [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) K W), Function.Injective ρ →
    cubicRatio ρ ≤ 2 → ∀ D : Subgroup K, D ∈ QhatStar ρ →
    ∀ p : ℕ, p.Prime → Odd p → ⁅pCore p K, D⁆ ≠ ⊥ → p = 3 ∨ p = 5

variable {K W : Type*} [Group K] [AddCommGroup W] [Module (ZMod 2) W]

/-- D.2.1's Q-membership survives restriction of the acting group. -/
theorem Q_subgroupOf (ρ : Representation (ZMod 2) K W) (J A : Subgroup K)
    (hAJ : A ≤ J) (hA : A ∈ Q ρ) : A.subgroupOf J ∈ Q (ρ.comp J.subtype) := by
  let _ := hA.1.2
  refine ⟨⟨?_, IsElementaryAbelian.subgroupOf hAJ⟩,
    quadratic_subgroupOf ρ J A hA.2.1, ?_⟩
  · intro he
    have hh := congrArg (Subgroup.map J.subtype) he
    rw [map_subgroupOf_eq_of_le hAJ, Subgroup.map_bot] at hh
    exact hA.1.1 hh
  · rw [actionRatio_subgroupOf ρ J A hAJ]
    exact hA.2.2

section Endpoint
variable {G : Type u} [Group G] [Finite G]
variable {E : Type v} [AddCommGroup E] [Module (ZMod 2) E]
variable {p : ℕ} {L L₁ T H M V Vα V₃ : Subgroup G}
variable [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- Select the required global-minimum cubic actor in P*Uγ* and prove,
after selection, that it moves the local odd prime core. -/
theorem exists_minimal_moving_endpoint
    (c : OddConstruction p H L₁ T M Vα)
    (e : CriticalGeometry.CriticalPair L T H V)
    (hUV : Source.UH H V₃ ≤ Source.VH H V) (h : H)
    (hα : e.Vgamma.map (MulAut.conj (h : G)).toMonoidHom = Vα)
    (hplace : Vα ≤ (L₁ ⊔ T).pCoreIn 2)
    (ρ : Representation (ZMod 2) (Source.Hstar H) E)
    (hQ : Source.starImage H (e.Ugamma V₃) ∈ Q ρ) :
    let J := Source.starImage H c.P ⊔ Source.starImage H (e.Ugamma V₃)
    ∃ D : Subgroup J, D ∈ QhatStar (ρ.comp J.subtype) ∧ ⁅pCore p J, D⁆ ≠ ⊥ := by
  dsimp only
  let J := Source.starImage H c.P ⊔ Source.starImage H (e.Ugamma V₃)
  have hA := Q_subgroupOf ρ J _ le_sup_right hQ
  have hbound : cubicRatio (ρ.comp J.subtype) ≤ 2 :=
    (Qhat_nonempty_iff _).mp ⟨_, hA.1, isCubic_of_isQuadratic hA.2.1, hA.2.2⟩
  obtain ⟨D, hD⟩ := (QhatStar_nonempty_iff _).mpr hbound
  let _ := hD.1.2.1.2
  exact ⟨D, hD, endpoint_join_primeCore_moved c e hUV h hα hplace D
    (IsElementaryAbelian.isPGroup 2 D) hD.1.2.1.1⟩

/-- The prime restriction in 13.8.13, with all local hypotheses of the
universal earlier D.2.13(1) implication proved on the restricted action. -/
theorem prime_restriction_of_Q [FiniteDimensional (ZMod 2) E]
    (hD213 : D213PrimeRestriction.{u, v})
    (c : OddConstruction p H L₁ T M Vα)
    (e : CriticalGeometry.CriticalPair L T H V)
    (hUV : Source.UH H V₃ ≤ Source.VH H V) (h : H)
    (hα : e.Vgamma.map (MulAut.conj (h : G)).toMonoidHom = Vα)
    (hplace : Vα ≤ (L₁ ⊔ T).pCoreIn 2)
    (ρ : Representation (ZMod 2) (Source.Hstar H) E) (hfaith : Function.Injective ρ)
    (hQ : Source.starImage H (e.Ugamma V₃) ∈ Q ρ) : p = 3 ∨ p = 5 := by
  let J := Source.starImage H c.P ⊔ Source.starImage H (e.Ugamma V₃)
  obtain ⟨D, hD, hm⟩ := exists_minimal_moving_endpoint c e hUV h hα hplace ρ hQ
  have hfaithJ : Function.Injective (ρ.comp J.subtype) :=
    hfaith.comp J.subtype_injective
  exact hD213 J E (ρ.comp J.subtype) hfaithJ hD.1.1 D hD p c.prime c.odd hm

end Endpoint
end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Supercritical.Offenders
end
