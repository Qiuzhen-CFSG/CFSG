module

public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Ambient
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Transport
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Generation
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.PairQuotients
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.PartitionStructure

/-!
# Assembly of the M₂₂ local pair from concrete geometry

The marked pair stabilizer and hexad-partition stabilizer generate both M₂₂
and its full design automorphism group. Four intrinsic two-core quotient
isomorphisms and a common Sylow subgroup in each model therefore give the
local pair for any finite group with a normal, centralizer-free M₂₂ subgroup.
The ambient reduction uses the proved coverage of all abstract automorphisms;
Sylow conjugacy then places the pair over the prescribed Sylow subgroup.

The five-hexad and three-pair actions identify the intrinsic two-core
quotients, and the intersection orders give the common Sylow subgroups.
The final existence theorem discharges all six inputs of the intermediate
conditional assembly, including the inner-intersection quotients in the
outer-extension case.

Source: Aschbacher–Smith E.4.3(2), combined manuscript of 1 March 2004,
printed pp. 241–242 (PDF pp. 252–253).
-/

@[expose] public section
namespace Sporadic.Mathieu.M22ValueBound.Concrete
open Subgroup

/-- Quotient data turn the fixed inner geometry into the required pair. -/
noncomputable def innerPairOfQuotients (U : Sylow 2 M22)
    (hU : (U : Subgroup M22) ≤ first ⊓ second)
    (e₁ : (first ⧸ pCore 2 first) ≃* Equiv.Perm (Fin 5))
    (e₂ : (second ⧸ pCore 2 second) ≃* Equiv.Perm (Fin 3)) :
    InnerCompatiblePair U ⊤ where
  first := first
  second := second
  sylow_le_first := hU.trans inf_le_left
  sylow_le_second := hU.trans inf_le_right
  generate := first_sup_second
  firstQuotient := e₁
  secondQuotient := e₂
  firstInnerQuotient := (coreQuotientEquiv (MulEquiv.subgroupCongr (inf_top_eq _))).trans e₁
  secondInnerQuotient := (coreQuotientEquiv (MulEquiv.subgroupCongr (inf_top_eq _))).trans e₂

/-- The outer pair keeps the intrinsic quotients of both inner intersections. -/
noncomputable def outerPairOfQuotients (U : Sylow 2 m22DesignAut)
    (hU : (U : Subgroup m22DesignAut) ≤ outerFirst ⊓ outerSecond)
    (e₁ : (first ⧸ pCore 2 first) ≃* Equiv.Perm (Fin 5))
    (e₂ : (second ⧸ pCore 2 second) ≃* Equiv.Perm (Fin 3))
    (f₁ : (outerFirst ⧸ pCore 2 outerFirst) ≃* Equiv.Perm (Fin 5))
    (f₂ : (outerSecond ⧸ pCore 2 outerSecond) ≃* Equiv.Perm (Fin 3)) :
    InnerCompatiblePair U inner where
  first := outerFirst
  second := outerSecond
  sylow_le_first := hU.trans inf_le_left
  sylow_le_second := hU.trans inf_le_right
  generate := outerFirst_sup_outerSecond
  firstQuotient := f₁
  secondQuotient := f₂
  firstInnerQuotient := (coreQuotientEquiv firstInnerEquiv).trans e₁
  secondInnerQuotient := (coreQuotientEquiv secondInnerEquiv).trans e₂

variable {X : Type*} [Group X] [Finite X]

/-- The two concrete ambient cases suffice for every faithful almost simple extension. -/
theorem nonempty_innerCompatiblePair_of_models
    (hin : ∀ U : Sylow 2 M22, Nonempty (InnerCompatiblePair U ⊤))
    (hout : ∀ U : Sylow 2 m22DesignAut, Nonempty (InnerCompatiblePair U inner))
    (S : Subgroup X) [S.Normal] (hc : centralizer (S : Set X) = ⊥)
    (e : S ≃* M22) (T : Sylow 2 X) : Nonempty (InnerCompatiblePair T S) := by
  rcases ambient_equiv_alternatives S hc e with ⟨hS, ⟨f⟩⟩ | ⟨f, hf⟩
  · apply nonempty_innerCompatiblePair_of_equiv f
    rw [hS, Subgroup.map_top_of_surjective _ f.surjective]
    exact hin _
  · apply nonempty_innerCompatiblePair_of_equiv f
    rw [hf]
    exact hout _

/-- Conditional assembly from four concrete quotient isomorphisms and common
Sylow subgroups. The concrete geometry theorems must discharge all six inputs. -/
theorem nonempty_innerCompatiblePair_of_local_data
    (hin : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ first ⊓ second)
    (hout : ∃ U : Sylow 2 m22DesignAut,
      (U : Subgroup m22DesignAut) ≤ outerFirst ⊓ outerSecond)
    (e₁ : (first ⧸ pCore 2 first) ≃* Equiv.Perm (Fin 5))
    (e₂ : (second ⧸ pCore 2 second) ≃* Equiv.Perm (Fin 3))
    (f₁ : (outerFirst ⧸ pCore 2 outerFirst) ≃* Equiv.Perm (Fin 5))
    (f₂ : (outerSecond ⧸ pCore 2 outerSecond) ≃* Equiv.Perm (Fin 3))
    (S : Subgroup X) [S.Normal] (hc : centralizer (S : Set X) = ⊥)
    (e : S ≃* M22) (T : Sylow 2 X) : Nonempty (InnerCompatiblePair T S) := by
  obtain ⟨U, hU⟩ := hin
  obtain ⟨V, hV⟩ := hout
  apply nonempty_innerCompatiblePair_of_models ?_ ?_ S hc e T
  · intro W
    exact nonempty_innerCompatiblePair_of_sylow W U ⊤ (innerPairOfQuotients U hU e₁ e₂)
  · intro W
    exact nonempty_innerCompatiblePair_of_sylow W V inner
      (outerPairOfQuotients V hV e₁ e₂ f₁ f₂)

/-- Every finite group with a normal, centralizer-free copy of M₂₂ has two
overgroups of the prescribed Sylow two-subgroup which generate the group.
Their intrinsic two-core quotients, and those of their intersections with
the normal M₂₂ subgroup, are respectively S₅ and S₃. -/
theorem nonempty_innerCompatiblePair
    (S : Subgroup X) [S.Normal] (hc : centralizer (S : Set X) = ⊥)
    (e : S ≃* M22) (T : Sylow 2 X) : Nonempty (InnerCompatiblePair T S) :=
  nonempty_innerCompatiblePair_of_local_data
    exists_sylow_le_first_inf_second exists_sylow_le_outerFirst_inf_outerSecond
    firstQuotientEquiv secondQuotientEquiv outerFirstQuotientEquiv outerSecondQuotientEquiv
    S hc e T

end Sporadic.Mathieu.M22ValueBound.Concrete
