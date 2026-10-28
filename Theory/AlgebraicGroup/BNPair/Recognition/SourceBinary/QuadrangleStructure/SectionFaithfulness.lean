module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnitaryLinearActions
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.ProfileActors

/-!
# Faithful full-root actions on the source Frattini sections

A root actor centralizing its complementary radical centralizes the
parabolic two-core. Local characteristic two places it in that core;
disjointness of the root actor and the radical then makes it trivial.
The residual-core identification gives O2(R) = 1. Burnside's Frattini
automorphism-kernel theorem consequently makes the action on the literal
radical quotient faithful as well.

The argument needs no perfectness, field size, or module irreducibility.
It applies in particular to the six-dimensional unitary section at q = 2.
The CFSG UnitaryCover adapters discharge self-centralization from the
original Hypothesis F.1.1 on the same marked quotient and both endpoints.
Faithfulness alone does not select SU3(2) over its projective quotient.

Source: Fong--Seitz I (5D), (6A)(c), pp.26--27,37; DGS (11.8),
pp.175--176; Burnside's basis theorem.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- Characteristic two makes the full root actor act faithfully on its radical. -/
theorem remainderRankOneAction_injective
    (i : Fin 2) (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple i}) :
      Set (Q.tits.standardParabolic {Q.simple i})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple i})) :
    Function.Injective (remainderRankOneAction Q split i hV) := by
  let D := Q.tits.standardParabolic {Q.simple i}
  have hUD : split.U ≤ D := split.U_le.trans (Q.tits.B_le_standardParabolic _)
  have hcoreU : D.pCoreIn 2 ≤ split.U := by
    have hh := pCoreIn_le_sylow D (split.sylow.subtype hUD)
    change D.pCoreIn 2 ≤ (split.U.subgroupOf D).map D.subtype at hh
    rwa [map_subgroupOf_eq_of_le hUD] at hh
  have hcoreV : D.pCoreIn 2 ≤ simpleRemainder Q split i :=
    parabolic_core_le_remainder Q split i hcoreU
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro r hr
  let rD : D := ⟨r,rankOne_le_parabolic Q split i r.property⟩
  have hrD : rD ∈ pCore 2 D := by
    apply hc
    rw [mem_centralizer_iff]
    intro v hv
    have hvV : (v : X ⧸ Q.D) ∈ simpleRemainder Q split i :=
      hcoreV (mem_map_of_mem D.subtype hv)
    have he := congrArg (fun a : MulAut (simpleRemainder Q split i) =>
      (a ⟨v,hvV⟩ : X ⧸ Q.D)) hr
    rw [remainderRankOneAction_apply] at he
    change (r : X ⧸ Q.D) * v * (r : X ⧸ Q.D)⁻¹ = v at he
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp he).symm
  have hrV := hcoreV (mem_map_of_mem D.subtype hrD)
  exact Subtype.ext ((disjoint_def.mp (RootLocalCover.rankOne_disjoint_radical Q split i))
    r.property ⟨hrV.1,hV hrV⟩)

/-- The full root actor has trivial two-core, including nonperfect endpoints. -/
theorem rankOne_twoCore_eq_bot
    (i : Fin 2) (s : RootReflection Q split i)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    pCore 2 (rankOne Q split i) = ⊥ := by
  let e := rankOneResidualCoreEquiv Q split i s hV
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [pCore_map_iso,Subgroup.map_bot]
  let A := primeToResidual 2 (Q.tits.standardParabolic {Q.simple i})
  let f := QuotientGroup.mk' (pCore 2 A)
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hk : IsPGroup 2 f.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have he := congrArg (Subgroup.map f) (f.comap_pCore_of_ker_isPGroup hf hk)
  rw [map_comap_eq_self_of_surjective hf] at he
  exact he.trans ((Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']))

/-- Burnside's kernel theorem preserves faithfulness on the literal Frattini section. -/
theorem remainderFrattiniAction_injective
    (i : Fin 2) (s : RootReflection Q split i)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (hc : centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple i}) :
      Set (Q.tits.standardParabolic {Q.simple i})) ≤
      pCore 2 (Q.tits.standardParabolic {Q.simple i})) :
    Function.Injective (remainderFrattiniAction Q split i hV) := by
  have hp := split.isTwo.to_le (show simpleRemainder Q split i ≤ split.U from inf_le_left)
  have hk : IsPGroup 2 (remainderFrattiniAction Q split i hV).ker :=
    (Subgroup.isPGroup_quotientAut_frattini_kernel hp).comap_of_injective
      (remainderRankOneAction Q split i hV) (remainderRankOneAction_injective Q split i hV hc)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  have hle : (remainderFrattiniAction Q split i hV).ker ≤ pCore 2 (rankOne Q split i) :=
    le_sSup ⟨inferInstance,hk⟩
  simpa only [rankOne_twoCore_eq_bot Q split i s hV] using hle

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
