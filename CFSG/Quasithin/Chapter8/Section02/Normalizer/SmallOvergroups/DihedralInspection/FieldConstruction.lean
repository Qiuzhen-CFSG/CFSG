module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.DihedralInspection.Scalars
public import Theory.Representation.EndFieldRep
public import Theory.Representation.CentralizerField
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.RingTheory.LittleWedderburn

/-!
# The marked endomorphism field in the dihedral row

The field used in the last paragraph of Proposition 8.2.8 is the actual Schur
endomorphism field of the binary four-dimensional constituent J. This file
constructs that field and transports its module structure through a supplied
incoming marking of the literal section P/U. In particular, the field below
is End_(F₂ X)(J) itself; a field having the same cardinality is never used as
a substitute.

The constituent and the incoming marking are conclusions of the preceding
clauses of 8.2.8. They are consequently explicit hypotheses of the consumer
below. The resulting package supplies precisely the scalar premises required
by componentMultiplicityAction, while retaining the original X action.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), Proposition
8.2.8(1), printed p.719 (PDF p.736).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

public section
noncomputable section

open Subgroup
open scoped commutatorElement IsMulCommutative

namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups

variable {G J : Type*} [Group G] [Finite G]
  [AddCommGroup J] [Module (ZMod 2) J]
  {I U : Subgroup G}
  [(U.subgroupOf (I.pCoreIn 2)).Normal]
  [IsMulCommutative (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))]
  [Module (ZMod 2) (Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)))]

variable (ρ : Representation (ZMod 2) ((pResidual 2 I).map I.subtype) J)
  [Finite ((pResidual 2 I).map I.subtype)] [Finite J] [FiniteDimensional (ZMod 2) J]
  [Representation.IsIrreducible ρ]

noncomputable instance dihedralEndField : Field (Representation.IntertwiningMap ρ ρ) :=
  Representation.CentralizerField.endField ρ

instance dihedralEndFieldFinite : Finite (Representation.IntertwiningMap ρ ρ) :=
  Representation.CentralizerField.end_finite ρ

theorem endField_card (hEnd : Module.finrank (ZMod 2) (Representation.IntertwiningMap ρ ρ) = 4) :
    Nat.card (Representation.IntertwiningMap ρ ρ) = 16 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hEnd]
  norm_num


/-- A generator of the multiplicative group of the actual endomorphism field
    generates the field as a subring. -/
theorem exists_endField_generator :
    ∃ ζ : Representation.IntertwiningMap ρ ρ,
      Subring.closure ({ζ} : Set (Representation.IntertwiningMap ρ ρ)) = ⊤ := by
  letI := dihedralEndField ρ
  letI := dihedralEndFieldFinite ρ
  letI : Fintype (Representation.IntertwiningMap ρ ρ) := Fintype.ofFinite _
  obtain ⟨u, hu⟩ := IsCyclic.exists_monoid_generator
    (α := (Representation.IntertwiningMap ρ ρ)ˣ)
  refine ⟨u, ?_⟩
  apply le_antisymm le_top
  intro a ha
  by_cases haz : a = 0
  · simpa [haz] using
      (Subring.zero_mem (Subring.closure ({(u : Representation.IntertwiningMap ρ ρ)} :
        Set (Representation.IntertwiningMap ρ ρ))))
  let au : (Representation.IntertwiningMap ρ ρ)ˣ :=
    ⟨a, a⁻¹, mul_inv_cancel₀ haz, inv_mul_cancel₀ haz⟩
  obtain ⟨n, hn⟩ := hu au
  have hpow : (u : Representation.IntertwiningMap ρ ρ) ^ n = a := congrArg Units.val hn
  rw [← hpow]
  exact Subring.pow_mem (Subring.closure ({(u : Representation.IntertwiningMap ρ ρ)} :
      Set (Representation.IntertwiningMap ρ ρ)))
    (Subring.subset_closure (Set.mem_singleton (u : Representation.IntertwiningMap ρ ρ))) n

variable (hIC : I ≤ centralizer (U : Set G))
  (mark : Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) ≃ₗ[ZMod 2] ρ.asModule)
  (x : (pResidual 2 I).map I.subtype)

local instance constituentEndModule :
    Module (Representation.IntertwiningMap ρ ρ) ρ.asModule :=
  Module.compHom ρ.asModule (Representation.IntertwiningMap.equivAlgEnd ρ).toRingEquiv.toRingHom

/-- The actual field, a marked generator, and the transported module on the
literal quotient.  The marked operator is an element of the actual Schur
field through equivAlgEnd, so this compares the scalar action with
End_(F₂ X)(J) itself. -/
theorem endField_marking
    (ζ : Representation.IntertwiningMap ρ ρ)
    (hmark : ∀ v : Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)),
      mark (Additive.ofMul (pairResidualQuotientAction I U hIC x v.toMul)) =
        (Representation.IntertwiningMap.equivAlgEnd ρ ζ) (mark v))
    (hgenx : Subring.closure ({ζ} :
      Set (Representation.IntertwiningMap ρ ρ)) = ⊤)
    (hEnd : Module.finrank (ZMod 2) (Representation.IntertwiningMap ρ ρ) = 4) :
    Nat.card (Representation.IntertwiningMap ρ ρ) = 16 ∧
      Subring.closure ({ζ} : Set (Representation.IntertwiningMap ρ ρ)) = ⊤ ∧
      ∃ m : Module (Representation.IntertwiningMap ρ ρ)
          (Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))),
        ∀ v : Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)),
          Additive.ofMul (pairResidualQuotientAction I U hIC x v.toMul) =
            @SMul.smul _ _ m.toSMul ζ v := by
  let m : Module (Representation.IntertwiningMap ρ ρ)
      (Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))) :=
    (LinearEquiv.toAddEquiv mark).module (Representation.IntertwiningMap ρ ρ)
  refine ⟨endField_card ρ hEnd, hgenx, m, ?_⟩
  letI : Module (Representation.IntertwiningMap ρ ρ) ρ.asModule :=
    Module.compHom ρ.asModule (Representation.IntertwiningMap.equivAlgEnd ρ).toRingEquiv.toRingHom
  letI : Module (Representation.IntertwiningMap ρ ρ)
      (Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))) := m
  intro v
  apply (LinearEquiv.toAddEquiv mark).injective
  change mark (Additive.ofMul (pairResidualQuotientAction I U hIC x v.toMul)) =
    mark (ζ • v)
  rw [hmark]
  have hs : ζ • v = (LinearEquiv.toAddEquiv mark).symm
      ((Representation.IntertwiningMap.equivAlgEnd ρ ζ) (mark v)) := by
    rfl
  rw [hs]
  simp

/-! A concrete consumer of the scalar package. -/

variable {K : Subgroup G} [Group.IsPerfect K]

/-- Instantiate the F-linear component action and apply the source section
orders.  The module instance is the one returned by endField_marking (installed
by the caller); the scalar equality is consequently the literal equality on
P/U, not an equality after choosing coordinates. -/
theorem componentMultiplicityAction_consumer
    [Module (Representation.IntertwiningMap ρ ρ)
      (Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)))]
    (eD : (I ⧸ pCore 2 I) ≃* DihedralGroup 5)
    (hQI : K.pCoreIn 2 ≤ normalizer (I : Set G))
    (hKI : ⁅K, I⁆ ≤ K.pCoreIn 2)
    (hKU : K ≤ normalizer (U : Set G))
    (hUP : U ≤ I.pCoreIn 2)
    (hfull : I.pCoreIn 2 = ⁅I.pCoreIn 2, (pResidual 2 I).map I.subtype⁆ ⊔ U)
    (hIC : I ≤ centralizer (U : Set G))
    (hPP : ⁅I.pCoreIn 2, I.pCoreIn 2⁆ ≤ U)
    (ζ : Representation.IntertwiningMap ρ ρ)
    (hgenx : Subring.closure ({ζ} : Set (Representation.IntertwiningMap ρ ρ)) = ⊤)
    (x : (pResidual 2 I).map I.subtype)
    (hscalar : ∀ v : I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2),
      Additive.ofMul (pairResidualQuotientAction I U hIC x v) =
        ζ • Additive.ofMul v)
    (hcard : Nat.card (Representation.IntertwiningMap ρ ρ) = 16)
    (hA : Nat.card (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) = 2 ^ 8 ∨
      Nat.card (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) = 2 ^ 12) :
    ∃ α : K →* (Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) ≃ₗ[
      Representation.IntertwiningMap ρ ρ]
      Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))),
      α = componentMultiplicityAction K I U eD hQI hKI hKU hUP hfull hIC hPP
        ζ hgenx x hscalar ∧
      (Module.finrank (Representation.IntertwiningMap ρ ρ)
        (Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))) = 2 ∨
       Module.finrank (Representation.IntertwiningMap ρ ρ)
        (Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))) = 3) := by
  let α := componentMultiplicityAction K I U eD hQI hKI hKU hUP hfull hIC hPP
      ζ hgenx x hscalar
  refine ⟨α, rfl, ?_⟩
  exact multiplicity_finrank hcard hA

end CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups
