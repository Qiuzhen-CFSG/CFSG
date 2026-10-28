module

public import Theory.AlgebraicGroup.RootSystems.F4WeightAction.OrbitCoordinates
public import Theory.AlgebraicGroup.RootSystems.F4WeightAction.DualTwist
public import Theory.RingTheory.MonoidAlgebraOrbitSums.Functoriality
/-!
# Exceptional Frobenius on fundamental F4 orbit sums

The positive coroot parameters transform as (t₃²,t₂²,t₁,t₀). Their
character pullback is the integral exceptional map. Orbit reindexing and
Frobenius therefore give the four literal fundamental orbit-sum identities,
including the squared long-root entries. No character-separation or
Frobenius-compatibility premise is assumed.

Source: Steinberg (1963), §12.2.
-/

public noncomputable section
open scoped BigOperators Matrix
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Theory.MonoidAlgebraOrbitSums
namespace Theory.AlgebraicGroup.StandardRootSystem.F4WeightAction
open scoped F4WeightAction
local instance twistedCoordinatesWeylFinite : Finite Weyl := weylGroup_finite typeF4RootPairing

@[expose] def dualTwistHom : Lattice →* Lattice where
  toFun a := Multiplicative.ofAdd (dualTwist a.toAdd)
  map_one' := congrArg Multiplicative.ofAdd (map_zero dualTwist)
  map_mul' a b := congrArg Multiplicative.ofAdd (map_add dualTwist a.toAdd b.toAdd)

lemma dualTwistHom_injective : Function.Injective dualTwistHom := by
  intro a b h
  apply Multiplicative.toAdd.injective
  apply dualTwist_injective
  exact congrArg Multiplicative.toAdd h

lemma dualTwistHom_orbit (a : Lattice) :
    dualTwistHom '' MulAction.orbit Weyl a = MulAction.orbit Weyl (dualTwistHom a) := by
  have he := dualTwist_orbit a.toAdd
  ext b
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hm : dualTwist c.toAdd ∈ dualTwist '' {v | ∃w:Weyl, representation w a.toAdd=v} :=
      ⟨c.toAdd, hc, rfl⟩
    rw [he] at hm
    obtain ⟨w, hw⟩ := hm
    exact ⟨w, congrArg Multiplicative.ofAdd hw⟩
  · intro hb
    have hm : b.toAdd ∈ {v | ∃w:Weyl, representation w (dualTwist a.toAdd)=v} := hb
    rw [← he] at hm
    obtain ⟨c, hc, hcb⟩ := hm
    exact ⟨Multiplicative.ofAdd c, hc, congrArg Multiplicative.ofAdd hcb⟩

@[expose] def torusTwist {F : Type*} [Field F] (t : Fin 4 → Fˣ) : Fin 4 → Fˣ :=
  ![t 3 ^ 2, t 2 ^ 2, t 1, t 0]

lemma character_torusTwist {F : Type*} [Field F] (t : Fin 4 → Fˣ) :
    character (torusTwist t) = (character t).comp dualTwistHom := by
  ext a
  simp [character, torusTwist, dualTwistHom, dualTwist, Fin.prod_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three, zpow_mul]
  ac_rfl

lemma dualTwist_fundamental (i : Fin 4) :
    dualTwistHom (fundamental i) =
      if i.val < 2 then fundamental (Fin.revPerm i) ^ 2 else fundamental (Fin.revPerm i) := by
  apply Multiplicative.toAdd.injective
  ext j
  fin_cases i <;> fin_cases j <;>
    norm_num [dualTwistHom, dualTwist, fundamental, Pi.single_apply,
      Matrix.cons_val_two, Matrix.cons_val_three, Fin.revPerm, Fin.rev, Fin.ext_iff]

lemma fundamentalValue_torusTwist {F : Type*} [Field F] [CharP F 2]
    (t : Fin 4 → Fˣ) (i : Fin 4) :
    fundamentalValue (torusTwist t) i =
      if i.val < 2 then fundamentalValue t (Fin.revPerm i) ^ 2
      else fundamentalValue t (Fin.revPerm i) := by
  unfold fundamentalValue
  rw [character_torusTwist, orbitSumValue_comp (character t) dualTwistHom
    dualTwistHom_injective _ (dualTwistHom_orbit _), dualTwist_fundamental]
  split_ifs with hi
  · simpa only [pow_one] using orbitSumValue_frobenius (G:=Weyl) (character t)
      (fundamental (Fin.revPerm i)) 1
  · rfl
end Theory.AlgebraicGroup.StandardRootSystem.F4WeightAction
