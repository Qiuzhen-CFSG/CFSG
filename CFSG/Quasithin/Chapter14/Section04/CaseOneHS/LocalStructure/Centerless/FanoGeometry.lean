module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.Orbit
public import Theory.Representation.PSL3Two.NaturalPlaneStabilizer
public import Theory.Representation.PSL3Two.FanoLocalStructure.ParabolicSpaces
public import Theory.GroupAction.SurjectiveFlagCosets
public import Theory.GroupAction.MarkedOrbit

/-!
# The marked Fano-line action of the central involution orbit

Coordinates on the original natural subgroup V send its marked plane V₂ to
v₂ = 0. The same coordinates give the full SL₃(2) action of LT, with the
original parabolic P as the exact preimage of the line stabilizer. The
stabilizer identity for e then identifies its conjugacy orbit equivariantly
with the seven Fano lines, sending e itself to the marked line.

This supplies the action comparison needed to apply H.5.3 in 14.3.29(1).
It retains the explicit preceding seed exclusion 14.3.25; that exclusion and
the final centerlessness argument remain with qt-d-hs-centerless-source.

Source: Aschbacher--Smith, 14.3.29, printed p.1002, and H.5.3, pp.385--386.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open BinaryLinearThree BinaryLinearThree.FanoDecomposition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Coordinates retain the original plane and the whole natural action. -/
theorem source_marked_plane_action (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (F : InvariantFlag T V 3) :
    let := chosen.elementary
    ∃ β : Additive V ≃ₗ[ZMod 2] Vector,
    ∃ f : (L ⊔ (T : Subgroup G) : Subgroup G) →* BinaryLinearThree.Group,
      Function.Surjective f ∧
      (∀ a v, W (f a) (β v) = β (elementaryRepresentation (p := 2) (F.naturalFlagAction L chosen.normalizes) a v)) ∧
      (∀ v : V, β (Additive.ofMul v) 2 = 0 ↔ (v : G) ∈ F.Vi 2) ∧
      (F.P L).subgroupOf (L ⊔ (T : Subgroup G)) = Matrix.PSL3Two.lineParabolicSL.comap f := by
  let := chosen.elementary
  let b := F.naturalFlagCoordinates
  obtain ⟨s, hs⟩ := NaturalPlaneStabilizer.exists_matrix (F.naturalFlagSpace b 2)
    (F.naturalFlagSpace_finrank b 2 (by decide))
  let t := BinaryLinear.OuterCyclic.slEquivLinear 3 s
  let β := b.trans t.symm
  let c := (naturalFlagActorEquiv β).trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm
  let f := c.toMonoidHom.comp (F.naturalFlagAction L chosen.normalizes)
  have hc (a : MulAut V) (v : V) :
      W (c a) (β (Additive.ofMul v)) = β (Additive.ofMul (a v)) := by
    have he : BinaryLinear.OuterCyclic.slEquivLinear 3 (c a) = naturalFlagActorEquiv β a :=
      (BinaryLinear.OuterCyclic.slEquivLinear 3).apply_symm_apply _
    change BinaryLinear.OuterCyclic.slEquivLinear 3 (c a) (β (Additive.ofMul v)) = _
    rw [he, naturalFlagActorEquiv_intertwines]
  have hfc (a : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V) :
      W (f a) (β (Additive.ofMul v)) = β (Additive.ofMul ((F.naturalFlagAction L chosen.normalizes a) v)) := hc _ _
  have hβ (v : V) : β (Additive.ofMul v) 2 = 0 ↔ (v : G) ∈ F.Vi 2 := by
    have hh := hs (t.symm (b (Additive.ofMul v)))
    change t (t.symm (b (Additive.ofMul v))) ∈ F.naturalFlagSpace b 2 ↔
      t.symm (b (Additive.ofMul v)) ∈ NaturalPlaneStabilizer.standard at hh
    rw [LinearEquiv.apply_symm_apply, mem_naturalFlagSpace, NaturalPlaneStabilizer.mem_standard] at hh
    exact hh.symm
  refine ⟨β, f, c.surjective.comp (F.naturalFlagAction_surjective L chosen.normalizes
    (higherRankHypothesis d earlier hq chosen).full_L_action), fun a v => hc _ v.toMul, hβ, ?_⟩
  ext a
  have hp : (a : G) ∈ F.P L ↔ (a : G) ∈ F.Gi 2 := by
    simp only [P, mem_inf, mem_iInf]
    exact ⟨fun ha => ha.2 2 ⟨by decide, by decide⟩,
      fun ha => ⟨a.property, fun i hi => by
        have hi2 : i = 2 := by omega
        simpa only [hi2] using ha⟩⟩
  rw [mem_subgroupOf, hp, mem_comap]
  rw [← F.naturalFlagAction_mem_stabilizer L chosen.normalizes 2 a]
  rw [← NaturalPlaneStabilizer.stabilizer_standard, NaturalPlaneStabilizer.mem_stabilizer]
  change (∀ v : V, ((F.naturalFlagAction L chosen.normalizes a) v : G) ∈ F.Vi 2 ↔
    (v : G) ∈ F.Vi 2) ↔ _
  constructor
  · intro ha w
    obtain ⟨v, rfl⟩ := β.surjective w
    change W (f a) (β (Additive.ofMul v.toMul)) ∈ NaturalPlaneStabilizer.standard ↔
      β (Additive.ofMul v.toMul) ∈ NaturalPlaneStabilizer.standard
    rw [hfc, NaturalPlaneStabilizer.mem_standard, NaturalPlaneStabilizer.mem_standard, hβ, hβ]
    exact ha v.toMul
  · intro ha v
    have hh := ha (β (Additive.ofMul v))
    rw [hfc, NaturalPlaneStabilizer.mem_standard, NaturalPlaneStabilizer.mem_standard, hβ, hβ] at hh
    exact hh


local instance conjugation (A : Subgroup G) : MulAction A G :=
  MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp A.subtype)

local instance lineAction : MulAction BinaryLinearThree.Group Line := MulAction.compHom Line linePerm

local instance lineTransitive : MulAction.IsPretransitive BinaryLinearThree.Group Line where
  exists_smul_eq x y := by
    obtain ⟨a, ha⟩ := FanoLocalStructure.line_reachable x
    obtain ⟨b, hb⟩ := FanoLocalStructure.line_reachable y
    refine ⟨b * a⁻¹, ?_⟩
    change linePerm (b * a⁻¹) x = y
    rw [map_mul, Equiv.Perm.mul_apply, ← ha, map_inv, Equiv.Perm.inv_def,
      Equiv.symm_apply_apply, hb]

/-- The original central-involution orbit is the line orbit for the same marked natural action. -/
theorem source_involution_fano_lines (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (e : G) (he : orderOf e = 2)
    (heI : e ∈ Chapter12.Section08.centerIn (F.I₂ L)) (heT : e ∈ sylowOmega T) :
    letI := chosen.elementary
    ∃ β : Additive V ≃ₗ[ZMod 2] Vector,
    ∃ f : (L ⊔ (T : Subgroup G) : Subgroup G) →* BinaryLinearThree.Group,
      Function.Surjective f ∧
      (∀ a v, W (f a) (β v) = β (elementaryRepresentation (p := 2)
        (F.naturalFlagAction L chosen.normalizes) a v)) ∧
      (∀ v : V, β (Additive.ofMul v) 2 = 0 ↔ (v : G) ∈ F.Vi 2) ∧
      ∃ E : Representation.BinaryConjugacyOrbit.Orbit (L ⊔ (T : Subgroup G)) e ≃ Line,
        (∀ a x, E (Representation.BinaryConjugacyOrbit.permutation
          (L ⊔ (T : Subgroup G)) e a x) = linePerm (f a) (E x)) ∧
        E ⟨e, MulAction.mem_orbit_self e⟩ = Matrix.PSL3Two.flagLine := by
  let := chosen.elementary
  obtain ⟨β, f, hf, hβ, hplane, hP⟩ := source_marked_plane_action d earlier hq chosen F
  let A := L ⊔ (T : Subgroup G)
  have hs : MulAction.stabilizer A e = (F.P L).subgroupOf A := by
    ext a
    have hc := source_involution_stabilizer d earlier hq chosen structural alternatives F hne hseed e he heI heT
    rw [← hc]
    simp only [mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    rw [and_iff_right a.property]
    change (a : G) * e * (a : G)⁻¹ = e ↔ (a : G) * e = e * (a : G)
    exact mul_inv_eq_iff_eq_mul
  have hfix : MulAction.stabilizer BinaryLinearThree.Group Matrix.PSL3Two.flagLine =
      Matrix.PSL3Two.lineParabolicSL := by
    ext g
    exact (FanoLocalStructure.ParabolicSpaces.mem_lineParabolic_iff_fixes_line g).symm
  have hs' : MulAction.stabilizer A e = Matrix.PSL3Two.lineParabolicSL.comap f := hs.trans hP
  have hm : (MulAction.stabilizer A e).map f =
      MulAction.stabilizer BinaryLinearThree.Group Matrix.PSL3Two.flagLine := by
    rw [hs', map_comap_eq_self_of_surjective hf, hfix]
  have hk : f.ker ≤ MulAction.stabilizer A e := by
    rw [hs']
    exact ker_le_comap f _
  let E₀ := MulAction.markedOrbitEquiv (MulEquiv.refl A) e (MulAction.stabilizer A e) (by simp)
  let E₁ := MulAction.surjectiveCosetEquiv (MulAction.stabilizer A e) f hf hk Matrix.PSL3Two.flagLine hm
  let E := E₀.trans E₁
  refine ⟨β, f, hf, hβ, hplane, E, ?_, ?_⟩
  · intro a x
    change E₁ (E₀ (a • x)) = f a • E₁ (E₀ x)
    rw [MulAction.markedOrbitEquiv_smul]
    exact MulAction.surjectiveCosetEquiv_smul _ _ _ _ _ _ _ _
  · change E₁ (E₀ ⟨e, MulAction.mem_orbit_self e⟩) = _
    rw [MulAction.markedOrbitEquiv_base]
    change linePerm (f 1) Matrix.PSL3Two.flagLine = Matrix.PSL3Two.flagLine
    rw [map_one, map_one, Equiv.Perm.one_apply]

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
