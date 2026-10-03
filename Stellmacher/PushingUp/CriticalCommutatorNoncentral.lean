module

public import Stellmacher.PushingUp.CriticalPairSL2Two

/-!
# Noncentral commutators at a critical vertex

For a positive-distance critical pair, a 2-subgroup `U` of the first vertex
stabilizer which is not contained in its 2-core has a commutator with `Z_a`
not contained in the stabilizer center. This is the natural-module inference
in Stellmacher, *Pushing up* (1986), the proof of (2.4), step (2), from (2.2)(c).

If all commutators were central, `U` would act trivially on the quotient of
`Z_a` by its central part. The supplied natural-module coordinates identify
this action with the faithful matrix action of `SL₂(2)`, so `U` lies in the
full action centralizer. The critical-vertex centralizer has odd index over
the 2-core; since `U` is a 2-group, it lies in that core, a contradiction.
The 2-group hypothesis is essential to this final index argument.
-/

open scoped commutatorElement

namespace Stellmacher.PushingUp

open AmalgamGraph

universe u

variable {M : Type u} [Group M] [Finite M]

private theorem natural_faithful {A W : Type*} [Group A] [Group W]
    [MulDistribMulAction A W]
    (eA : A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (hNat : IsNaturalSL2TwoActionAlong W eA)
    (a : A) (ha : ∀ w : W, a • w = w) : a = 1 := by
  obtain ⟨eW, heW⟩ := hNat
  have hmat : ∀ x : Fin 2 → ZMod 2, Matrix.mulVec (eA a).1 x = x := by
    intro x
    let w : W := Additive.toMul (eW.symm x)
    simpa [ha, w] using (heW a w).symm
  have hcalc : ∀ B : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
      (∀ x : Fin 2 → ZMod 2, Matrix.mulVec B.1 x = x) → B = 1 := by
    decide +kernel
  exact eA.injective (by simpa using hcalc (eA a) hmat)

private theorem central_commutator_le_actionCentralizer
    (S : Subgroup M) (a : Vertex S)
    (hV : IsElementaryAbelian 2 (vertexModule S a))
    (eA : VertexActionQuotient S a ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (hC : letI := vertexQuotientConjugationAction S a
      IsInvariant (VertexActionQuotient S a) (vertexModule S a) (vertexCenterPart S a))
    (hNat : letI := hV
      letI := vertexQuotientConjugationAction S a
      letI := quotientMulDistribMulAction (vertexCenterPart S a) hC
      IsNaturalSL2TwoActionAlong (vertexModule S a ⧸ vertexCenterPart S a) eA)
    (U : Subgroup (FreeAmalgam S))
    (hc : ⁅vertexZ S a, U⁆ ≤
      (Subgroup.center (stabilizer S a)).map (stabilizer S a).subtype) :
    U.subgroupOf (stabilizer S a) ≤ vertexActionCentralizer S a := by
  let _ := hV
  let _ := vertexQuotientConjugationAction S a
  let _ := quotientMulDistribMulAction (vertexCenterPart S a) hC
  intro x hx
  have hqx : vertexActionQuotientMap S a x = 1 := by
    apply natural_faithful eA hNat
    intro w
    induction w using Quotient.inductionOn' with
    | h z =>
      change ((vertexActionQuotientMap S a x • z : vertexModule S a) :
        vertexModule S a ⧸ vertexCenterPart S a) = z
      apply QuotientGroup.eq.mpr
      change (vertexActionQuotientMap S a x • z)⁻¹ * z ∈ vertexCenterPart S a
      change (((vertexActionQuotientMap S a x • z : vertexModule S a) :
        stabilizer S a)⁻¹ * (z : stabilizer S a)) ∈
          Subgroup.center (stabilizer S a)
      rw [SectionTwo.quotientConjugationAction_smul_coe]
      have hz : ((z : stabilizer S a) : FreeAmalgam S) ∈ vertexZ S a := by
        rw [← vertexZ_eq_local_vSubgroup S a]
        exact Subgroup.mem_map_of_mem _ z.property
      have hm := hc (Subgroup.commutator_mem_commutator hz hx)
      obtain ⟨y, hy, hyval⟩ := hm
      have hcenter : ⁅(z : stabilizer S a), x⁆ ∈
          Subgroup.center (stabilizer S a) := by
        have heq : y = ⁅(z : stabilizer S a), x⁆ := by
          apply Subtype.ext
          exact hyval
        rwa [heq] at hy
      have heq : (x * (z : stabilizer S a) * x⁻¹)⁻¹ * z =
          ⁅(z : stabilizer S a), x⁆ := by
        have hcomm := (Subgroup.mem_center_iff.mp hcenter) (z : stabilizer S a)
        calc
          _ = (z : stabilizer S a)⁻¹ *
              (⁅(z : stabilizer S a), x⁆ * z) := by
            simp only [commutatorElement_def]
            group
          _ = _ := by rw [← hcomm]; simp
      rwa [heq]
  exact (QuotientGroup.eq_one_iff _).mp hqx

/-- A 2-subgroup outside the vertex core has noncentral commutators with `Z_a`. -/
public theorem criticalPair_commutator_not_le_center
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' : Vertex S) (hcrit : IsCriticalPair S a a')
    (hb : 0 < criticalDistance S)
    (U : Subgroup (FreeAmalgam S)) (hU : U ≤ stabilizer S a)
    (hUtwo : IsPGroup 2 U) (hUne : ¬ U ≤ vertexTwoCore S a) :
    ¬ ⁅vertexZ S a, U⁆ ≤
      (Subgroup.center (stabilizer S a)).map (stabilizer S a).subtype := by
  intro hc
  obtain ⟨hV, ha', hsl⟩ := criticalPair_sl2Two S T hTS hP hSne hA a a' hcrit hb
  let _ := hV
  let _ := vertexQuotientConjugationAction S a
  obtain ⟨eA, hC, hNat⟩ := hsl.sl2AndNaturalModule
  have hUcent := central_commutator_le_actionCentralizer S a hV eA hC hNat U hc
  rw [vertexActionCentralizer_eq_vertexCentralizerLocal] at hUcent
  have hGaA := stabilizer_isSL2Two_nested_of_mOrbit S a hcrit.1 hA
  have hres : HasMinimalFrattiniResidual S a := by
    simpa [HasMinimalFrattiniResidual, vertexFrattiniResidual,
      VertexFrattiniQuotient, VertexCoreQuotient] using
        sl2Two_twoResidual_isMinimalNormal hGaA
  have hodd := criticalVertex_centralizer_oddIndex T hTS hP hSne a hcrit.1 hb hres
  have hUlocal : IsPGroup 2 (U.subgroupOf (stabilizer S a)) :=
    hUtwo.of_equiv (Subgroup.subgroupOfEquivOfLe hU).symm
  have hUcore := hUlocal.le_pCore_of_le_oddIndexOverCore
    hodd.core_le_centralizer hodd.centralizer_mod_core_odd hUcent
  apply hUne
  intro x hx
  exact Subgroup.mem_map_of_mem (stabilizer S a).subtype
    (hUcore (show (⟨x, hU hx⟩ : stabilizer S a) ∈
      U.subgroupOf (stabilizer S a) from hx))

end Stellmacher.PushingUp
