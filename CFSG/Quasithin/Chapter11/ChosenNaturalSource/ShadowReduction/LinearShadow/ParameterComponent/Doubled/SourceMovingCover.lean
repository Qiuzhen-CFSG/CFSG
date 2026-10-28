module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.SourceCover
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.MovingOrthogonal
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.NaturalProjection

/-!
Orthogonal coordinates on the original omega orbit, allowing its fixed direct
summand. The coordinate kernel misses every commutator with the selected actor.
The maximal Sylow commutator dimension must still come from the doubled SL₃
calculation in 11.3.6, printed pp.772--773.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.OneCohomology
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
open CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {H A : Subgroup G}
    [IsElementaryAbelian 2 (omegaClosure T H)]
    {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance sourceMovingFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The full orbit need not be a cover. Its moving part suffices for the
literal commutator contradiction, with the exact source actor projection. -/
theorem source_orthogonalMarking_of_moving_dimension
    (e : residualStar T H ≃* SL(2,F)) (hAH : A ≤ H)
    (hAK : (A.subgroupOf H).map (starProjection T H) ≤ residualStar T H)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (p : (NaturalRecognition.binaryAction T H e).IntertwiningMap
      (SL2OrthogonalCover.binaryNatural (F := F)))
    (hp : Function.Surjective p)
    (hk : p.toLinearMap.ker = fixed (NaturalRecognition.binaryAction T H e))
    (hs : Coinvariants.ker (NaturalRecognition.binaryAction T H e) ⊔
      fixed (NaturalRecognition.binaryAction T H e) = ⊤)
    (P : Sylow 2 SL(2,F))
    (hmove : Module.finrank (ZMod 2)
      (Coinvariants.ker ((NaturalRecognition.binaryAction T H e).comp P.toSubgroup.subtype)) =
        2 * n) :
    ∃ c : OrthogonalMarking T H A F, ∀ a : A,
      c.parameter a = e ⟨starProjection T H (inclusion hAH a),
        hAK (mem_map_of_mem (starProjection T H) a.property)⟩ := by
  let ρ := NaturalRecognition.binaryAction T H e
  obtain ⟨j,_,hj⟩ := orthogonal_map_of_sylow_moved_dimension n hn hF ρ p hp hk hs P hmove
  let f : A →* residualStar T H :=
    { toFun a := ⟨starProjection T H (inclusion hAH a),
        hAK (mem_map_of_mem (starProjection T H) a.property)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' a b := Subtype.ext (by simp) }
  let q : omegaClosure T H →* Multiplicative (SL2OrthogonalCover.Space F) :=
    { toFun w := Multiplicative.ofAdd (j (Additive.ofMul w))
      map_one' := j.map_zero
      map_mul' a b := j.map_add (Additive.ofMul a) (Additive.ofMul b) }
  let C : Subgroup (omegaClosure T H) := (Coinvariants.ker ρ).toAddSubgroup.toSubgroup
  have hAC : ⁅A,omegaClosure T H⁆ ≤ C.map (omegaClosure T H).subtype := by
    apply commutator_le.mpr
    intro a ha w hw
    let w' : omegaClosure T H := ⟨w,hw⟩
    let a' : A := ⟨a,ha⟩
    refine ⟨localAction T H (inclusion hAH a') w' * w'⁻¹,?_,rfl⟩
    have hh := Coinvariants.sub_mem_ker (ρ := ρ) (e (f a')) (Additive.ofMul w')
    have he : ρ (e (f a')) (Additive.ofMul w') =
        Additive.ofMul (localAction T H (inclusion hAH a') w') := by
      apply Additive.toMul.injective
      exact NaturalRecognition.binaryAction_equiv T H e (f a') (Additive.ofMul w')
    rw [he] at hh
    change Additive.ofMul (localAction T H (inclusion hAH a') w' * w'⁻¹) ∈ Coinvariants.ker ρ
    simpa only [ofMul_mul,ofMul_inv,sub_eq_add_neg] using hh
  let c : OrthogonalMarking T H A F :=
    { le_local := hAH
      parameter := e.toMonoidHom.comp f
      coordinates := q
      kernel_disjoint := by
        apply disjoint_iff_inf_le.mpr
        intro w hw
        have hwC : Additive.ofMul w ∈ Coinvariants.ker ρ := by
          obtain ⟨v,hv,he⟩ := hAC hw.2
          have hvw : v = w := Subtype.ext he
          exact hvw ▸ hv
        have hwj : Additive.ofMul w ∈ j.toLinearMap.ker := hw.1
        have hz := disjoint_iff_inf_le.mp hj ⟨hwj,hwC⟩
        exact hz
      intertwines := by
        intro a w
        change j (Additive.ofMul (localAction T H (inclusion hAH a) w)) = _
        have he : ρ (e (f a)) (Additive.ofMul w) =
            Additive.ofMul (localAction T H (inclusion hAH a) w) := by
          apply Additive.toMul.injective
          exact NaturalRecognition.binaryAction_equiv T H e (f a) (Additive.ofMul w)
        rw [← he]
        exact LinearMap.congr_fun (j.isIntertwining' (e (f a))) (Additive.ofMul w) }
  exact ⟨c,fun _ => rfl⟩

/-- The degree-2n application starts with the actual G.1.6 coordinates and
constructs the orthogonal marking. Only the Sylow commutator dimension
remains from the reciprocal doubled-module calculation. -/
theorem source_orthogonalMarking_of_coordinates
    (e : residualStar T H ≃* SL(2,F)) (hAH : A ≤ H)
    (hAK : (A.subgroupOf H).map (starProjection T H) ≤ residualStar T H)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (P : Sylow 2 SL(2,F))
    (hP : SL2SylowFixedRecognition.FixedSpaceHypotheses
      (NaturalRecognition.binaryAction T H e) P)
    (c : SL2SylowFixedRecognition.QuotientCoordinates
      (NaturalRecognition.binaryAction T H e)) (hc : c.multiplicity = 1)
    (hmove : Module.finrank (ZMod 2)
      (Coinvariants.ker ((NaturalRecognition.binaryAction T H e).comp P.toSubgroup.subtype)) =
        2 * n) :
    ∃ m : OrthogonalMarking T H A F, ∀ a : A,
      m.parameter a = e ⟨starProjection T H (inclusion hAH a),
        hAK (mem_map_of_mem (starProjection T H) a.property)⟩ := by
  obtain ⟨p,hp,hk⟩ := natural_projection_of_multiplicity_one
    (NaturalRecognition.binaryAction T H e) c hc
  exact source_orthogonalMarking_of_moving_dimension e hAH hAK n hn hF p hp hk
    (moving_fixed_span_of_sylow_fixed _ P hP) P hmove

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
