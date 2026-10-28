module
public import Theory.Representation.PSL3Two.FanoLocalStructure.ParabolicSpaces
public import Theory.Representation.PSL3Two.NaturalDualRank
public import Theory.Representation.BinaryNormalizerResidual.TrivialCommutant

/-!
# Normalizer residuals of the three binary linear six-spaces

The point parabolic fixes only its point-complement line. An invertible
commuting operator therefore fixes that vector, all its conjugates, and
hence the whole Fano core. Coordinate duality gives the line-core result.
Together with the natural–dual commutant calculation, the two-group outer
automorphism quotient puts the two-residual of every model normalizer in
the original component image. These are the exact three module models
needed for the overgroup supplement in source 13.4.7(2).

Source: Aschbacher–Smith, H.5.2(5), H.5.3 and 13.4.7(2), printed pp.385,902.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryLinearThree.SixSpaceNormalizers
open FanoDecomposition FanoLocalStructure.ParabolicSpaces

/-- The Fano point core has trivial invertible commutant. -/
theorem point_centralizer (f : Core ≃ₗ[ZMod 2] Core)
    (hf : ∀ g v, f (U₂ g v) = U₂ g (f v)) : f = LinearEquiv.refl _ _ := by
  have hfix : f up ∈ fixedSpace U₂ Matrix.PSL3Two.pointParabolicSL := by
    intro g
    change U₂ g.val (f up) = f up
    rw [← hf]
    have hg : U₂ g.val up = up := by
      rw [← pointSpike_action, (mem_pointParabolic_iff_fixes_point g).mp g.property]
    rw [hg]
  rw [fixedSpace_pointParabolic] at hfix
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hfix
  have hup : up ≠ 0 := by
    intro hz
    have he := congrArg (fun v : Core => v.val ⟨![0,1,0], by decide⟩) hz
    change (Pi.single Matrix.PSL3Two.flagPoint 1 : Point → ZMod 2)
      ⟨![0,1,0], by decide⟩ + 1 = 0 at he
    norm_num [Matrix.PSL3Two.flagPoint, Pi.single_apply] at he
  have hc1 : c = 1 := by
    have hb : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hb c with hz | ho
    · rw [hz,zero_smul] at hc
      exact (hup (f.injective (hc.symm.trans f.map_zero.symm))).elim
    · exact ho
  have hu : f up = up := by simpa only [hc1,one_smul] using hc.symm
  have hp (p : Point) : f (pointSpike p) = pointSpike p := by
    obtain ⟨g,hg⟩ := SimpleHeadQuotientObstruction.point_reachable p
    rw [← hg, pointSpike_action,hf,hu]
  ext v : 1
  calc
    f v = f (∑ p : Point, v.val p • pointSpike p) :=
      congrArg f (SimpleHeadQuotientObstruction.pointSpike_expansion v).symm
    _ = ∑ p : Point, v.val p • pointSpike p := by simp only [map_sum,map_smul,hp]
    _ = v := SimpleHeadQuotientObstruction.pointSpike_expansion v

/-- Coordinate duality transfers the commutant calculation to the line core. -/
theorem line_centralizer (f : LineCore ≃ₗ[ZMod 2] LineCore)
    (hf : ∀ g v, f (lineCoreRepresentation g v) = lineCoreRepresentation g (f v)) :
    f = LinearEquiv.refl _ _ := by
  let a := coreDuality.trans (f.trans coreDuality.symm)
  have hd (g : Group) (v : Core) : coreDuality (U₂ g v) =
      lineCoreRepresentation (AutomorphismAction.graph g) (coreDuality v) := by
    have he := LinearMap.congr_fun (coreDualityEquiv.isIntertwining'
      (AutomorphismAction.graph g)) v
    change coreDuality (U₂ (AutomorphismAction.graph (AutomorphismAction.graph g)) v) = _ at he
    rwa [AutomorphismAction.graph_graph] at he
  have ha : a = LinearEquiv.refl _ _ := point_centralizer a (by
    intro g v
    apply coreDuality.injective
    change coreDuality (coreDuality.symm (f (coreDuality (U₂ g v)))) =
      coreDuality (U₂ g (coreDuality.symm (f (coreDuality v))))
    rw [coreDuality.apply_symm_apply,hd,hf,hd,coreDuality.apply_symm_apply])
  ext v : 1
  have he := congrArg (fun b : Core ≃ₗ[ZMod 2] Core => coreDuality (b (coreDuality.symm v))) ha
  simpa only [a,LinearEquiv.trans_apply,coreDuality.apply_symm_apply,LinearEquiv.refl_apply] using he

private theorem point_faithful : Function.Injective U₂ := by
  intro g h he
  have hp (p : Point) : pointPerm g p = pointPerm h p := by
    apply FanoLocalStructure.pointSpike_injective
    rw [pointSpike_action,pointSpike_action]
    exact LinearMap.congr_fun he (pointSpike p)
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext v
  by_cases hv : v = 0
  · simp [hv]
  · exact congrArg Subtype.val (hp ⟨v,hv⟩)

private theorem line_faithful : Function.Injective lineCoreRepresentation := by
  intro g h he
  have hh : U₂ (AutomorphismAction.graph g) = U₂ (AutomorphismAction.graph h) := by
    apply LinearMap.ext
    intro v
    apply coreDuality.injective
    have hg := LinearMap.congr_fun (coreDualityEquiv.isIntertwining' g) v
    have hh := LinearMap.congr_fun (coreDualityEquiv.isIntertwining' h) v
    exact hg.trans ((LinearMap.congr_fun he (coreDuality v)).trans hh.symm)
  exact AutomorphismAction.graph.injective (point_faithful hh)

/-- The two-residual of each actual six-space normalizer lies in the component image. -/
theorem natural_dual_residual :
    (pResidual 2 (linearNormalizer (W.prod W.dual))).map
      (linearNormalizer (W.prod W.dual)).subtype ≤ actionImage (W.prod W.dual) :=
  BinaryNormalizerResidual.residual_le_of_trivial_commutant _ NaturalDual.action_injective
    Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup NaturalDual.centralizer_eq_one

theorem point_residual :
    (pResidual 2 (linearNormalizer U₂)).map (linearNormalizer U₂).subtype ≤ actionImage U₂ :=
  BinaryNormalizerResidual.residual_le_of_trivial_commutant _ point_faithful
    Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup point_centralizer

theorem line_residual :
    (pResidual 2 (linearNormalizer lineCoreRepresentation)).map
      (linearNormalizer lineCoreRepresentation).subtype ≤ actionImage lineCoreRepresentation :=
  BinaryNormalizerResidual.residual_le_of_trivial_commutant _ line_faithful
    Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup line_centralizer
end BinaryLinearThree.SixSpaceNormalizers
