module
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.PairFieldAutomorphism

/-!
# The two Borel subgroups meeting the fixed pair

Coefficient square Frobenius fixes infinity and preserves its point
stabilizer. An element of the setwise pair stabilizer carries infinity to
infinity or zero, so its conjugation carries the point stabilizer to itself
or to the opposite Borel. The point-pair overlap is C₃ × D₁₀, and each of
its cubic elements is central in that overlap. A pair element moving such
a cubic therefore exchanges the two Borel subgroups.
-/

noncomputable section
open Subgroup MulAction
open BenderSuzuki.Converse Theory.PSL2 Theory.PSL2.BinaryFourFieldExtension
namespace Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam

/-- The point stabilizer conjugated by the fixed Weyl swap. -/
@[expose] public def oppositePoint : Subgroup Model := point.map (MulAut.conj swap).toMonoidHom

/-- The opposite Borel is precisely the stabilizer of zero. -/
public theorem oppositePoint_eq_stabilizer : oppositePoint = stabilizer Model (pZero F) := by
  rw [oppositePoint,point_eq_stabilizer,←stabilizer_smul_eq_stabilizer_map_conj,swap_inf]

/-- Coefficient square Frobenius preserves the original point subgroup. -/
public theorem squareModel_point : point.map squareModel.toMonoidHom = point := by
  have hmove (g : Model) :
      fieldPoint squareField (g • pInf F) = squareModel g • pInf F := by
    simp only [model_smul,fieldPoint_inf,fieldPoint_psl2]
    rfl
  have hmem (g : Model) : squareModel g ∈ point ↔ g ∈ point := by
    change squareModel g • pInf F = pInf F ↔ g • pInf F = pInf F
    constructor
    · intro hg
      apply (fieldPerm squareField).injective
      change fieldPoint squareField (g • pInf F) = fieldPoint squareField (pInf F)
      rw [hmove,fieldPoint_inf]
      exact hg
    · intro hg
      rw [←hmove,hg,fieldPoint_inf]
  apply le_antisymm
  · rintro _ ⟨g,hg,rfl⟩
    exact (hmem g).mpr hg
  · intro g hg
    exact ⟨squareModel.symm g,(hmem _).mp (by rwa [squareModel.apply_symm_apply]),
      squareModel.apply_symm_apply g⟩

/-- Conjugation by a pair element permutes the two marked Borel subgroups. -/
public theorem pair_conj_point_or_opposite (c : pair) :
    point.map (MulAut.conj (c : Model)).toMonoidHom = point ∨
      point.map (MulAut.conj (c : Model)).toMonoidHom = oppositePoint := by
  rw [point_eq_stabilizer,←stabilizer_smul_eq_stabilizer_map_conj,
    oppositePoint_eq_stabilizer]
  rcases (mem_pair c.val).mp c.property with hc | hc
  · left
    rw [model_smul,fieldPoint_inf,hc.1]
  · right
    rw [model_smul,fieldPoint_inf,hc.1]

private theorem overlap_cube_central :
    ∀ x y : Multiplicative (ZMod 3) × DihedralGroup 5, y ^ 3 = 1 → x * y = y * x := by
  decide +kernel

/-- Every cube-one element is central in the actual point-pair overlap. -/
public theorem overlap_commutes_cubic (c s : Model) (hc : c ∈ point ⊓ pair)
    (hs : s ∈ point ⊓ pair) (hs3 : s ^ 3 = 1) : Commute c s := by
  let c' : ↥(point ⊓ pair) := ⟨c,hc⟩
  let s' : ↥(point ⊓ pair) := ⟨s,hs⟩
  have he : c' * s' = s' * c' := by
    apply overlapEquiv.injective
    rw [map_mul,map_mul]
    apply overlap_cube_central
    rw [←map_pow,show s'^3=1 from Subtype.ext hs3,map_one]
  exact congrArg Subtype.val he

/-- A pair element that moves an overlap cubic exchanges the two Borel subgroups. -/
public theorem pair_conj_point_eq_opposite_of_not_commute {s : Model}
    (hs : s ∈ point ⊓ pair) (hs3 : s ^ 3 = 1) (c : pair)
    (hc : ¬ Commute (c : Model) s) :
    point.map (MulAut.conj (c : Model)).toMonoidHom = oppositePoint := by
  rcases (mem_pair c.val).mp c.property with hfix | hswap
  · have hcp : (c : Model) ∈ point := by
      change (c : Model) • pInf F = pInf F
      rw [model_smul,fieldPoint_inf,hfix.1]
    exact False.elim (hc (overlap_commutes_cubic _ _ ⟨hcp,c.property⟩ hs hs3))
  · rw [point_eq_stabilizer,←stabilizer_smul_eq_stabilizer_map_conj,
      oppositePoint_eq_stabilizer,model_smul,fieldPoint_inf,hswap.1]

end Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam
