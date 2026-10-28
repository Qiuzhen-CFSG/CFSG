module
public import Theory.Representation.PSL3Two.FanoLocalStructure.ParabolicSpaces
public import Theory.Representation.PSL3Two.NaturalSylowFixed
public import Theory.Representation.BinaryOffender.EquivariantOffender
/-!
# Sylow fixed planes in the two Fano cores

Sylow conjugacy transports the known fixed plane of the flag subgroup to
any Sylow two-subgroup. Coordinate duality transfers this result to the
line core, retaining the inverse-transpose twist. These fixed planes identify
the whole original orbit module in the 13.4.7 application.
Source: Aschbacher–Smith H.5.2(2), 13.4.7, printed pp.385,901.
-/

public noncomputable section
open Representation Representation.BinaryOffender Subgroup
namespace BinaryLinearThree.FanoSylowFixed
open FanoDecomposition Matrix.PSL3Two

/-- Every Sylow two-subgroup fixes a plane in the point core. -/
theorem point_finrank (P : Sylow 2 Group) :
    Module.finrank (ZMod 2) (fixedSpace U₂ (P : Subgroup Group)) = 2 := by
  obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq Group flagSylow P
  change Module.finrank (ZMod 2) (fixedSpace U₂ ((flagSylow : Subgroup Group).map (MulAut.conj g).toMonoidHom)) = 2
  rw [←(fixedSpaceConjEquiv U₂ (flagSylow : Subgroup Group) g).finrank_eq]
  exact FanoLocalStructure.ParabolicSpaces.finrank_fixedSpace_flagSylow

/-- The line core has the same Sylow fixed dimension under its actual action. -/
theorem line_finrank (P : Sylow 2 Group) :
    Module.finrank (ZMod 2) (fixedSpace lineCoreRepresentation (P : Subgroup Group)) = 2 := by
  let e := coreDualityEquiv
  let j := e.toLinearEquiv.submoduleMap
    (fixedSpace (U₂.comp AutomorphismAction.graph.toMonoidHom) (P : Subgroup Group))
  have hj := j.finrank_eq
  have hm := fixedSpace_map_equivariant
    (U₂.comp AutomorphismAction.graph.toMonoidHom) lineCoreRepresentation
    (MonoidHom.id Group) e.toLinearEquiv (fun a v => LinearMap.congr_fun (e.isIntertwining' a) v) (P : Subgroup Group)
  rw [Subgroup.map_id] at hm
  change (fixedSpace (U₂.comp AutomorphismAction.graph.toMonoidHom) (P : Subgroup Group)).map e.toLinearMap = _ at hm
  rw [hm] at hj
  rw [←hj, fixedSpace_comp_map]
  exact point_finrank (P.mapSurjective AutomorphismAction.graph.surjective)
end BinaryLinearThree.FanoSylowFixed
