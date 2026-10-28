module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.ModelDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.ModelNormalizer
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.SourceMarking.ModelCommutator.CentralExtension

/-!
# The intrinsic commutator mark in the hexacode cover

The coordinate map restricts the literal cover parabolic to a central
extension of its S₄ point stabilizer. The central-extension calculation
identifies the embedded O²([O²(P),U]) with P′ for every ambient Sylow
two-subgroup U contained in P. Both subgroups lie in the embedded O²(P).
Consequently their images in the quotient by its intrinsic two-core agree,
which identifies the source plus mark with `derivedLine`.

The proof keeps the actual coordinate map, parabolic, residual, and quotient
maps. No cubic coordinates, splitting, quotient order, or source residual
factorization enter the argument.

Source: Aschbacher–Smith, Notation 13.2.1 and Lemma 13.2.2(3), printed
pp.877–878, used in 13.8.16(1), printed p.952 (PDF p.969).
-/

public section

open Subgroup Theory.SpecificGroups.SymmetricSix
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer.Model

private theorem point_stabilizer_symmetric_equiv (x : BinaryPoint) :
    Nonempty (MulAction.stabilizer A6 x ≃* Equiv.Perm (Fin 4)) := by
  have he : MulAction.stabilizer A6 x =
      MulAction.stabilizer A6 (duadPolarEquiv.symm x) := by
    ext g
    change g.val • x = x ↔ g.val • duadPolarEquiv.symm x = duadPolarEquiv.symm x
    rw [← duadPolarEquiv.injective.eq_iff, duadPolarEquiv_equivariant]
    simp
  obtain ⟨g, hg⟩ := a6_duad_transitive 0 (duadPolarEquiv.symm x)
  exact ⟨(MulEquiv.subgroupCongr he).trans
    ((MulAction.stabilizerEquivStabilizer hg.symm).symm.trans
      ((MulEquiv.subgroupCongr a6_duad_stabilizer_zero).trans a6DuadModelEquiv.symm))⟩

private theorem parabolic_central_quotient (x : BinaryPoint) :
    ∃ f : parabolic x →* Equiv.Perm (Fin 4),
      Function.Surjective f ∧ f.ker ≤ center (parabolic x) := by
  let c : parabolic x →* MulAction.stabilizer A6 x :=
    Atlas.Codes.hexEvenCoordinate.subgroupComap (MulAction.stabilizer A6 x)
  have hc : Function.Surjective c := by
    intro y
    obtain ⟨g, hg⟩ := Atlas.Codes.hexEvenCoordinate_surjective y.val
    exact ⟨⟨g, by change Atlas.Codes.hexEvenCoordinate g ∈ MulAction.stabilizer A6 x
                  rw [hg]; exact y.property⟩, Subtype.ext hg⟩
  obtain ⟨e⟩ := point_stabilizer_symmetric_equiv x
  let f := e.toMonoidHom.comp c
  refine ⟨f, e.surjective.comp hc, ?_⟩
  intro g hg
  have hcg : c g = 1 := e.injective
    ((show e (c g) = 1 from hg).trans (map_one e).symm)
  have hgk : (g : Cover) ∈ Atlas.Codes.hexEvenCoordinate.ker := congrArg Subtype.val hcg
  have hgz : (g : Cover) ∈ center Cover := by
    rwa [← Representation.Hexacode.even_kernel_eq_center]
  rw [mem_center_iff]
  intro y
  apply Subtype.ext
  exact mem_center_iff.mp hgz y.val

/-- The commutator stays inside the residual because the Sylow subgroup
lies in its actual normalizer. -/
theorem residual_commutator_le (x : BinaryPoint) (U : Sylow 2 Cover)
    (hU : (U : Subgroup Cover) ≤ parabolic x) :
    ⁅residual x, (U : Subgroup Cover)⁆ ≤ residual x := by
  apply le_normalizer_iff_commutator_le_left.mp
  rwa [residual_normalizer]

/-- The parabolic's derived subgroup is contained in its two-residual. -/
theorem parabolic_derived_le_residual (x : BinaryPoint) :
    (commutator (parabolic x)).map (parabolic x).subtype ≤ residual x := by
  obtain ⟨f, hf, hk⟩ := parabolic_central_quotient x
  let S : Sylow 2 (parabolic x) := Classical.choice inferInstance
  have he := ModelCommutator.central_symmetric_residual_commutator f hf hk S
  apply map_mono
  rw [← he]
  exact (map_subtype_le _).trans (commutator_le_left _ _)

/-- The embedded plus residual is exactly the embedded derived subgroup
of the literal cover parabolic. -/
theorem commutator_residual_eq_derived (x : BinaryPoint) (U : Sylow 2 Cover)
    (hU : (U : Subgroup Cover) ≤ parabolic x) :
    (pResidual 2 (⁅residual x, (U : Subgroup Cover)⁆ : Subgroup Cover)).map
      ⁅residual x, (U : Subgroup Cover)⁆.subtype =
      (commutator (parabolic x)).map (parabolic x).subtype := by
  obtain ⟨f, hf, hk⟩ := parabolic_central_quotient x
  have he := ModelCommutator.central_symmetric_residual_commutator f hf hk (U.subtype hU)
  have hC :
      (⁅pResidual 2 (parabolic x), (U.subtype hU : Subgroup (parabolic x))⁆).map
        (parabolic x).subtype = ⁅residual x, (U : Subgroup Cover)⁆ := by
    rw [map_commutator, Sylow.coe_subtype, map_subgroupOf_eq_of_le hU]
    rfl
  have hm := congrArg (fun K : Subgroup (parabolic x) => K.map (parabolic x).subtype) he
  rw [map_embedded_pResidual, hC] at hm
  exact hm

/-- The intrinsic source plus mark is the model's derived line. -/
theorem commutator_residual_image_eq_derivedLine (x : BinaryPoint) (U : Sylow 2 Cover)
    (hU : (U : Subgroup Cover) ≤ parabolic x) :
    (((pResidual 2 (⁅residual x, (U : Subgroup Cover)⁆ : Subgroup Cover)).map
      ⁅residual x, (U : Subgroup Cover)⁆.subtype).subgroupOf (residual x)).map
      (QuotientGroup.mk' (pCore 2 (residual x))) = derivedLine x := by
  rw [commutator_residual_eq_derived x U hU]
  rfl

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer.Model

end
