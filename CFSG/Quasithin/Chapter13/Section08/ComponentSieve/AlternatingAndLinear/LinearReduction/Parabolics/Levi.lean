module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.Levi.FiveSpaces
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.Levi.MarkedResiduals
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.Levi.TwoNodes
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.Levi.Normalizers
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.Levi.FourComponent
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# Small binary Levi calculations for 13.8.25

The actual two-space and three-space stabilizers in binary five-space have
quotients S₃ × PSL₃(2) and PSL₃(2) × S₃ by their intrinsic two-cores. Both
maps are induced by the corresponding subspace and quotient actions. Cubic
elements in the marked endpoint O² residuals have nontrivial S₃ coordinates,
so their images cannot lie in the marked PSL₃(2) factors.

The imported constructions complete the intrinsic package: nonadjacent
node pairs have quotient S₃ × S₃ with their O² residuals mapping to the
ordered A₃ factors; solvability and three-part nine recognize exactly these
flags; normalizer containment forces the ordered nodes (2,0) or (1,3); and
in degree four an adjacent-node enlargement contains a genuine local
C-component with quotient PSL₃(2), containing the original node residual.

The assembly below supplies the solvable single-node enlargement and uses
the normalizer restriction to choose a strict S₃ × PSL₃(2) overgroup, retaining
the endpoint residual outside its PSL₃(2) factor. The general block actions
and exact two-core kernels are in BinaryLinear.SmallParabolicLevi. Identifying
these marked subgroups with the source groups and lifting them through H*
remain the responsibility of the surrounding source-theorem assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.25,
printed pp.959–960 (PDF pp.976–977). Source assembly belongs to Parabolics.
-/

public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

/-- The nonadjacent-node parabolic is solvable: its two-core is nilpotent
and its actual quotient is S₃ × S₃. -/
theorem fiveTwoNode_isSolvable (b : FiveBasis) (i j : Fin 4)
    (hgap : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    Group.IsSolvable (fiveParabolic b {i, j}) := by
  let : Finite (LinearGroup 5) := Finite.of_injective
    (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
    Group.isSolvable_of_isSolvable_injective
      (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
  let e := fiveTwoNodeQuotientEquiv b i j hgap
  have hquot : Group.IsSolvable (fiveParabolic b {i, j} ⧸ pCore 2 (fiveParabolic b {i, j})) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let : Group.IsNilpotent (pCore 2 (fiveParabolic b {i, j})) := pCore_isPGroup.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient _).mpr ⟨inferInstance, hquot⟩

/-- Adding a nonadjacent node gives a strict solvable overgroup, with its
actual two-core quotient and both ordered residual images. -/
theorem five_single_node_levi_overgroup (b : FiveBasis) (i : Fin 4) :
    ∃ j : Fin 4, (i.val + 1 < j.val ∨ j.val + 1 < i.val) ∧
      fiveParabolic b {i} < fiveParabolic b {i, j} ∧
      Group.IsSolvable (fiveParabolic b {i, j}) ∧
      ∃ e : (fiveParabolic b {i, j} ⧸ pCore 2 (fiveParabolic b {i, j})) ≃*
          Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3),
        ((fiveNodeResidual b i).subgroupOf (fiveParabolic b {i, j})).map
            (e.toMonoidHom.comp (QuotientGroup.mk' _)) =
          (alternatingGroup (Fin 3)).prod ⊥ ∧
        ((fiveNodeResidual b j).subgroupOf (fiveParabolic b {i, j})).map
            (e.toMonoidHom.comp (QuotientGroup.mk' _)) =
          (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup (Fin 3)) := by
  obtain ⟨j, hgap, hlt⟩ := five_single_node_overgroup b i
  exact ⟨j, hgap, hlt, fiveTwoNode_isSolvable b i j hgap,
    fiveTwoNodeQuotientEquiv b i j hgap,
    fiveNodeResidual_map_twoNodeBlockAction_first b i j hgap,
    fiveNodeResidual_map_twoNodeBlockAction_second b i j hgap⟩

/-- Normalizer containment selects a strict two-space or three-space
overgroup. Its quotient is S₃ × PSL₃(2), with the endpoint residual outside
the PSL₃(2) factor; factor reversal preserves the original geometric map. -/
theorem five_normalizer_levi_overgroup (b : FiveBasis) (beta delta : Fin 4)
    (hgap : beta.val + 1 < delta.val ∨ delta.val + 1 < beta.val)
    (hN : normalizer (fiveNodeResidual b beta : Set (LinearGroup 5)) ≤
      normalizer (fiveNodeResidual b delta : Set (LinearGroup 5))) :
    ∃ k : Fin 4, (k = 1 ∨ k = 2) ∧
      fiveParabolic b {beta, delta} < flagStabilizer b {k} ∧
      fiveNodeResidual b delta ≤ flagStabilizer b {k} ∧
      ∃ e : (flagStabilizer b {k} ⧸ pCore 2 (flagStabilizer b {k})) ≃*
          Equiv.Perm (Fin 3) × Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2),
        ¬ ((fiveNodeResidual b delta).subgroupOf (flagStabilizer b {k})).map
            (e.toMonoidHom.comp (QuotientGroup.mk' _)) ≤
          (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod ⊤ := by
  rcases fiveNodeResidual_normalizer_pair b beta delta hgap hN with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨1, Or.inl rfl, ?_, ?_, fiveTwoSpaceQuotientEquiv b,
      first_residual_image_not_le_projective_factor b⟩
    · simpa only [Set.pair_comm] using five_first_third_overgroup b
    · exact (fiveNodeResidual_le b 0).trans (flagStabilizer_antitone b (by simp))
  · let e := (fiveThreeSpaceQuotientEquiv b).trans MulEquiv.prodComm
    refine ⟨2, Or.inr rfl, five_second_fourth_overgroup b, ?_, e, ?_⟩
    · exact (fiveNodeResidual_le b 3).trans (flagStabilizer_antitone b (by simp))
    · intro h
      obtain ⟨g, hg, hn⟩ := exists_last_residual_nontrivial_threeSpace_image b
      exact hn (h (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)).1

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

end
