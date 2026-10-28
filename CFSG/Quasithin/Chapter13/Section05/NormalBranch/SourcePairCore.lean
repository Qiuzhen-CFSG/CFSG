module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceNonTwoPair
public import Theory.GroupTheory.QuaternionSquareFixedFreeGeneration
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.SingularPairCubicFixed

/-!
# The original non-two pair contains the entire quaternion closure

The original Q_H normalizes both module generators and hence their join I.
The product of their singular orthogonal involutions is fixed-free on the
square quotient of U_H. Frattini displacement generation therefore gives
U_H≤I. Every coordinate and subgroup is the one constructed in the source;
the final consumer chooses a non-two pair without plane-control premises.

Source: Aschbacher–Smith13.5.15, printed p.920.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairCore
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
open SourceOrthogonal ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
  (hseed : D.Vplus=⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)

include d h hU in
theorem twoCore_normalizes_pair (g : G) (hg : g∈D.H) :
    D.QH≤normalizer ((D.V⊔D.V.map (MulAut.conj g).toMonoidHom:Subgroup G):Set G) := by
  let f := (MulAut.conj g).toMonoidHom
  have hc := h.core_module_commutator_le_seed (seed_index d) (module_not_le_core h hU)
  have hcg : ⁅D.QH,D.V.map f⁆≤D.Vplus.map f := by
    have hh := map_mono (f:=f) hc
    have he : D.QH.map f=D.QH := mem_normalizer_iff_map_conj_eq.mp (H_normalizes_QH hg)
    rwa [map_commutator,he] at hh
  exact (le_inf (h.QH_le_T.trans h.T_normalizes_V)
    (le_normalizer_iff_commutator_le_right.mpr (hcg.trans (map_mono h.plus_le)))).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

include d h e hseed hn hU in
theorem closure_le_nonTwo_pair (g : G) (hg : g∈D.H)
    (hpair : ¬IsPGroup 2 (Section08.Source.starImage D.H
      (D.V⊔D.V.map (MulAut.conj g).toMonoidHom))) :
    D.UH≤D.V⊔D.V.map (MulAut.conj g).toMonoidHom := by
  let I := D.V⊔D.V.map (MulAut.conj g).toMonoidHom
  have hIH : I≤D.H := sup_le h.V_le_H (by
    rintro _ ⟨v,hv,rfl⟩
    exact D.H.mul_mem (D.H.mul_mem hg (h.V_le_H hv)) (D.H.inv_mem hg))
  let q := quaternion d h e hseed hn hU
  let α := closureOrthogonalAction I hIH q
  let E := h.closureOrthogonalEquiv I hIH q (center_map d h e hseed hn hU)
  obtain ⟨a,b,ha,hb,hsa,hsb,he⟩ := h.closure_pair_orthogonal_generators
    (seed_index d) (module_not_le_core h hU) g hg q (center_map d h e hseed hn hU) hIH
  let F := E.trans (MulEquiv.subgroupCongr he)
  have hab : ¬IsPGroup 2 (zpowers a⊔zpowers b:Subgroup BinaryFourPlus.Wreath) :=
    fun hh=>hpair (hh.of_equiv F.symm)
  have hc := (BinaryFourPlus.singular_pair_cubic_fixed_free a b ha hb hsa hsb hab).2
  have hm : a*b∈α.range := he ▸ (zpowers a⊔zpowers b).mul_mem
    (mem_sup_left (mem_zpowers a)) (mem_sup_right (mem_zpowers b))
  obtain ⟨x,hx⟩ := hm
  apply quaternion_le_of_square_fixed_free D.UH I q
    (hIH.trans (le_normalizer_conjugateSpanBy D.Vplus D.H))
    (h.UH_le_QH.trans (twoCore_normalizes_pair d h hU g hg)) x
  change ∀v,(BinaryFourPlus.wreathToIsometry (α x)).val v=v→v=0
  rw [hx]
  exact hc

include d h e hseed hn hU in
theorem exists_original_pair_containing_closure : ∃g∈D.H,
    D.UH≤D.V⊔ChapterG.Section02.Setup.conjugate D.V g ∧
    Nonempty ((Section08.Source.starImage D.H
      (D.V⊔ChapterG.Section02.Setup.conjugate D.V g))≃*Equiv.Perm (Fin 3)) := by
  obtain ⟨g,hg,hp,he⟩ := SourceNonTwoPair.exists_original_symmetricThree_pair d h e hseed hn hU
  exact ⟨g,hg,closure_le_nonTwo_pair d h e hseed hn hU g⁻¹ (D.H.inv_mem hg) hp,he⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairCore
end
