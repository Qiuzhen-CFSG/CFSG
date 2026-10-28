module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Linear.Actions.Inputs
public import Theory.SpecificGroups.PSL3.CartanActions.ThreeAlignment

/-!
# Simultaneous Sylow and torus alignment for the ternary PSL₃ case

Sylow conjugacy first sends the supplied Sylow two-subgroup to the concrete
upper unipotent group. Its proved normalizer formula then puts the transported
three-subgroup in the upper Borel. Sylow three-conjugacy inside that Borel
puts it into the diagonal torus, preserving the first alignment. This proves
the published model input with its original commutativity hypothesis.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), the ternary Borel case. This is the
alignment input for the separately assembled action calculation.
-/

public section

open scoped MatrixGroups
open Subgroup Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Matrix.PSL3.CartanActions.ThreeAlignment
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Actions

/-- The actual simultaneous alignment, including field order four and B = 1. -/
theorem borelThreeAlignment (F : Type*) [Field F] [Finite F] [CharP F 2] : BorelThreeAlignment F := by
  intro f hf hF S B hB _hcomm hBN
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) S
    (unipotentSylow F (by omega) hF)
  have hS : (S : Subgroup PSL(3,F)).map (MulAut.conj g).toMonoidHom = unipotent F :=
    congrArg Sylow.toSubgroup hg
  have hB' : IsPGroup 3 (B.map (MulAut.conj g).toMonoidHom) := hB.map _
  have hBb : B.map (MulAut.conj g).toMonoidHom ≤ borel F := by
    have h := (map_mono hBN).trans
      (le_normalizer_map (H := (S : Subgroup PSL(3,F))) (MulAut.conj g).toMonoidHom)
    rwa [hS, normalizer_unipotent_of_charTwo] at h
  obtain ⟨b,hb,hbt⟩ := conjugate_borel_threeSubgroup_into_torus F hF _ hB' hBb
  refine ⟨(MulAut.conj g).trans (MulAut.conj b), ?_, ?_⟩
  · change (S : Subgroup PSL(3,F)).map
      ((MulAut.conj b).toMonoidHom.comp (MulAut.conj g).toMonoidHom) = _
    rw [← Subgroup.map_map, hS]
    exact mem_normalizer_iff_map_conj_eq.mp (borel_le_normalizer_unipotent F hb)
  · change B.map ((MulAut.conj b).toMonoidHom.comp (MulAut.conj g).toMonoidHom) ≤ _
    rwa [← Subgroup.map_map]

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Actions
