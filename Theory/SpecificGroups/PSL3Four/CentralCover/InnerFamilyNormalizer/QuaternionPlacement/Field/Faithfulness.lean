module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.QuaternionPlacement.Field.Dihedral
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.QuaternionPlacement.Graph.Model

/-!
# Faithfulness of the binary graph and field action

The concrete binary model acts faithfully on the actual PSL₃(4). The binary
coefficient inclusion is injective, and an element whose projective image is
trivial must lie in the trivial center of SL₃(2). Since PSL₃(4) is centerless,
the resulting inner action is faithful as well. The root-matrix separation
lemma `Graph.linear_field_graph_eq_one` then separates this inner action from
the graph and field factors.

Composing with the explicit dihedral-times-C₂ embedding proves the required
faithfulness of the order-thirty-two candidate in the full Frobenius
centralizer. Neither surjectivity nor a Sylow assertion is needed here.

Source: the field-involution row of Aschbacher–Smith 16.1.4(4), printed p.1171,
and the quaternion-placement application in 16.4.9, printed p.1192,
`refs/quasithin.pdf` (1 March 2004 manuscript).
-/

public section

open Subgroup
open Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement.Field
noncomputable section

private theorem binaryMap_injective :
    Function.Injective (SpecialLinearGroup.map binaryCast : Binary →* SL) := by
  intro x y h
  ext i j
  apply binaryCast.injective
  exact congrArg (fun z : SL => z i j) h

private theorem binaryProject_injective : Function.Injective binaryProject := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  have hz : SpecialLinearGroup.map binaryCast x ∈ center SL :=
    (QuotientGroup.eq_one_iff _).mp hx
  have hb : x ∈ center Binary := by
    apply mem_center_iff.mpr
    intro y
    apply binaryMap_injective
    simp only [map_mul]
    exact mem_center_iff.mp hz (SpecialLinearGroup.map binaryCast y)
  rwa [PSL3Two.center_eq_bot] at hb

private theorem binaryInner_injective : Function.Injective binaryInner := by
  have hconj : Function.Injective (MulAut.conj : PSL →* MulAut PSL) := by
    let := Atlas.sl_perfect (F := F) 3 (by decide)
    exact MulAut.conj_injective_of_center_eq_bot
      (Group.IsPerfect.center_quotient_center_eq_bot SL)
  exact hconj.comp binaryProject_injective

/-- The binary inner, graph and field model acts faithfully on PSL₃(4). -/
theorem modelHom_injective : Function.Injective modelHom := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  have he : (modelHom x : MulAut PSL) = 1 := congrArg Subtype.val hx
  rw [modelHom_apply] at he
  have hlin (y : Binary) :
      linearConj F (SpecialLinearGroup.toGL (SpecialLinearGroup.map binaryCast y)) =
        binaryInner y := linearConj_toGL F _
  have hcomm : Commute
      (involutionHom (graph F) (graph_sq F) x.1.right)
      (Matrix.PSL3Four.fieldAction x.2) :=
    (graph_commute_frobenius.pow_left x.1.right.toAdd.val).pow_right x.2.toAdd.val
  have he' : binaryInner x.1.left * Matrix.PSL3Four.fieldAction x.2 *
      involutionHom (graph F) (graph_sq F) x.1.right = 1 := by
    rw [mul_assoc, ← hcomm.eq, ← mul_assoc]
    exact he
  obtain ⟨hA, hs, ht⟩ := Graph.linear_field_graph_eq_one
    (SpecialLinearGroup.toGL (SpecialLinearGroup.map binaryCast x.1.left))
    x.2 x.1.right (by rwa [hlin])
  have hleft : x.1.left = 1 := binaryInner_injective (by
    simpa only [hlin, map_one] using hA)
  apply Subgroup.mem_bot.mpr
  exact Prod.ext (SemidirectProduct.ext hleft ht) hs

/-- The concrete dihedral-times-C₂ candidate embeds in the full Frobenius centralizer. -/
theorem candidateHom_injective : Function.Injective candidateHom :=
  modelHom_injective.comp candidateModelHom_injective

end
end Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement.Field
