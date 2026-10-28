module
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Nonabelian
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# Binary PSL₃ and PSL₂ have different Sylow two-subgroups

The actual PSL₃ Sylow has nontrivial commutators, while every defining
Sylow of SL₂ is the additive field. The characteristic-two SL₂–PSL₂
equivalence preserves this obstruction in every field degree.

Source: the unipotent matrix Sylow models, as in E.6.11(3b) of
Aschbacher–Smith, printed pp.249–250, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace Matrix.PSL3.LinearThree
variable {F E : Type*} [Field F] [Finite F] [Field E] [Finite E] [CharP E 2]

/-- A binary projective linear-three group is never a binary PSL₂. -/
theorem not_equiv_linear_two {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) : ¬ Nonempty (PSL(3,F) ≃* PSL(2,E)) := by
  rintro ⟨e⟩
  let f := e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := E)).symm
  let S : Sylow 2 PSL(3,F) := Classical.arbitrary _
  let P := S.mapSurjective (f := f.toMonoidHom) f.surjective
  let : IsMulCommutative P :=
    ⟨⟨fun x y => (SpecialLinearGroup.sylowEquivAdditive E 2 P).symm.injective
      (by rw [map_mul, map_mul]; exact mul_comm _ _)⟩⟩
  apply sylow_not_isMulCommutative F hn hF S
  let r : S →* P := f.toMonoidHom.subgroupMap (S : Subgroup PSL(3,F))
  refine ⟨⟨fun x y => ?_⟩⟩
  apply Subtype.ext
  apply f.injective
  exact congrArg Subtype.val (show r (x * y) = r (y * x) by
    rw [map_mul, map_mul]
    exact mul_comm _ _)

end Matrix.PSL3.LinearThree
