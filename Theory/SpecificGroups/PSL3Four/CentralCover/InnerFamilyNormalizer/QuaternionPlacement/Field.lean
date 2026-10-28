module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.QuaternionPlacement.Field.Dihedral
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.QuaternionPlacement.Field.Faithfulness
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.QuaternionPlacement.Field.Surjectivity

/-!
# Sylow assembly for the field-involution centralizer

The concrete binary graph and field model has order 672 and covers the full
Frobenius centralizer. The concrete dihedral-times-C₂ candidate has order 32
and acts faithfully on PSL₃(4). Lagrange's theorem makes its image's index
divide 21. The image is therefore a Sylow two-subgroup, with an actual
multiplicative equivalence to D₁₆ × C₂.

`exists_sylow_model` discharges both map properties using `Surjectivity` and
`Faithfulness`. The named witnesses `sylow` and `sylowEquiv` can be passed
directly to `field_placement_of_sylow_model` in `Reduction` for the separate
quaternion-placement assembly.

Source: the field row of Aschbacher–Smith 16.1.4(4), printed p.1171, and
the quaternion-placement application on printed p.1192, `refs/quasithin.pdf`.
-/

public section
open Subgroup
namespace Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement.Field
noncomputable section

/-- A covering binary model and a faithful concrete candidate supply the actual Sylow witness. -/
theorem exists_sylow_model_of_cover_and_faithfulness
    (hcover : Function.Surjective modelHom)
    (hfaithful : Function.Injective candidateHom) :
    ∃ S : Sylow 2 C, Nonempty (S ≃* DihedralGroup 8 × C2) := by
  let e := MonoidHom.ofInjective hfaithful
  have hcard : Nat.card candidateHom.range = 32 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, DihedralGroup.nat_card, card_C2]
  have hdiv : Nat.card C ∣ 672 := by
    simpa only [card_model] using card_dvd_of_surjective modelHom hcover
  have hindex : candidateHom.range.index ∣ 21 := by
    apply (Nat.mul_dvd_mul_iff_left (by decide : 0 < 32)).mp
    change 32 * candidateHom.range.index ∣ 672
    rw [← hcard, Subgroup.card_mul_index]
    exact hdiv
  have hp : IsPGroup 2 candidateHom.range := IsPGroup.of_card (n := 5) hcard
  have hodd : ¬ 2 ∣ candidateHom.range.index := by
    intro h
    have hh := h.trans hindex
    norm_num at hh
  exact ⟨hp.toSylow hodd, ⟨e.symm⟩⟩

/-- The full Frobenius centralizer has a Sylow two-subgroup isomorphic to D₁₆ × C₂. -/
theorem exists_sylow_model :
    ∃ S : Sylow 2 C, Nonempty (S ≃* DihedralGroup 8 × C2) :=
  exists_sylow_model_of_cover_and_faithfulness modelHom_surjective candidateHom_injective

/-- A Sylow two-subgroup of the full automorphism centralizer of Frobenius. -/
def sylow : Sylow 2 C := Classical.choose exists_sylow_model

/-- The chosen Sylow subgroup's multiplicative equivalence with D₁₆ × C₂. -/
def sylowEquiv : sylow ≃* DihedralGroup 8 × C2 :=
  Classical.choice (Classical.choose_spec exists_sylow_model)

end
end Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement.Field
