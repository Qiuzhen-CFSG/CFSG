module
public import CFSG.Quasithin.Chapter10.SourceA5PointFFModels.LinearAction
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SpecialLinearThree

/-!
# The linear-three moving cubic from the actual local A₅ section

The specified group marking transports the local component to SL₃. The
local-section sieve forces field order four. The actual natural or repeated
natural action then supplies a cubic in the original section centralizer
moving the specified nonzero vector. Thus neither the field size nor a
model movement assertion remains an input to the point-action consumer.

Source: Aschbacher–Smith B.5.1 and 10.2.9, pp.99–103 and 751–752.
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter10
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings.FiveLocalFF
open ChapterB.QuasisimpleSource Chapter4
noncomputable section
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V}

private theorem linear_field_four_of_local_section {F : BinaryField}
    (a : D ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier)
    (S : Sylow 2 D) (B : Subgroup D) (hB : B ∈ localCComponents S)
    (hproper : B ≠ ⊤) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    Nat.card F.Carrier = 4 := by
  have hks : Group.IsSolvable a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]
    infer_instance
  have hi : Function.Injective (a.toMonoidHom.subgroupMap B) := by
    intro x y h
    exact Subtype.ext (a.injective (congrArg Subtype.val h))
  have hk : IsPGroup 2 (a.toMonoidHom.subgroupMap B).ker := by
    rw [(a.toMonoidHom.subgroupMap B).ker_eq_bot_iff.mpr hi]
    exact IsPGroup.of_subsingleton 2 _
  have hp : B.map a.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hproper
    apply Subgroup.map_injective (f := a.toMonoidHom) a.injective
    rw [ht,map_top_of_surjective _ a.surjective]
  exact (special_linear_three_five_section_image F.card_eq a.toMonoidHom a.surjective
    hks S B hB hk hp eB).1

theorem source_a5_point_linear_ff_moving_cubic
    {F : BinaryField} (e : ActionEquiv ρ (linearNatural F 3))
    (S : Sylow 2 D) (B : Subgroup D) (hB : B ∈ localCComponents S)
    (hproper : B ≠ ⊤) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    {v : V} (hv : v ≠ 0) :
    ∃ x : D, orderOf x = 3 ∧ x ∈ sectionCentralizer B ∧ ρ x v ≠ v :=
  source_a5_point_linear_natural_cubic
    (linear_field_four_of_local_section e.groupEquiv S B hB hproper eB) e B hv

theorem source_a5_point_repeated_linear_ff_moving_cubic
    {F : BinaryField} {r : ℕ} (e : ActionEquiv ρ (repeated (linearNatural F 3) r))
    (S : Sylow 2 D) (B : Subgroup D) (hB : B ∈ localCComponents S)
    (hproper : B ≠ ⊤) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    {v : V} (hv : v ≠ 0) :
    ∃ x : D, orderOf x = 3 ∧ x ∈ sectionCentralizer B ∧ ρ x v ≠ v :=
  source_a5_point_linear_repeated_cubic
    (linear_field_four_of_local_section e.groupEquiv S B hB hproper eB) e B hv
end
end CFSG.Quasithin.Chapter10
