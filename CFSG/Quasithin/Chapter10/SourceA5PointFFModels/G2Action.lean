module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2ActionTransport
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2Image
public import CFSG.Quasithin.Chapter4.Defs
public import Theory.GroupTheory.CommutatorPreimage.Membership

/-!
# The G₂ moving cubic from the actual local A₅ section

The literal local section forces field order four through the specified
actor marking. The natural-action theorem then moves the given nonzero
full-Sylow fixed vector, and its core commutator bound places the cubic in
the original model subgroup's section centralizer. This removes the model
movement premise for the G₂ branch of the original-group lifting argument.

Source: Aschbacher–Smith 10.2.9, printed pp.751–752.
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter10
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings.FiveLocalFF
open ChapterB.QuasisimpleSource Chapter4
noncomputable section
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V}

theorem source_a5_point_g2_ff_moving_cubic
    {F : BinaryField} (hlarge : 1 < F.degree)
    (e : ActionEquiv ρ (restrictScalars (k := ZMod 2) (g2Natural F.Carrier)))
    (S : Sylow 2 D) (B : Subgroup D) (hB : B ∈ localCComponents S)
    (hproper : B ≠ ⊤) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (v : V) (hv : v ≠ 0) (hfix : ∀ s ∈ (S : Subgroup D), ρ s v = v) :
    ∃ x : D, orderOf x = 3 ∧ x ∈ sectionCentralizer B ∧ ρ x v ≠ v := by
  let a := e.groupEquiv
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
  have hq : 2 < Nat.card F.Carrier := by
    rw [F.card_eq]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree))
  have hF : Nat.card F.Carrier = 4 :=
    (G2.five_section_image hq a.toMonoidHom a.surjective
      hks S B hB hk hp eB).1
  obtain ⟨x,ho,hn,hc,hm⟩ := marked_g2_local_moving_cubic ρ F hF e S B hB hproper v hv hfix
  exact ⟨x,ho,(mem_commutatorPreimage_iff _ _ _
    (normalizer_le_normalizer_characteristic_image B (pCore 2 B)) x).mpr ⟨hn,hc⟩,hm⟩
end
end CFSG.Quasithin.Chapter10
