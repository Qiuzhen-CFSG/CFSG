module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.RelativeBlocks.EndNodes.Transport
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.RelativeBlocks.EndNodes.AffineRigidity
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.RelativeBlocks.EndNodes.ParabolicAffine
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.RelativeBlocks.MiddleFlag
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.BlockObstructions

/-!
# End-node blocks and their natural binary modules

The adjacent affine calculation constructs the quotient by O₂ and the actual
conjugation module U/C_U, then transports both along a group isomorphism.
The existing component-orbit embedding places each original short subnormal
block in a finite power of the intrinsic flag stabilizer, including when S
permutes components. An affine identification of that stabilizer therefore
feeds the finite-power calculation without replacing the block by P itself.

The end-node stabilizer's affine isomorphism (with the dual action correctly
reparametrized) and rigidity of short subnormal groups in finite affine powers
are supplied by the adjacent leaves. Their assembly identifies every block
with one affine factor and constructs its natural quotient module in dimension
n-1. The original conditional interfaces are retained, followed by the complete
end-node calculation and its application to the parent's block obstruction.
The calculation applies to every block of this overgroup, so the source's
movement and escape conditions require no additional argument.

Source: Aschbacher–Smith 2.3.9(7), printed pp.525–526, and the actual
short-group and block definitions C.1.7/C.1.12, printed pp.123–124.
-/

public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open Subgroup ChapterC EndNodes

variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
  {n : ℕ} [NeZero n]

/-- The full-S flag overgroup embeds each actual block subnormally in a finite
power of the affine seed. The domain remains the original block carrier. -/
theorem block_embedding_in_affine_power (h : LocalSetup H L M S z)
    (e : L ≃* PSL n) (F : Flag n)
    (hinv : FlagInvariant e ((S : Subgroup H).map H.subtype) F)
    {d : ℕ} (eK : flagStabilizer e F ≃* Affine d)
    (B : Subgroup (flagOvergroup e F ((S : Subgroup H).map H.subtype)))
    (hB : IsBlock B) :
    ∃ (k : ℕ) (f : B →* (Fin k → Affine d)),
      Function.Injective f ∧ f.range.IsSubnormal := by
  obtain ⟨k, f, hf, hs⟩ := block_embedding_in_flag_power h e F hinv B hB
  let E := MulEquiv.piCongrRight (fun _ : Fin k => eK)
  refine ⟨k, E.toMonoidHom.comp f, E.injective.comp hf, ?_⟩
  rw [MonoidHom.range_comp]
  exact hs.map E.surjective

/-- Conditional assembly in the sharper natural dimension. Its two remaining
inputs are the seed's affine isomorphism and rigidity of short subnormal
groups in affine powers. Neither input asserts a block-module conclusion. -/
theorem linearTwoBlock_of_affine_flag_calculations (h : LocalSetup H L M S z)
    (e : L ≃* PSL n) (F : Flag n)
    (hinv : FlagInvariant e ((S : Subgroup H).map H.subtype) F)
    {d : ℕ} (hd : 2 ≤ d) (eK : flagStabilizer e F ≃* Affine d)
    (B : Subgroup (flagOvergroup e F ((S : Subgroup H).map H.subtype)))
    (hB : IsBlock B)
    (hRigidity : ∀ (k : ℕ) (f : B →* (Fin k → Affine d)),
      Function.Injective f → f.range.IsSubnormal → Nonempty (B ≃* Affine d)) :
    IsLinearTwoBlock B d := by
  obtain ⟨k, f, hf, hs⟩ := block_embedding_in_affine_power h e F hinv eK B hB
  obtain ⟨b⟩ := hRigidity k f hf hs
  exact linearTwoBlock_of_affine_equiv hd hB.short b

/-- Apply the two structural calculations to the exact source flag overgroup.
The actual block quotient and module have already been constructed above. -/
theorem endNode_block_types_of_affine_calculations (h : LocalSetup H L M S z)
    (hn : n = 4 ∨ n = 5) (e : L ≃* PSL n) (F : Flag n)
    (hinv : FlagInvariant e ((S : Subgroup H).map H.subtype) F)
    (eK : flagStabilizer e F ≃* Affine (n - 1))
    (B : Subgroup (flagOvergroup e F ((S : Subgroup H).map H.subtype)))
    (hB : IsBlock B)
    (hRigidity : ∀ (k : ℕ) (f : B →* (Fin k → Affine (n - 1))),
      Function.Injective f → f.range.IsSubnormal → Nonempty (B ≃* Affine (n - 1))) :
    IsLinearTwoBlock B 3 ∨ IsLinearTwoBlock B 4 := by
  have htype := linearTwoBlock_of_affine_flag_calculations h e F hinv
    (by omega : 2 ≤ n - 1) eK B hB hRigidity
  rcases hn with rfl | rfl
  · exact Or.inl htype
  · exact Or.inr htype

/-- The conditional calculations feed the literal relative block obstruction
used by the parent. Movement by J(S) and escape remain in its original domain;
the structural calculation is stronger and applies to every block. -/
theorem blockObstruction_of_affine_flag_calculations (h : LocalSetup H L M S z)
    (hn : n = 4 ∨ n = 5) (e : L ≃* PSL n) (F : Flag n)
    (hinv : FlagInvariant e ((S : Subgroup H).map H.subtype) F)
    (eK : flagStabilizer e F ≃* Affine (n - 1))
    (hRigidity : ∀ B : Subgroup (flagOvergroup e F ((S : Subgroup H).map H.subtype)),
      IsBlock B → ∀ (k : ℕ) (f : B →* (Fin k → Affine (n - 1))),
      Function.Injective f → f.range.IsSubnormal → Nonempty (B ≃* Affine (n - 1))) :
    BlockObstruction M ((S : Subgroup H).map H.subtype)
      (flagOvergroup e F ((S : Subgroup H).map H.subtype)) := by
  apply blockObstruction_of_binary_natural
  intro B hB _ _
  exact endNode_block_types_of_affine_calculations h hn e F hinv eK B hB (hRigidity B hB)

/-- Every actual block in an end-node flag overgroup is one affine factor.
The embedding retains subnormality relative to the full-S overgroup, including
the possibility that S permutes the components. -/
theorem endNode_block_affine_equiv (h : LocalSetup H L M S z)
    (hn : n = 4 ∨ n = 5) (e : L ≃* PSL n) {t : L}
    (ht : IsConjugationProjection L z t) (c : TransvectionCoordinates e t)
    (F : Flag n) (hF : F.types = {1} ∨ F.types = {n - 1})
    (hinv : FlagInvariant e ((S : Subgroup H).map H.subtype) F)
    (hSF : ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F)
    (B : Subgroup (flagOvergroup e F ((S : Subgroup H).map H.subtype)))
    (hB : IsBlock B) : Nonempty (B ≃* Affine (n - 1)) := by
  let eK := ParabolicAffine.flagAffineEquiv c h ht F hSF hF
  obtain ⟨k, f, hf, hs⟩ := block_embedding_in_affine_power h e F hinv eK B hB
  exact affine_equiv_of_short_subnormal_power (by omega) hB.short f hf hs

/-- The original block's quotient by O₂ and its conjugation module U/C_U are
the natural binary model of dimension n-1. All structural inputs of the earlier
conditional assembly are discharged by the end-node calculations. -/
theorem linearTwoBlock_of_endNode (h : LocalSetup H L M S z)
    (hn : n = 4 ∨ n = 5) (e : L ≃* PSL n) {t : L}
    (ht : IsConjugationProjection L z t) (c : TransvectionCoordinates e t)
    (F : Flag n) (hF : F.types = {1} ∨ F.types = {n - 1})
    (hinv : FlagInvariant e ((S : Subgroup H).map H.subtype) F)
    (hSF : ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F)
    (B : Subgroup (flagOvergroup e F ((S : Subgroup H).map H.subtype)))
    (hB : IsBlock B) : IsLinearTwoBlock B (n - 1) := by
  obtain ⟨b⟩ := endNode_block_affine_equiv h hn e ht c F hF hinv hSF B hB
  exact linearTwoBlock_of_affine_equiv (by omega) hB.short b

/-- The two binary types needed for the end-node branch of
`blockObstruction_of_flag_calculations`. This stronger calculation covers all
blocks, in particular those moved by J(S) and escaping M. -/
theorem endNode_block_types (h : LocalSetup H L M S z)
    (hn : n = 4 ∨ n = 5) (e : L ≃* PSL n) {t : L}
    (ht : IsConjugationProjection L z t) (c : TransvectionCoordinates e t)
    (F : Flag n) (hF : F.types = {1} ∨ F.types = {n - 1})
    (hinv : FlagInvariant e ((S : Subgroup H).map H.subtype) F)
    (hSF : ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F)
    (B : Subgroup (flagOvergroup e F ((S : Subgroup H).map H.subtype)))
    (hB : IsBlock B) : IsLinearTwoBlock B 3 ∨ IsLinearTwoBlock B 4 := by
  have htype := linearTwoBlock_of_endNode h hn e ht c F hF hinv hSF B hB
  rcases hn with rfl | rfl
  · exact Or.inl htype
  · exact Or.inr htype

/-- The completed end-node calculation discharges the literal relative χ₀
block obstruction. Neither an affine recognition nor a module premise remains. -/
theorem blockObstruction_of_endNode_flag (h : LocalSetup H L M S z)
    (hn : n = 4 ∨ n = 5) (e : L ≃* PSL n) {t : L}
    (ht : IsConjugationProjection L z t) (c : TransvectionCoordinates e t)
    (F : Flag n) (hF : F.types = {1} ∨ F.types = {n - 1})
    (hinv : FlagInvariant e ((S : Subgroup H).map H.subtype) F)
    (hSF : ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F) :
    BlockObstruction M ((S : Subgroup H).map H.subtype)
      (flagOvergroup e F ((S : Subgroup H).map H.subtype)) := by
  apply blockObstruction_of_binary_natural
  intro B hB _ _
  exact endNode_block_types h hn e ht c F hF hinv hSF B hB

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
end
