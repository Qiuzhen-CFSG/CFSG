module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.Local
public import Theory.SpecificGroups.SL2.Affine.Action
public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# Descending a pointwise block-layer fixer

An automorphism fixing U(L) pointwise acts trivially on its natural module.
Faithfulness identifies its induced action on L/O₂(L) with the identity.
The kernel of L/U(L) → L/O₂(L) is central. Uniqueness of maps from a
perfect group into a central extension then gives trivial action on L/U(L).
The remaining displacement takes values in U(L); it is not assumed trivial.

The Borel and its prime-to-three residual below are literal preimages and
subgroups. They provide common inputs for the remaining covering-module and
displacement arguments in Aschbacher–Smith 15.3.30, pp.1131–1132.
The central quotient observation is the first step of C.1.8, printed p.123.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo

variable {L F : Type*} [Group L] [Field F]

/-- The literal map from the block to its natural matrix actor. -/
def blockLinearMap (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F)) :
    L →* Matrix.SpecialLinearGroup (Fin 2) F :=
  model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

/-- The full preimage of the standard Borel in the actual block. -/
def blockBorel (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F)) :
    Subgroup L := (Matrix.SpecialLinearGroup.rankOneBorel F).comap (blockLinearMap model)

/-- O^{3′}(B), mapped back into the block; this is not O₃(B). -/
def blockBorelResidual (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F)) :
    Subgroup L := (primeToResidual 3 (blockBorel model)).map (blockBorel model).subtype

theorem blockLinearMap_surjective
    (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F)) :
    Function.Surjective (blockLinearMap model) :=
  model.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)

theorem blockLinearMap_ker
    (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F)) :
    (blockLinearMap model).ker = pCore 2 L := by
  ext l
  change model.quotientIso (QuotientGroup.mk' (pCore 2 L) l) = 1 ↔ l ∈ pCore 2 L
  constructor
  · intro hl
    exact (QuotientGroup.eq_one_iff l).mp
      (model.quotientIso.injective (hl.trans model.quotientIso.map_one.symm))
  · intro hl
    have he : QuotientGroup.mk' (pCore 2 L) l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
    rw [he, map_one]

/-- Faithfulness of the actual module kills the induced core-quotient action. -/
theorem coreQuotient_fixed_of_blockU_fixed
    (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F))
    (a : MulAut L) (hfix : ∀ u : ChapterC.blockU L, a u = u) (l : L) :
    QuotientGroup.mk' (pCore 2 L) (a l) = QuotientGroup.mk' (pCore 2 L) l := by
  apply model.quotientIso.injective
  apply Matrix.SL2.naturalAction_injective F
  ext v : 1
  obtain ⟨q, rfl⟩ := model.moduleIso.surjective v
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (ChapterC.blockFixed L) q
  rw [← model.intertwining, ← model.intertwining]
  have he : ChapterC.blockConjugate L (a l) u = ChapterC.blockConjugate L l u := by
    apply Subtype.ext
    change a l * (u : L) * (a l)⁻¹ = l * (u : L) * l⁻¹
    have hh := hfix (ChapterC.blockConjugate L l u)
    change a (l * (u : L) * l⁻¹) = l * (u : L) * l⁻¹ at hh
    simpa only [map_mul, map_inv, hfix u] using hh
  rw [he]

/-- The central extension above U(L) also has trivial induced action.
This uses perfectness, not a split extension or a multiplier identification. -/
theorem blockUQuotient_fixed_of_blockU_fixed [Group.IsPerfect L]
    (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F))
    (a : MulAut L) (hfix : ∀ u : ChapterC.blockU L, a u = u) (l : L) :
    QuotientGroup.mk' (ChapterC.blockU L) (a l) =
      QuotientGroup.mk' (ChapterC.blockU L) l := by
  let q := QuotientGroup.mk' (ChapterC.blockU L)
  let f : (L ⧸ ChapterC.blockU L) →* (L ⧸ pCore 2 L) :=
    QuotientGroup.lift (ChapterC.blockU L) (QuotientGroup.mk' (pCore 2 L))
      (by rw [QuotientGroup.ker_mk']; exact ChapterC.blockU_le_core)
  have hk : f.ker ≤ center (L ⧸ ChapterC.blockU L) := by
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (ChapterC.blockU L) x
    have hy : y ∈ pCore 2 L := (QuotientGroup.eq_one_iff y).mp hx
    exact ChapterC.blockU_core_image_le_center (mem_map_of_mem _ hy)
  have he := PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq
    f hk (q.comp a.toMonoidHom) q (by
      ext x : 1
      exact coreQuotient_fixed_of_blockU_fixed model a hfix x)
  exact congrArg (fun k : L →* (L ⧸ ChapterC.blockU L) => k l) he

/-- The remaining automorphism displacement lies in the elementary layer. -/
theorem displacement_mem_blockU_of_blockU_fixed [Group.IsPerfect L]
    (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F))
    (a : MulAut L) (hfix : ∀ u : ChapterC.blockU L, a u = u) (l : L) :
    a l * l⁻¹ ∈ ChapterC.blockU L := by
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' (ChapterC.blockU L) (a l * l⁻¹) = 1
  rw [map_mul, map_inv, blockUQuotient_fixed_of_blockU_fixed model a hfix,
    mul_inv_cancel]

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo

end
