module
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.Maps
public import Theory.SpecificGroups.ReeTwo.ParabolicIndexTwo.Kernels

/-!
# The actual Tits intersection is the mixed-character kernel

Each positive Parrott generator and the first reflection has an explicit
preimage killed by the mixed character. The marked Tits first parabolic
therefore lies in the mixed-kernel image. Both have the already proved
order 10240, so the inclusion is equality. The ambient marked-comparison
theorem then identifies this image with the first parabolic intersected
with the actual derived group. This determines the character from the
specified embeddings, rather than guessing it from a quotient order.

Restriction gives compatible Tits first-parabolic, Sylow and overlap maps,
and preserves both intrinsic cores. The finite ambient root identities
remain the explicit `Ambient.Relations` premise, discharged by the final
assembly owner after their separate matrix verification.

Sources: Parrott (1972), pp.672,683; Aschbacher (1982), Section 3;
Aschbacher–Smith 14.2.21, printed p.989.
-/

@[expose] public section
noncomputable section
namespace ReeTwo.ParabolicMarkedComparison
open ReeF4 Tits.ExceptionalParabolics
open Centralizer.IndexTwo

/-- The eight positive Parrott generators, in their printed order. -/
def positiveIndex : Fin 8 → Tits.ParrottGenerator :=
  ![.s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8]

/-- Their literal coordinate-model preimages. -/
def positiveWord : Fin 8 → Centralizer :=
  ![Centralizer.rootOne * Centralizer.rootOne, Centralizer.root 4,
    Centralizer.rootOne * Centralizer.root 3, Centralizer.root 7,
    Centralizer.rootOne * Centralizer.root 2, Centralizer.root 6,
    Centralizer.root 1 * Centralizer.rootOne⁻¹, Centralizer.root 0]

private theorem mixed_root (i : CoreRoot) :
    Centralizer.mixedCharacter (Centralizer.root i) = Core.binaryCharacter (Core.root i) :=
  mixedCharacter_inl _

private theorem mixed_rootOne :
    Centralizer.mixedCharacter Centralizer.rootOne = FiveFour.generator 2 := by
  rw [← SylowModel.embedding_rootOne, Centralizer.mixedCharacter_embedding,
    SylowModel.mixedCharacter_rootOne]
  decide +kernel

/-- Every positive Parrott generator lies in the mixed kernel. -/
theorem positiveWord_mem_mixed (i : Fin 8) : positiveWord i ∈ mixedLocal := by
  change Centralizer.mixedCharacter (positiveWord i) = 1
  fin_cases i <;> simp [positiveWord, mixed_root, mixed_rootOne] <;> decide +kernel

/-- The actual first reflection also lies in the mixed kernel. -/
theorem weyl_mem_mixed : Centralizer.weyl ∈ mixedLocal := by
  change Centralizer.mixedCharacter Centralizer.weyl = 1
  have he : Centralizer.weyl = Centralizer.rootOne ^ 2 * Centralizer.fiveGenerator := by
    simp only [Centralizer.weyl, Centralizer.rootOne, Centralizer.fiveGenerator,
      map_mul, map_pow, map_inv]
    group
  rw [he, map_mul, map_pow, mixed_rootOne, mixedCharacter_fiveGenerator]
  decide +kernel

variable (h : Ambient.Relations)

theorem map_positiveWord (i : Fin 8) :
    localMap h (positiveWord i) =
      FullRee.atlasEmbedding (Tits.atlas1600ParrottAssignment (positiveIndex i)) := by
  rw [Ambient.atlas_generator]
  fin_cases i <;> simp [positiveWord, positiveIndex, Ambient.parrottWord]

private theorem atlas_sylow_le_mixed_image :
    Tits.ExceptionalParabolics.S.map FullRee.atlasEmbedding ≤ mixedLocal.map (localMap h) := by
  rw [Subgroup.map_le_iff_le_comap, Tits.ExceptionalParabolics.S,
    Tits.atlas1600SylowTwoSubgroup_eq]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  have hm (i : Fin 8) : Tits.atlas1600ParrottAssignment (positiveIndex i) ∈
      (mixedLocal.map (localMap h)).comap FullRee.atlasEmbedding :=
    ⟨positiveWord i, positiveWord_mem_mixed i, map_positiveWord h i⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hm 7
  · exact hm 6
  · exact hm 5
  · exact hm 4
  · exact hm 3
  · exact hm 2
  · exact hm 1
  · exact hm 0

private theorem atlas_first_le_mixed_image :
    Tits.ExceptionalParabolics.first.map FullRee.atlasEmbedding ≤
      mixedLocal.map (localMap h) := by
  rw [Tits.ExceptionalParabolics.first, Subgroup.map_sup]
  apply sup_le (atlas_sylow_le_mixed_image h)
  rw [Subgroup.map_le_iff_le_comap]
  apply (Subgroup.closure_le _).mpr
  rintro x (rfl : x = Tits.atlas1600ParrottAssignment .r1)
  exact ⟨Centralizer.weyl, weyl_mem_mixed, (localMap_weyl h).trans
    (Ambient.atlas_generator .r1).symm⟩

/-- The mixed kernel maps onto the actual marked Tits first parabolic. -/
theorem mixed_image : mixedLocal.map (localMap h) =
    Tits.ExceptionalParabolics.first.map FullRee.atlasEmbedding := by
  symm
  apply Subgroup.eq_of_le_of_card_ge (atlas_first_le_mixed_image h)
  rw [Subgroup.card_map_of_injective (localMap_injective h),
    Subgroup.card_map_of_injective FullRee.atlasEmbedding_injective,
    alternative_card _ (Or.inr rfl), Tits.ExceptionalParabolics.first_card]

/-- The ambient derived-group preimage is exactly the actual mixed character kernel. -/
theorem derived_preimage :
    (commutator (Model 0)).comap (localMap h) = mixedLocal := by
  apply Subgroup.map_injective (localMap_injective h)
  rw [Subgroup.map_comap_eq, localMap_range, mixed_image, FullRee.atlas_first_map, inf_comm]

/-- Restriction and the inverse Atlas embedding give the marked Tits local isomorphism. -/
def titsFirstEquiv : mixedLocal ≃* Tits.ExceptionalParabolics.first :=
  ((mixedLocal.equivMapOfInjective (localMap h) (localMap_injective h)).trans
    (MulEquiv.subgroupCongr (mixed_image h))).trans
    (Tits.ExceptionalParabolics.first.equivMapOfInjective FullRee.atlasEmbedding
      FullRee.atlasEmbedding_injective).symm

/-- The restricted comparison uses exactly the original ambient root map. -/
theorem titsFirstEquiv_coe (g : mixedLocal) :
    FullRee.atlasEmbedding (titsFirstEquiv h g : Tits.Atlas1600Group) = localMap h g := by
  have he := (Tits.ExceptionalParabolics.first.equivMapOfInjective FullRee.atlasEmbedding
      FullRee.atlasEmbedding_injective).apply_symm_apply
      (MulEquiv.subgroupCongr (mixed_image h)
        (mixedLocal.equivMapOfInjective (localMap h) (localMap_injective h) g))
  exact congrArg Subtype.val he


/-- The source Sylow subgroup in the Tits local group. -/
abbrev titsSylow := SylowModel.mixedCharacter.ker

/-- Its inclusion into the mixed local group retains the original Sylow embedding. -/
def titsSylowInclusion : titsSylow →* mixedLocal :=
  ((SylowModel.embedding).comp titsSylow.subtype).codRestrict mixedLocal (by
    intro g
    change Centralizer.mixedCharacter (SylowModel.embedding g) = 1
    rw [Centralizer.mixedCharacter_embedding]
    exact g.property)

@[simp] theorem titsSylowInclusion_coe (g : titsSylow) :
    (titsSylowInclusion g : Centralizer) = SylowModel.embedding g := rfl

theorem titsSylow_preimage :
    (commutator (Model 0)).comap (sylowMap h) = titsSylow := by
  rw [sylowMap, ← Subgroup.comap_comap, derived_preimage]
  ext g
  exact (Centralizer.mixedCharacter_embedding g).congr_left

/-- The kernel Sylow maps onto the actual marked Atlas Sylow intersection. -/
theorem titsSylow_image : titsSylow.map (sylowMap h) =
    Tits.ExceptionalParabolics.S.map FullRee.atlasEmbedding := by
  rw [← titsSylow_preimage h, Subgroup.map_comap_eq, sylowMap_range,
    FullRee.atlas_sylow_map, inf_comm]

def titsSylowEquiv : titsSylow ≃* Tits.ExceptionalParabolics.S :=
  ((titsSylow.equivMapOfInjective (sylowMap h) (sylowMap_injective h)).trans
    (MulEquiv.subgroupCongr (titsSylow_image h))).trans
    (Tits.ExceptionalParabolics.S.equivMapOfInjective FullRee.atlasEmbedding
      FullRee.atlasEmbedding_injective).symm

theorem titsSylowEquiv_coe (g : titsSylow) :
    FullRee.atlasEmbedding (titsSylowEquiv h g : Tits.Atlas1600Group) = sylowMap h g := by
  have he := (Tits.ExceptionalParabolics.S.equivMapOfInjective FullRee.atlasEmbedding
      FullRee.atlasEmbedding_injective).apply_symm_apply
      (MulEquiv.subgroupCongr (titsSylow_image h)
        (titsSylow.equivMapOfInjective (sylowMap h) (sylowMap_injective h) g))
  exact congrArg Subtype.val he

/-- Both Tits comparisons use the same maps on the common Sylow subgroup. -/
theorem titsSylow_first_commutes (g : titsSylow) :
    Subgroup.inclusion Tits.ExceptionalParabolics.sylow_le_first (titsSylowEquiv h g) =
      titsFirstEquiv h (titsSylowInclusion g) := by
  apply Subtype.ext
  apply FullRee.atlasEmbedding_injective
  rw [titsFirstEquiv_coe]
  exact titsSylowEquiv_coe h g

/-- This Sylow image is also the whole Atlas overlap. -/
theorem titsSylow_image_overlap : titsSylow.map (sylowMap h) =
    Tits.ExceptionalParabolics.overlap.map FullRee.atlasEmbedding := by
  rw [Tits.ExceptionalParabolics.overlap_eq_sylow, titsSylow_image]

/-- The full comparison carries the specified ten-root core to the intrinsic core. -/
theorem firstEquiv_core : Centralizer.core.map (firstEquiv h).toMonoidHom =
    pCore 2 FullRee.first := by
  rw [Centralizer.core_eq_pCore, pCore_map_iso]

/-- The Tits comparison carries the actual order-512 core to the intrinsic Atlas core. -/
theorem titsFirstEquiv_core :
    (Centralizer.core.subgroupOf mixedLocal).map (titsFirstEquiv h).toMonoidHom =
      pCore 2 Tits.ExceptionalParabolics.first := by
  rw [core_subgroupOf_eq_pCore, pCore_map_iso]


/-- The last source root in the actual mixed kernel. -/
def mixedLastRoot : mixedLocal := ⟨Centralizer.root 9, by
  change Centralizer.mixedCharacter (Centralizer.root 9) = 1
  rw [mixed_root]
  decide +kernel⟩

/-- Restriction retains the marked central involution in Atlas coordinates. -/
theorem titsFirstEquiv_last_root :
    (titsFirstEquiv h mixedLastRoot : Tits.Atlas1600Group) = Tits.atlas1600R5 := by
  apply FullRee.atlasEmbedding_injective
  rw [titsFirstEquiv_coe, atlas_last_root h]
  exact localMap_root h 9

end ReeTwo.ParabolicMarkedComparison
