module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Interface
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.BlockGeometry

/-!
# Quotient preimages for the Hall–Janko block exclusion

Use the specified degree-100 quotient of the component, pull back the full
second parabolic, and adjoin the supplied Sylow subgroup. All of the central
two-kernel survives. Generation uses the image of actual centralizing lifts,
not the full centralizer in the quotient. Characteristic two then makes the
local two-core nontrivial, since the local contains the supplied involution.

The invariant geometry is constructed in `Transport`. The remaining native
subnormal calculation is separate from these quotient and containment lemmas.
Source: Aschbacher–Smith, 2.3.9(7), printed p.526; F.1.12(I)(10), p.263.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.HallJanko
open ChapterC Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.ExceptionalParabolics
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The specified model isomorphism after the actual two-core quotient. -/
noncomputable def quotientMap (d : SporadicQuotientInput L z .j2) : L →* Carrier :=
  d.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

/-- Surjectivity is inherited from the source quotient identification. -/
theorem quotientMap_surjective (d : SporadicQuotientInput L z .j2) :
    Function.Surjective (quotientMap d) :=
  d.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)

/-- The retained kernel is exactly O₂(L). -/
theorem quotientMap_ker (d : SporadicQuotientInput L z .j2) :
    (quotientMap d).ker = pCore 2 L := by
  ext x
  change d.quotientIso (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ x ∈ pCore 2 L
  rw [map_eq_one_iff d.quotientIso d.quotientIso.injective]
  exact QuotientGroup.eq_one_iff x

/-- The image of genuinely centralizing elements in the component. -/
noncomputable def centralizerImage (d : SporadicQuotientInput L z .j2) : Subgroup Carrier :=
  ((centralizer ({z} : Set G)).subgroupOf L).map (quotientMap d)

/-- The full inverse image, embedded in G without removing its central kernel. -/
noncomputable def componentPreimage (d : SporadicQuotientInput L z .j2)
    (P : Subgroup Carrier) : Subgroup G := (P.comap (quotientMap d)).map L.subtype

/-- Adjoin the supplied subgroup; it may permute conjugate components of H. -/
noncomputable def localOvergroup (A : Subgroup G) (d : SporadicQuotientInput L z .j2)
    (P : Subgroup Carrier) : Subgroup G := componentPreimage d P ⊔ A

/-- The lifted parabolic stays in the distinguished component. -/
theorem componentPreimage_le (d : SporadicQuotientInput L z .j2)
    (P : Subgroup Carrier) : componentPreimage d P ≤ L := map_subtype_le _

/-- The construction contains the actual supplied subgroup. -/
theorem le_localOvergroup (A : Subgroup G) (d : SporadicQuotientInput L z .j2)
    (P : Subgroup Carrier) : A ≤ localOvergroup A d P := le_sup_right

/-- The construction lies in the required join LS. -/
theorem localOvergroup_le (A : Subgroup G) (d : SporadicQuotientInput L z .j2)
    (P : Subgroup Carrier) : localOvergroup A d P ≤ L ⊔ A :=
  sup_le_sup (componentPreimage_le d P) le_rfl

/-- The whole embedded two-kernel survives in every constructed overgroup. -/
theorem pCoreIn_le_localOvergroup (A : Subgroup G) (d : SporadicQuotientInput L z .j2)
    (P : Subgroup Carrier) : L.pCoreIn 2 ≤ localOvergroup A d P := by
  apply le_trans (map_mono (f := L.subtype) ?_) le_sup_left
  rw [← quotientMap_ker d]
  exact MonoidHom.ker_le_comap _ _

/-- Generation lifts because the full kernel is already in the lifted parabolic. -/
theorem generated_of_model_join (A : Subgroup G) (d : SporadicQuotientInput L z .j2)
    (P : Subgroup Carrier) (hg : centralizerImage d ⊔ P = ⊤) :
    L ≤ centralizer ({z} : Set G) ⊔ localOvergroup A d P := by
  let U := centralizer ({z} : Set G) ⊔ localOvergroup A d P
  have hP : P ≤ (U.subgroupOf L).map (quotientMap d) := by
    intro x hx
    obtain ⟨y, rfl⟩ := quotientMap_surjective d x
    refine ⟨y, ?_, rfl⟩
    exact (show localOvergroup A d P ≤ U from le_sup_right)
      ((show componentPreimage d P ≤ localOvergroup A d P from le_sup_left) ⟨y, hx, rfl⟩)
  have hC : centralizerImage d ≤ (U.subgroupOf L).map (quotientMap d) :=
    map_mono (comap_mono le_sup_left)
  have htop : (U.subgroupOf L).map (quotientMap d) = ⊤ :=
    top_unique (hg ▸ sup_le hC hP)
  have hk : (quotientMap d).ker ≤ U.subgroupOf L := by
    intro x hx
    apply (show localOvergroup A d P ≤ U from le_sup_right)
    apply (show componentPreimage d P ≤ localOvergroup A d P from le_sup_left)
    exact ⟨x, MonoidHom.ker_le_comap _ _ hx, rfl⟩
  have he := congrArg (Subgroup.comap (quotientMap d)) htop
  have hU : U.subgroupOf L = ⊤ := by
    simpa only [comap_map_eq, sup_eq_left.mpr hk, comap_top] using he
  exact subgroupOf_eq_top.mp hU

/-- The geometry and relative normalization, without a block premise. -/
structure LocalGeometry (A : Subgroup G) (d : SporadicQuotientInput L z .j2) where
  localSubgroup : Subgroup Carrier
  modelIso : localSubgroup ≃* Seed.p₂
  generated : centralizerImage d ⊔ localSubgroup = ⊤
  even : localOvergroup A d localSubgroup ∈ Chapter1.He G
  normalized : A ⊓ normalizer (L : Set G) ≤
    normalizer (componentPreimage d localSubgroup : Set G)

/-- Characteristic two and the supplied involution make the core nontrivial. -/
theorem localOvergroup_mem_HeOver (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .j2)
    (g : LocalGeometry ((S : Subgroup H).map H.subtype) d) :
    localOvergroup ((S : Subgroup H).map H.subtype) d g.localSubgroup ∈
      Chapter1.HeOver G (((S : Subgroup H).map H.subtype) : Set G) := by
  let K := localOvergroup ((S : Subgroup H).map H.subtype) d g.localSubgroup
  have hz : z ∈ K := le_localOvergroup _ d g.localSubgroup h.mem_sylow
  refine ⟨g.even, ?_, le_localOvergroup _ d g.localSubgroup⟩
  change K.pCoreIn 2 ≠ ⊥
  intro he
  have hc : z ∈ centralizer (K.pCoreIn 2 : Set G) := by
    apply mem_centralizer_iff.mpr
    intro y hy
    have hy : y = 1 := by simpa only [he, Subgroup.coe_bot, Set.mem_singleton_iff] using hy
    simp [hy]
  have hm := g.even ⟨hz, hc⟩
  rw [he, mem_bot] at hm
  have := h.involution
  rw [hm, orderOf_one] at this
  norm_num at this

end CFSG.Quasithin.Chapter2.ComponentRefinement.HallJanko

end
