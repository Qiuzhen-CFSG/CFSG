module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Interface
public import Theory.GroupTheory.PResidual.AbelianSquareObstruction
public import Theory.Mathieu.M12.BlockGeometry.Defs

/-!
# The M₁₂ block calculation through its full second parabolic

The supplied quotient map has kernel exactly O₂(L). A model parabolic is
pulled back along this map, embedded in G, and joined with the supplied
Sylow subgroup. Generation uses the image of the actual C_L(z), so a fixed
point modulo the central kernel is never silently treated as a fixed lift.

A normal section of this overgroup maps onto a finite direct power of the
full second parabolic, with two-group kernels below and above. The square
obstruction then rules out every short subnormal group in the overgroup:
its actual U(B) = [O₂(B),B] is elementary by C.1.7. No classification of
abstract groups of the same order, module labels, or ambient subnormality
of B is used.

`LocalGeometry` is the remaining geometric construction. It contains no
block-exclusion conclusion. The constructor below is conditional on that
geometry and the independently constructed square control. The importing
M12 module supplies the concrete square control; its invariant model seed
and central-cover transport still need to be supplied before the source
branch is complete.

Source: Aschbacher–Smith, 2.3.9(7), printed p.526, C.1.7, printed p.123,
and GLS3, Table 5.3b, the (4 × 4).D₁₂ local subgroup.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.M12Exclusion
open ChapterC Sporadic.Mathieu Sporadic.Mathieu.M12SmallPair
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The specified model isomorphism after the actual two-core quotient. -/
noncomputable def quotientMap (d : SporadicQuotientInput L z .m12) : L →* M12 :=
  d.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

/-- Surjectivity is inherited from the source quotient identification. -/
theorem quotientMap_surjective (d : SporadicQuotientInput L z .m12) :
    Function.Surjective (quotientMap d) :=
  d.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)

/-- The retained kernel is exactly O₂(L). -/
theorem quotientMap_ker (d : SporadicQuotientInput L z .m12) :
    (quotientMap d).ker = pCore 2 L := by
  ext x
  change d.quotientIso (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ x ∈ pCore 2 L
  rw [map_eq_one_iff d.quotientIso d.quotientIso.injective]
  exact QuotientGroup.eq_one_iff x

/-- The image of genuinely centralizing elements in the component. -/
noncomputable def centralizerImage (d : SporadicQuotientInput L z .m12) : Subgroup M12 :=
  ((centralizer ({z} : Set G)).subgroupOf L).map (quotientMap d)

/-- The full inverse image, embedded in G without removing its central kernel. -/
noncomputable def componentPreimage (d : SporadicQuotientInput L z .m12)
    (P : Subgroup M12) : Subgroup G := (P.comap (quotientMap d)).map L.subtype

/-- Adjoin the supplied subgroup; it may permute conjugate components of H. -/
noncomputable def localOvergroup (A : Subgroup G) (d : SporadicQuotientInput L z .m12)
    (P : Subgroup M12) : Subgroup G := componentPreimage d P ⊔ A

/-- The lifted parabolic stays in the distinguished component. -/
theorem componentPreimage_le (d : SporadicQuotientInput L z .m12)
    (P : Subgroup M12) : componentPreimage d P ≤ L := map_subtype_le _

/-- The construction contains the actual supplied subgroup. -/
theorem le_localOvergroup (A : Subgroup G) (d : SporadicQuotientInput L z .m12)
    (P : Subgroup M12) : A ≤ localOvergroup A d P := le_sup_right

/-- The construction lies in the required join LS. -/
theorem localOvergroup_le (A : Subgroup G) (d : SporadicQuotientInput L z .m12)
    (P : Subgroup M12) : localOvergroup A d P ≤ L ⊔ A :=
  sup_le_sup (componentPreimage_le d P) le_rfl

/-- The whole embedded two-kernel survives in every constructed overgroup. -/
theorem pCoreIn_le_localOvergroup (A : Subgroup G) (d : SporadicQuotientInput L z .m12)
    (P : Subgroup M12) : L.pCoreIn 2 ≤ localOvergroup A d P := by
  apply le_trans (map_mono (f := L.subtype) ?_) le_sup_left
  rw [← quotientMap_ker d]
  exact MonoidHom.ker_le_comap _ _

/-- Generation lifts because the full kernel is already in the lifted parabolic. -/
theorem generated_of_model_join (A : Subgroup G) (d : SporadicQuotientInput L z .m12)
    (P : Subgroup M12) (hg : centralizerImage d ⊔ P = ⊤) :
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

/-- The outstanding geometry and full-parabolic section, without a block premise. -/
structure LocalGeometry (A : Subgroup G) (d : SporadicQuotientInput L z .m12) where
  localSubgroup : Subgroup M12
  modelIso : localSubgroup ≃* secondParabolic
  generated : centralizerImage d ⊔ localSubgroup = ⊤
  even : localOvergroup A d localSubgroup ∈ Chapter1.He G
  sectionCover : NormalPowerCover 2 (localOvergroup A d localSubgroup) secondParabolic

/-- Characteristic two and the supplied involution make the core nontrivial. -/
theorem localOvergroup_mem_HeOver (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .m12)
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

/-- Shortness supplies elementary U, so the proved square obstruction applies. -/
theorem not_short_of_normalPowerCover {K A : Type*} [Group K] [Finite K] [Group A] [Finite A]
    (control : AbelianSquareControl A) (c : NormalPowerCover 2 K A)
    (B : Subgroup K) (hB : B.IsSubnormal) : ¬ IsShort B := by
  intro hs
  have hu : ∀ u ∈ (⁅pCore 2 B, (⊤ : Subgroup B)⁆).map B.subtype, u ^ 2 = 1 := by
    change ∀ u ∈ (blockU B).map B.subtype, u ^ 2 = 1
    let : IsElementaryAbelian 2 (blockU B) := hs.elementary
    let : IsElementaryAbelian 2 ((blockU B).map B.subtype) := IsElementaryAbelian.map_subtype
    exact fun u hu => elemPow_eq_one_of_isElementaryAbelian u hu
  have hzero := eq_bot_of_square_control_normal_cover control c B hB hs.twoPerfect hu
  have htriv : ∀ b : B, b = 1 := by
    intro b
    apply Subtype.ext
    exact mem_bot.mp (hzero ▸ b.property)
  apply hs.blockU_ne_bot
  apply eq_bot_iff.mpr
  intro b _
  exact htriv b

/-- Conditional source assembly from the geometry and the square calculation. -/
noncomputable def centralizerBlockCover_of_geometry
    (control : AbelianSquareControl secondParabolic) (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .m12)
    (g : LocalGeometry ((S : Subgroup H).map H.subtype) d) :
    CentralizerBlockCover L M ((S : Subgroup H).map H.subtype) z := by
  let := h.finite
  let K := localOvergroup ((S : Subgroup H).map H.subtype) d g.localSubgroup
  refine { locals := {K}, generated := ?_, within := ?_, even := ?_, obstruction := ?_ }
  · simpa only [sSup_singleton] using generated_of_model_join _ d g.localSubgroup g.generated
  · intro J hJ
    have he : J = K := Set.mem_singleton_iff.mp hJ
    subst J
    exact localOvergroup_le _ d g.localSubgroup
  · intro J hJ
    have he : J = K := Set.mem_singleton_iff.mp hJ
    subst J
    exact localOvergroup_mem_HeOver h d g
  · intro J hJ
    have he : J = K := Set.mem_singleton_iff.mp hJ
    subst J
    intro B hb _
    exact (not_short_of_normalPowerCover control g.sectionCover B hb.1.subnormal hb.1.short).elim
end CFSG.Quasithin.Chapter2.ComponentRefinement.M12Exclusion

end
