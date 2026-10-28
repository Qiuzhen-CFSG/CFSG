module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.Embedding
public import Theory.GroupTheory.PResidual.PrimeToTransport

/-!
# From a short block to the literal central coefficient module

For a short group L, the intrinsic U(L) maps isomorphically onto the ambient
commutator core Q. Elementary abelianness makes Q its own center. We transport
the full fixed subgroup, the quotient and conjugation, producing `CenterModel`
from the actual natural-module identification in the block hypothesis.
The actor map is unchanged, so its O^{3′} parabolic marking is preserved.

Source: Aschbacher--Smith, C.1.7, C.1.12--13, and the centralizing branch
of 15.3.31, combined manuscript (1 March 2004), printed pp.123--125 and 1132.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover.BlockModels
variable {G : Type*} [Group G] {L : Subgroup G}

/-- The intrinsic block commutator has the prescribed ambient image. -/
theorem blockU_map (L : Subgroup G) :
    (ChapterC.blockU L).map L.subtype = extensionCore L := by
  rw [ChapterC.blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  rfl

/-- In a short group the actual commutator core is its own center. -/
theorem coreCenter_eq_of_short (h : ChapterC.IsShort L) :
    coreCenter L = extensionCore L := by
  apply inf_eq_left.mpr
  let := h.elementary
  have he : IsElementaryAbelian 2 (extensionCore L) :=
    blockU_map L ▸ (IsElementaryAbelian.map_subtype :
      IsElementaryAbelian 2 ((ChapterC.blockU L).map L.subtype))
  let := he
  exact le_centralizer_iff_isMulCommutative.mpr inferInstance

/-- The identification retains the original ambient element. -/
noncomputable def blockCenterEquiv (h : ChapterC.IsShort L) :
    ChapterC.blockU L ≃* coreCenter L :=
  ((ChapterC.blockU L).equivMapOfInjective L.subtype L.subtype_injective).trans
    (MulEquiv.subgroupCongr ((blockU_map L).trans (coreCenter_eq_of_short h).symm))

@[simp] theorem blockCenterEquiv_coe (h : ChapterC.IsShort L) (u : ChapterC.blockU L) :
    (blockCenterEquiv h u : G) = (u : L) := rfl

theorem blockCenterEquiv_conjugate (h : ChapterC.IsShort L) (l : L)
    (u : ChapterC.blockU L) :
    blockCenterEquiv h (ChapterC.blockConjugate L l u) =
      centerConjugate L l (blockCenterEquiv h u) := by
  apply Subtype.ext
  rfl

/-- The intrinsic fixed subgroup becomes the literal ambient centralizer. -/
theorem blockCenterEquiv_fixed (h : ChapterC.IsShort L) :
    (ChapterC.blockFixed L).map (blockCenterEquiv h).toMonoidHom = centerKernel L := by
  ext z
  obtain ⟨u, rfl⟩ := (blockCenterEquiv h).surjective z
  rw [show (blockCenterEquiv h) u ∈ (ChapterC.blockFixed L).map
    (blockCenterEquiv h).toMonoidHom ↔ u ∈ ChapterC.blockFixed L from
      mem_map_iff_mem (f := (blockCenterEquiv h).toMonoidHom) (blockCenterEquiv h).injective]
  change (u : L) ∈ center L ↔ (u : L).val ∈ centralizer (L : Set G)
  rw [mem_center_iff, mem_centralizer_iff]
  constructor
  · intro hu l hl
    exact congrArg Subtype.val (hu ⟨l, hl⟩)
  · intro hu l
    exact Subtype.ext (hu l l.property)

/-- The two coefficient quotients are isomorphic with their full central kernels. -/
noncomputable def blockCenterQuotientEquiv (h : ChapterC.IsShort L) :
    ChapterC.BlockModule L ≃* CenterQuotient L :=
  QuotientGroup.congr _ _ (blockCenterEquiv h) (blockCenterEquiv_fixed h)

@[simp] theorem blockCenterQuotientEquiv_mk (h : ChapterC.IsShort L)
    (u : ChapterC.blockU L) :
    blockCenterQuotientEquiv h (QuotientGroup.mk' (ChapterC.blockFixed L) u) =
      QuotientGroup.mk' (centerKernel L) (blockCenterEquiv h u) := rfl

theorem core_centralizes_center_of_short (h : ChapterC.IsShort L) :
    L.pCoreIn 2 ≤ centralizer (coreCenter L : Set G) := by
  rw [coreCenter_eq_of_short h, ← blockU_map]
  rintro _ ⟨x, hx, rfl⟩
  apply mem_centralizer_iff.mpr
  rintro _ ⟨u, hu, rfl⟩
  exact congrArg Subtype.val (mem_centralizer_iff.mp (h.core_centralizes_blockU hx) u hu)

variable {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]

/-- Multiplicative notation for the same linear representation. -/
noncomputable def multiplicativeAction (ρ : Representation (ZMod 2) A V) :
    A →* MulAut (Multiplicative V) where
  toFun a := (LinearEquiv.ofBijective (ρ a) (ρ.apply_bijective a)).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro v
    change Multiplicative.ofAdd (ρ 1 v.toAdd) = v
    simp
  map_mul' a b := by
    apply MulEquiv.ext
    intro v
    change Multiplicative.ofAdd (ρ (a*b) v.toAdd) =
      Multiplicative.ofAdd (ρ a (ρ b v.toAdd))
    rw [map_mul, Module.End.mul_apply]

/-- An actual natural block module supplies the center model required by the
central-cover bridge; the whole-center centrality condition is proved from C.1.7. -/
noncomputable def centerModel (h : ChapterC.IsShort L)
    (ρ : Representation (ZMod 2) A V)
    (m : ChapterC.BlockModuleModel L (multiplicativeAction ρ)) : CenterModel L ρ where
  quotientIso := m.quotientIso
  moduleIso := (blockCenterQuotientEquiv h).symm.trans m.moduleIso
  intertwining := by
    intro l z
    obtain ⟨u, rfl⟩ := (blockCenterEquiv h).surjective z
    rw [← blockCenterEquiv_conjugate]
    change m.moduleIso ((blockCenterQuotientEquiv h).symm
      (QuotientGroup.mk' (centerKernel L) (blockCenterEquiv h (ChapterC.blockConjugate L l u)))) = _
    rw [← blockCenterQuotientEquiv_mk, MulEquiv.symm_apply_apply]
    change m.moduleIso _ = Multiplicative.ofAdd (ρ _ (Multiplicative.toAdd
      (m.moduleIso ((blockCenterQuotientEquiv h).symm
        (QuotientGroup.mk' (centerKernel L) (blockCenterEquiv h u))))))
    rw [← blockCenterQuotientEquiv_mk, MulEquiv.symm_apply_apply]
    exact m.intertwining l u
  core_centralizes := core_centralizes_center_of_short h

/-- The center construction uses precisely the original block quotient marking. -/
@[simp] theorem centerModel_actorMap (h : ChapterC.IsShort L)
    (ρ : Representation (ZMod 2) A V)
    (m : ChapterC.BlockModuleModel L (multiplicativeAction ρ)) :
    (centerModel h ρ m).actorMap =
      m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)) := rfl

/-- The source O^{3′} marking commutes with the same actor map. No replacement
of the source parabolic by an unrelated model subgroup occurs. -/
theorem marking_image [Finite G] {ρ : Representation (ZMod 2) A V}
    (m : CenterModel L ρ) (P Y : Subgroup L)
    (hY : Y = (primeToResidual 3 P).map P.subtype) :
    Y.map m.actorMap =
      (primeToResidual 3 (P.map m.actorMap)).map (P.map m.actorMap).subtype := by
  rw [hY, map_embedded_primeToResidual_of_hom]

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover.BlockModels
