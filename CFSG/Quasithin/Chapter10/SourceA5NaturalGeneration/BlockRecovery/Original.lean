module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.MovedSectionModel
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.Representation.SL2.BinarySmallModels
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.BlockRecovery.Center
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking
/-!
# Recovering the original natural block without changing its module

The full original module is contained in T and normalized by L₀T. Within
that local ambient, the nonzero module commutator of a block is its actual
U-layer. Mapping this equality back to G identifies U(L) with [V,L]. The
root's chosen natural section therefore gives the intrinsic L₂(4) marking
with its literal quotient map. The original fixed-center calculation then
removes the central module kernel, gives a 16-element U-layer, and proves
the actual two-core elementary. Its equality with U is not assumed here.

Source: Aschbacher–Smith C.1.27, p.133, and 10.2.3(4), pp.746–747.
-/
public section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10
noncomputable section
variable {G : Type*} [Group G]
variable {F : Type} [Field F] [Finite F] [CharP F 2]
local instance recoveryBinaryAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- Recover the intrinsic natural block marking from the actual moved section. -/
theorem source_natural_block_of_identified_moved_section
    (K U : Subgroup G) (hK : ChapterC.IsShort K)
    (hmoved : (ChapterC.blockU K).map K.subtype = ⁅U,K⁆)
    (e : (K ⧸ pCore 2 K) ≃* SL(2,F)) (hF : Nat.card F = 4)
    (c : BinaryConjugationSection K ⁅U,K⁆ (⁅U,K⁆ ⊓ centralizer (K : Set G))
      (SL2.BinarySmall.natural.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))))) :
    ChapterC.IsL2EvenBlock K 2 := by
  let ρ := SL2.BinarySmall.natural (K := F)
  let r : SL(2,F) →* MulAut (Multiplicative (Fin 2 → F)) := {
    toFun := fun g => (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)).toAddEquiv.toMultiplicative
    map_one' := by apply MulEquiv.ext; intro w; exact congrArg Multiplicative.ofAdd (LinearMap.congr_fun ρ.map_one w.toAdd)
    map_mul' := fun g k => by apply MulEquiv.ext; intro w; exact congrArg Multiplicative.ofAdd (LinearMap.congr_fun (ρ.map_mul g k) w.toAdd) }
  let m := ChapterC.blockModelOfIdentifiedMovedSection K U hmoved e ρ r (fun _ _ => rfl) c
  refine ⟨by decide,hK,F,inferInstance,inferInstance,by simpa using hF,
    ⟨F,inferInstance,inferInstance,by simpa using hF,⟨e.trans (Theory.PSL2.sl2QuotientEquiv F)⟩⟩,
    r,⟨m⟩,fun _ _ => rfl⟩
variable [Finite G]
open Chapter3.Section02 ChapterC
variable {T : Sylow 2 G} {L : Subgroup G}
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

theorem source_original_blockU_eq_full_moved
    (hb : IsBlock (L.subgroupOf (localJoin T L))) :
    (blockU L).map L.subtype = ⁅D.fullModule,L⁆ := by
  have hunique := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  let H := localJoin T L
  let A := L.subgroupOf H
  let U := D.fullModule.subgroupOf H
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  have hUH : D.fullModule ≤ H := (D.fullModule_le_sylow hunique).trans le_sup_right
  have hHM : H ≤ D.maximalLocal := sup_le (localOrbit T L).le_normalizer
    (le_normalizer_componentOrbit L T)
  let : U.Normal := normal_subgroupOf_of_le_normalizer
    (hHM.trans D.maximalLocal_normalizes_fullModule)
  let := D.fullModule_elementary hunique
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hUH).toMonoidHom (subgroupOfEquivOfLe hUH).injective
  have hne : ⁅U,A⁆ ≠ ⊥ := by
    intro he
    have hh := congrArg (map H.subtype) he
    rw [map_commutator,map_subgroupOf_eq_of_le hUH,
      map_subgroupOf_eq_of_le hLH,Subgroup.map_bot] at hh
    exact source_full_moved_ne_bot D hh
  have hh := congrArg (map H.subtype)
    (ChapterC.RankOne.ChiProduct.SelectedRankOne.blockU_eq_nontrivial_normal_module_commutator
      A U hb hne)
  rw [map_commutator,map_subgroupOf_eq_of_le hUH,map_subgroupOf_eq_of_le hLH] at hh
  let e := subgroupOfEquivOfLe hLH
  rw [map_map,show H.subtype.comp A.subtype = L.subtype.comp e.toMonoidHom from rfl,
    ←map_map,RankOne.Solvable.blockU_map_equiv] at hh
  exact hh

/-- The root's original natural coordinates now mark the intrinsic block module. -/
theorem source_original_natural_block
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (hF : Nat.card F = 4)
    (c : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    IsL2EvenBlock L 2 := by
  have hLH : L ≤ localJoin T L := (le_componentOrbit L T).trans le_sup_left
  have hs := RankOne.Solvable.isShort_of_equiv (subgroupOfEquivOfLe hLH) hb.short
  exact source_natural_block_of_identified_moved_section L D.fullModule hs
    (source_original_blockU_eq_full_moved D hb) e hF c

/-- The original central kernel vanishes after the common Sylow fixed center. -/
theorem source_original_moved_fixed_eq_bot
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    (hz : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    sourceMovedFixed D = ⊥ := by
  have hm := source_original_blockU_eq_full_moved D hb
  have hc := source_original_block_center_eq_bot D hn hb hz
  apply bot_unique
  rintro x ⟨hx,hxc⟩
  obtain ⟨u,hu,he⟩ := hm.ge hx
  change (u : G) = x at he
  have huC : u ∈ center L := by
    apply mem_center_iff.mpr
    intro l
    apply Subtype.ext
    change (l:G)*(u:G) = (u:G)*(l:G)
    rw [he]
    exact hxc l l.property
  rw [hc,mem_bot] at huC
  exact mem_bot.mpr (he.symm.trans (congrArg L.subtype huC))

/-- Intrinsic natural type and elementary actual core, with a 16-element moved layer. -/
theorem source_original_natural_block_recovery
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    (hz : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (hF : Nat.card F = 4)
    (c : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    IsL2EvenBlock L 2 ∧ center L = ⊥ ∧ IsElementaryAbelian 2 (pCore 2 L) ∧
      Nat.card (blockU L) = 16 ∧ sourceMovedFixed D = ⊥ := by
  have hm := source_original_natural_block D hb e hF c
  have hc := source_original_block_center_eq_bot D hn hb hz
  have he := source_original_block_core_elementary D hn hb hz
  have hf : blockFixed L = ⊥ := by rw [blockFixed,hc,bot_subgroupOf]
  have hcard := hm.module_card
  let q := (QuotientGroup.quotientMulEquivOfEq hf).trans QuotientGroup.quotientBot
  have hu : Nat.card (blockU L) = 16 := by
    exact (Nat.card_congr q.toEquiv).symm.trans hcard
  exact ⟨hm,hc,he,hu,source_original_moved_fixed_eq_bot D hn hb hz⟩
end
end CFSG.Quasithin.Chapter10
