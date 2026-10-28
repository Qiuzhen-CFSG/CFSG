module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingOddInvolutionSource
public import Theory.ElementaryAbelian.Injective
/-!
# The original central factor for the marked A5 extension

The centralizer of the selected block lies in the two-core of H and hence
in its Sylow subgroup. The C.1.13 module-centralizer splitting and the
original core and C.6 source identities make it an elementary central
direct factor complementary to the natural module in O2(H).

Source: Aschbacher–Smith 2.4.27(3) and 2.4.29, printed pp.544–545.
-/
public section
open Subgroup Stellmacher BinaryPermutation
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_centralizer_factor
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    let U := (blockU d.block).map d.block.subtype
    let D := centralizer (d.block : Set d.H)
    Disjoint U D ∧ D ≤ center d.H ∧ IsElementaryAbelian 2 D ∧
      pCore 2 d.H = U ⊔ D ∧ D ≤ (d.S : Subgroup d.H) := by
  let U := (blockU d.block).map d.block.subtype
  let D := centralizer (d.block : Set d.H)
  let : d.block.Normal := hsingle ▸ d.L0_normal
  have hAi : IsAlternatingBlock d.block 5 := hA.of_mulEquiv
    (d.block.equivMapOfInjective d.H.subtype d.H.subtype_injective).symm
  obtain ⟨q,e,hq,hker,hC,he⟩ := d.single_alternating_marked_action hsingle hA
  have hDK : D ≤ pCore 2 d.H := by
    rw [←hker,hC]
    exact centralizer_le (map_subtype_le _)
  have hDS : D ≤ (d.S : Subgroup d.H) := hDK.trans
    (pCore_isPGroup.le_sylow_of_normal d.S)
  have hDa : D.map d.H.subtype ≤ (T : Subgroup G) ⊓
      centralizer (d.block.map d.H.subtype : Set G) := by
    exact le_inf ((map_mono hDS).trans hST.le)
      (map_centralizer_le_centralizer_image (d.block : Set d.H) d.H.subtype)
  have hDZ := (d.single_alternating_centralizer_source hG T hM hTM hu hST hsingle hA).1
  have hcent : D ≤ center d.H := by
    intro z hz
    apply mem_center_iff.mpr
    intro g
    exact Subtype.ext (hDZ (hDa (mem_map_of_mem d.H.subtype hz)) g g.property)
  have hsplit := hAi.normalizer_twoCore_eq_module_sup_centralizer
    (H:=(⊤ : Subgroup d.H)) le_top (by rw [normalizer_eq_top])
  have htop : (⊤ : Subgroup d.H).pCoreIn 2 = pCore 2 d.H := by
    exact pCore_map_iso 2 (Subgroup.topEquiv : (⊤ : Subgroup d.H) ≃* d.H)
  rw [htop,inf_eq_right.mpr hDK] at hsplit
  let : IsElementaryAbelian 2 (twoCore d.H) := (d.core_source hG T hST).2.2.2.1
  let : IsElementaryAbelian 2 ((pCore 2 d.H).map d.H.subtype) :=
    inferInstanceAs (IsElementaryAbelian 2 (twoCore d.H))
  let j := (pCore 2 d.H).equivMapOfInjective d.H.subtype d.H.subtype_injective
  let : IsElementaryAbelian 2 (pCore 2 d.H) :=
    IsElementaryAbelian.of_injective j.toMonoidHom j.injective
  have hDe : IsElementaryAbelian 2 D :=
    IsElementaryAbelian.of_injective (inclusion hDK) (inclusion_injective hDK)
  exact ⟨alternatingModule_disjoint_of_commuting d.block D hAi le_rfl,
    hcent,hDe,hsplit,hDS⟩
end CFSG.Quasithin.Chapter2
