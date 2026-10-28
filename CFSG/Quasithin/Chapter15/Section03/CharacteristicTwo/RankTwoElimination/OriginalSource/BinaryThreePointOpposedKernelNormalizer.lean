module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointKernelExchange

/-!
# A nontrivial opposed kernel in the literal point quotient

The original exchange obstruction makes q(N^g) nontrivial. This same
subgroup lies in the original image Sylow and is normalized by that Sylow
and by every element of L^g intersect C. In particular, the already
constructed opposed cubic acts on this actual hidden-kernel image.
No placement in the containing simple component is asserted.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
variable {G : Type*} [Group G] [Finite G]

/-- The literal opposite kernel survives and is normalized by the actual
opposed point stabilizer and original full quotient Sylow. -/
theorem binary_three_source_binary_opposed_kernel_normalizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL K n 2)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    let C := centralizer ({z} : Set G)
    let N := C.pCoreIn 2
    let q := QuotientGroup.mk' (pCore 2 C)
    let A := ((N.conjBy g).subgroupOf C).map q
    let Sbar := (P : Subgroup C).map q
    A ≠ ⊥ ∧ A ≤ Sbar ∧ Sbar ≤ normalizer A ∧
      ((c.L.conjBy g).subgroupOf C).map q ≤ normalizer A := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let q := QuotientGroup.mk' (pCore 2 C)
  let Ng := N.conjBy g
  let A := (Ng.subgroupOf C).map q
  have hCN : C ≤ normalizer N := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hSN : d.S ≤ normalizer N := (le_sup_right.trans hLS).trans hCN
  have hLN : c.L ≤ normalizer N := (le_sup_left.trans hLS).trans hCN
  have hNS : N ≤ d.S := hP ▸ pCoreIn_le_sylow C P
  have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
  have hTS : (d.T : Subgroup G) ≤ normalizer d.S :=
    (normal_subgroupOf_iff_le_normalizer (show d.S ≤ (d.T : Subgroup G) from inf_le_left)).mp
      (normal_of_index_eq_two hi)
  have hSg : d.S.map (MulAut.conj g).toMonoidHom = d.S :=
    mem_normalizer_iff_map_conj_eq.mp (hTS hgT)
  have hNgS : Ng ≤ d.S := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hNS
    rwa [hSg] at hh
  have hSNg : d.S ≤ normalizer Ng := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hSN
    rwa [hSg,map_equiv_normalizer_eq] at hh
  have hLgNg : c.L.conjBy g ≤ normalizer Ng := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hLN
    rwa [map_equiv_normalizer_eq] at hh
  have hPC : (P : Subgroup C) = d.S.subgroupOf C := by
    rw [←hP]
    exact (comap_map_eq_self_of_injective C.subtype_injective (P : Subgroup C)).symm
  have hNP : Ng.subgroupOf C ≤ (P : Subgroup C) := by rw [hPC]; exact comap_mono hNgS
  have hPN : (P : Subgroup C) ≤ normalizer (Ng.subgroupOf C) := by
    intro x hx y
    change ((y : G) ∈ Ng) ↔ ((x : G) * (y : G) * (x : G)⁻¹ ∈ Ng)
    exact mem_normalizer_iff.mp (hSNg (hP ▸ mem_map_of_mem C.subtype hx)) y
  have hLcN : (c.L.conjBy g).subgroupOf C ≤ normalizer (Ng.subgroupOf C) := by
    intro x hx y
    change ((y : G) ∈ Ng) ↔ ((x : G) * (y : G) * (x : G)⁻¹ ∈ Ng)
    exact mem_normalizer_iff.mp (hLgNg hx) y
  have hNgC : Ng ≤ C := hNgS.trans (le_sup_right.trans hLS)
  have hnon : A ≠ ⊥ := by
    intro hz
    have hle : Ng ≤ N := by
      have hk : Ng.subgroupOf C ≤ pCore 2 C := by
        change (Ng.subgroupOf C).map q = ⊥ at hz
        rw [Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at hz
        exact hz
      intro x hx
      exact mem_map_of_mem C.subtype (hk (show (⟨x,hNgC hx⟩ : C) ∈ Ng.subgroupOf C from hx))
    have he := (binary_three_source_binary_kernel_exchange
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hn hm
        g hgT hgS).2.2.2.2.2
    exact he ((map_mono (f := (MulAut.conj g).toMonoidHom) inf_le_right).trans hle)
  exact ⟨hnon,map_mono hNP,(map_mono hPN).trans (le_normalizer_map q),
    (map_mono hLcN).trans (le_normalizer_map q)⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
