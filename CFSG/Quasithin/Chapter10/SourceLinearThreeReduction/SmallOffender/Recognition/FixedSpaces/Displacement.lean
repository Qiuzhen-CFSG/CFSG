module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.ActionKernel
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.FixedSpace

/-!
# Nonzero displacement supplies a supplement to the opposite moved factor

If [A,C_W(b)] is nonzero, point control puts V in Mˣ. An offender element
exchanging the two moved factors gives V=[A,W]Wᵗ. The normalizing element
b fixes [A,W] and therefore V/Wᵗ; the proved stabilizer-kernel transfer
makes b centralize W. Consequently V=[A,C_W(b)]Wᵗ, with literal original
subgroups. The component kernel and outside intersection remain explicit.
Source: Aschbacher--Smith 10.2.12, printed p.754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem nontrivial_displacement_supplement
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (c : Context D) (inputs : ActionInputs D) {g : G}
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hinter : ⁅D.fullModule,L⁆ ⊓
      (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⊥)
    {b : G}
    (hb : b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal ⊓
      normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hbn : b ∉ centralizer (L.map (MulAut.conj g).toMonoidHom : Set G))
    (hQ : ⁅(⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal,
      ⁅D.fullModule,L⁆ ⊓ centralizer ({b} : Set G)⁆ ≠ ⊥) :
    b ∈ centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) ∧
    D.fullModule = ⁅(⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal,
      ⁅D.fullModule,L⁆ ⊓ centralizer ({b} : Set G)⁆ ⊔
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom := by
  have hn := c.nonnormal
  have hcross := c.crossed t ht htn
  have hcent := c.pointCentralizers
  let V := D.fullModule
  let W := ⁅D.fullModule,L⁆
  let U := W.map (MulAut.conj t).toMonoidHom
  let P := W.map (MulAut.conj g).toMonoidHom
  let A := P ⊓ D.maximalLocal
  let Vg := V.map (MulAut.conj g).toMonoidHom
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  let := D.fullModule_elementary hu
  let : IsElementaryAbelian 2 Vg := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 P := by
    let := source_full_moved_elementary D
    exact IsElementaryAbelian.map _
  have hWV : W ≤ V := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  have hPV : P ≤ Vg := map_mono hWV
  have hAV : A ≤ normalizer (V : Set G) :=
    inf_le_right.trans D.maximalLocal_normalizes_fullModule
  have hgen := source_nonnormal_fullModule_eq_moved_pair D hn ht hcross
  have hUV : U ≤ V := le_sup_right.trans_eq hgen.symm
  obtain ⟨a,ha,han⟩ : ∃ a ∈ A, a ∉ normalizer (W : Set G) := by
    by_contra! hAN
    have hfix := normalizer_fixed_space c hinter hb.1.1 hbn
    change W ⊓ centralizer ({b} : Set G) ≤
      centralizer ((A ⊓ normalizer (W : Set G) : Subgroup G) : Set G) at hfix
    rw [inf_of_le_left (show A ≤ normalizer (W : Set G) from hAN)] at hfix
    exact hQ (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hfix))
  have hVa : V = ⁅A,W⁆ ⊔ U :=
    source_nonnormal_moved_swap_generation D hn ht htn hcross inf_le_right ha han
  have hVmg : V ≤ D.maximalLocal.map (MulAut.conj g).toMonoidHom :=
    source_nonnormal_nontrivial_displacement_module_le_conjugate D hn ht htn
      hcross hcent hb.1.1 hbn hQ
  have hVN : V ≤ normalizer (Vg : Set G) := hVmg.trans
    ((map_mono D.maximalLocal_normalizes_fullModule).trans
      (V.le_normalizer_map (MulAut.conj g).toMonoidHom))
  have hCVg : ⁅A,W⁆ ≤ Vg :=
    (commutator_mono (inf_le_left.trans hPV) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hWV.trans hVN))
  have hbC : b ∈ centralizer (↑(⁅A,W⁆ : Subgroup G) : Set G) :=
    (centralizer_le hCVg) (Vg.le_centralizer (hPV hb.1.1))
  have hWa : W.map (MulAut.conj a).toMonoidHom = U := by
    have hmap (m : G) (hm : m ∈ D.maximalLocal) :
        V.map (MulAut.conj m).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hm)
    have hnot : L.map (MulAut.conj a).toMonoidHom ≠ L := by
      intro he
      apply han
      apply mem_normalizer_iff_map_conj_eq.mpr
      change (⁅V,L⁆).map (MulAut.conj a).toMonoidHom = ⁅V,L⁆
      rw [map_commutator,hmap a ha.2,he]
    have he := (source_nonnormal_maximal_pair D hn ht htn a ha.2).resolve_left hnot
    change (⁅V,L⁆).map (MulAut.conj a).toMonoidHom =
      (⁅V,L⁆).map (MulAut.conj t).toMonoidHom
    rw [map_commutator,hmap a ha.2,he,map_commutator,
      hmap t (le_normalizer_componentOrbit L T ht)]
  have hab : (MulAut.conj a) b = b := by
    have hc := P.le_centralizer ha.1 b hb.1.1
    change a * b * a⁻¹ = b
    rw [← hc, mul_assoc]
    simp only [mul_inv_cancel, mul_one]
  have hbU : b ∈ normalizer (U : Set G) := by
    have hh := W.le_normalizer_map (MulAut.conj a).toMonoidHom
      (mem_map_of_mem (MulAut.conj a).toMonoidHom hb.2)
    simpa only [hWa,MulEquiv.coe_toMonoidHom,hab] using hh
  have hcomm : ⁅zpowers b,V⁆ ≤ U := by
    have hCU : ⁅⁅A,W⁆,zpowers b⁆ ≤ U := by
      rw [commutator_comm,commutator_eq_bot_iff_le_centralizer.mpr (zpowers_le.mpr hbC)]
      exact bot_le
    have hUU : ⁅U,zpowers b⁆ ≤ U :=
      le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hbU)
    have hVU : V ≤ normalizer (U : Set G) :=
      (V.le_centralizer.trans (centralizer_le hUV)).trans (centralizer_le_normalizer U)
    rw [commutator_comm,hVa]
    exact commutator_sup_le_of_relative_normal V ⁅A,W⁆ U (zpowers b) U
      hVU ((commutator_mono le_rfl hWV).trans
        (le_normalizer_iff_commutator_le_right.mp hAV)) hUV hCU hUU
  have hbW := partner_quotient_kernel_element inputs ht htn hcross
    hb.1.2 hb.2 hcomm
  refine ⟨hbW,?_⟩
  have hWC : W ≤ centralizer ({b} : Set G) := by
    intro w hw
    exact mem_centralizer_singleton_iff.mpr (hbW w hw)
  change V = ⁅A,W ⊓ centralizer ({b} : Set G)⁆ ⊔ U
  rw [inf_of_le_left hWC]
  exact hVa

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
