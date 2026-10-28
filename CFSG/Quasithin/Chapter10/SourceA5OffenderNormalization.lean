module
public import CFSG.Quasithin.Chapter10.SourceA5OffenderFixedGeometry
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.FactorKernel

/-!
# Nontrivial offender displacement supplies the original fixed supplement

If the source displacement is nontrivial, the full module lies in the
conjugate maximal local group. The offender then centralizes its own
displacement on the original moved factor. An element exchanging the two
factors shows that the chosen normalizing element centralizes the quotient
by the opposite factor. The proved original quotient-kernel identity forces
it to centralize the original factor itself. Consequently the displacement
and the opposite factor generate the full module.

This is the exact supplement used by point-centralizer generation in the
proof of 10.2.12. The genuine separate-factor, component-normalizer and
element-centralizer inputs remain explicit.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Proposition 10.2.12, printed p.754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem source_a5_nontrivial_offender_displacement_supplement
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 → centralizer ({u} : Set G) ≤ D.maximalLocal)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {g b : G} (hg : g ∉ D.maximalLocal)
    (hb : b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal ⊓
      normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hbn : b ∉ centralizer (L.map (MulAut.conj g).toMonoidHom : Set G))
    (hQ : ⁅(⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal,
      ⁅D.fullModule,L⁆ ⊓ centralizer ({b} : Set G)⁆ ≠ ⊥) :
    b ∈ centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) ∧
    D.fullModule = ⁅(⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal,
      ⁅D.fullModule,L⁆ ⊓ centralizer ({b} : Set G)⁆ ⊔
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom := by
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
    have hfix := source_a5_offender_fixed_space_of_normalizes D e hn ht htn
      hcross hcent hNL hg hAN hb.1.1 hbn
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
  have hbW := source_a5_original_partner_quotient_kernel_element D e ht htn hcross
    hb.1.2 hb.2 hcomm
  refine ⟨hbW,?_⟩
  have hWC : W ≤ centralizer ({b} : Set G) := by
    intro w hw
    exact mem_centralizer_singleton_iff.mpr (hbW w hw)
  change V = ⁅A,W ⊓ centralizer ({b} : Set G)⁆ ⊔ U
  rw [inf_of_le_left hWC]
  exact hVa

theorem source_nonnormal_normalizes_moved_of_fixed_subgroup
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (X A : Subgroup G) (hXW : X ≤ ⁅D.fullModule,L⁆)
    (hXL : ¬ X ≤ centralizer (L : Set G))
    (hAM : A ≤ D.maximalLocal) (hXA : X ≤ centralizer (A : Set G)) :
    A ≤ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  let W := ⁅D.fullModule,L⁆
  let U := W.map (MulAut.conj t).toMonoidHom
  have hmap (a : G) (ha : a ∈ D.maximalLocal) :
      D.fullModule.map (MulAut.conj a).toMonoidHom = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule ha)
  intro a ha
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (⁅D.fullModule,L⁆).map (MulAut.conj a).toMonoidHom = ⁅D.fullModule,L⁆
  rcases source_nonnormal_maximal_pair D hn ht htn a (hAM ha) with he | he
  · rw [map_commutator,hmap a (hAM ha),he]
  · exfalso
    apply hXL
    have hWU : W.map (MulAut.conj a).toMonoidHom = U := by
      change (⁅D.fullModule,L⁆).map (MulAut.conj a).toMonoidHom =
        (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom
      rw [map_commutator,hmap a (hAM ha),he,map_commutator,
        hmap t (le_normalizer_componentOrbit L T ht)]
    apply le_trans ?_ hcross
    intro x hx
    change x ∈ U
    rw [←hWU]
    refine ⟨x,hXW hx,?_⟩
    change a * x * a⁻¹ = x
    rw [hXA hx a ha,mul_assoc,mul_inv_cancel,mul_one]

end CFSG.Quasithin.Chapter10
