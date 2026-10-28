module

public import Theory.Representation.BinaryPermutation.SixCoreCentralKernel
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.BlockContainment

/-!
# The short-block branch of the solvable centralizer product

The actual core marking and short-block centralizer identity identify
L/O₂(L) with A₆. The quotient L/V is a perfect central two-cover of A₆.
For a ∈ C_T(V), the block displacement bound gives an automorphism cocycle
on L/V. The six-letter core calculation makes that cocycle vanish on
O₂(L)/V, proving that C_T(V) centralizes all of O₂(L), even when O₂(L)>V.

If J(R₁) centralizes V_H and V≤J(R₁), then V_H≤C_T(V), so O₂(L)
centralizes V_H. BlockContainment supplies [V,L₁]≤V_H; the action
contradiction then proves Thompson noncentrality. In the two-core
kernel branch this selects the S₃ factor and its moved plane. The final
theorem connects it to the actual H/O₂(H)≅S₃×S₃, H∩M=L₁T and H=L₁IT,
where H=C_G(z), M=N_G(L), and L₁ is the original O^{3′}(C_L(z)).

The earlier Chapter12/13.3 and 13.4.2 inputs remain explicit; their final
discharge belongs to qt-d-1341-fixed-core-source. The larger action-kernel
case, R₁ placement and normalization, IT uniqueness, marked C₃ chamber
and ambient fusion assembly remain with qt-d-1341-solvable-source.
This module proves the short-block branch, not full source 13.4.8–9.

Source: Aschbacher–Smith C.1.13(d), printed p.125, and 13.4.8, pp.904–905.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory
open Chapter12.Section02 Stellmacher Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
/-- The short-block centralizer identity removes the central quotient from the marked action. -/
theorem centralCore_eq_twoCore_of_short_core_marking
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L) :
    centralCore L = pCore 2 L := by
  apply le_antisymm
  · intro l hl
    rw [← hb.centralizer_blockU]
    intro w hw
    have hwV : (w : G) ∈ V := chosen_eq_block_layer D hb ▸ mem_map_of_mem L.subtype hw
    have hh := m.equivariant l ⟨w,hwV⟩
    have hlq : QuotientGroup.mk' (centralCore L) l = 1 :=
      (QuotientGroup.eq_one_iff l).mpr hl
    rw [hlq,map_one] at hh
    have he : V.normalizerMonoidHom ⟨l,D.normalizes l.property⟩ ⟨w,hwV⟩ = ⟨w,hwV⟩ :=
      m.coordinate.injective (Multiplicative.toAdd.injective hh)
    have he' := congrArg Subtype.val he
    change (l : G) * (w : G) * (l : G)⁻¹ = w at he'
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp he').symm
  · intro l hl
    change QuotientGroup.mk' (pCore 2 L) l ∈ center (L ⧸ pCore 2 L)
    have he : QuotientGroup.mk' (pCore 2 L) l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
    rw [he]
    exact one_mem _

omit [Finite G] in
/-- A short block with the literal core marking belongs to the ordinary A₆ row. -/
theorem ordinary_of_short_core_marking
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq
    (centralCore_eq_twoCore_of_short_core_marking D m hb).symm).trans m.quotient⟩

/-- The five-dimensional case of C.1.13(d), including a two-core larger than V. -/
theorem sylow_module_centralizer_centralizes_componentCore
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) ≤ centralizer (L.pCoreIn 2 : Set G) := by
  have hcore := centralCore_eq_twoCore_of_short_core_marking D m hb
  let N := V.subgroupOf L
  let : N.Normal := normal_subgroupOf_of_le_normalizer D.normalizes
  let f := m.quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L))
  have hf : Function.Surjective f := m.quotient.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ m.quotient.injective,QuotientGroup.ker_mk',hcore]
  have hp : IsPGroup 2 f.ker := by rw [hk]; exact pCore_isPGroup
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    GLS3.Chapter5.SchurPresentation.alternatingGroup_isQuasisimple 1 |>.toIsPerfect
  let : Group.IsPerfect L := hb.twoPerfect.isPerfect_of_surjective_pGroup_kernel f hf hp
  have hN : N = ChapterC.blockU L := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le D.le_component,chosen_eq_block_layer D hb]
  have hNk : N ≤ f.ker := by rw [hk,hN]; exact ChapterC.blockU_le_core
  have hcomm : ⁅f.ker, (⊤ : Subgroup L)⁆ ≤ N := by
    rw [hk,hN]
    exact le_rfl
  let e := (subgroupOfEquivOfLe D.le_component).trans m.coordinate
  have he0 (g : L) (v : N) :
      (e (MulAut.conjNormal g v)).toAdd =
        BinaryPermutation.alternatingCoreRepresentation (Fin 6) (f g) (e v).toAdd := by
    exact m.equivariant g ((subgroupOfEquivOfLe D.le_component) v)
  have he (g : L) (v : BinaryPermutation.core (Fin 6)) :
      (e.symm (Multiplicative.ofAdd
        (BinaryPermutation.alternatingCoreRepresentation (Fin 6) (f g) v)) : L) =
        g * (e.symm (Multiplicative.ofAdd v) : L) * g⁻¹ := by
    have hh := he0 g (e.symm (Multiplicative.ofAdd v))
    rw [e.apply_symm_apply] at hh
    have hsub : e.symm (Multiplicative.ofAdd
        (BinaryPermutation.alternatingCoreRepresentation (Fin 6) (f g) v)) =
        MulAut.conjNormal g (e.symm (Multiplicative.ofAdd v)) := by
      apply e.injective
      apply Multiplicative.toAdd.injective
      simpa only [e.apply_symm_apply,toAdd_ofAdd] using hh.symm
    exact congrArg Subtype.val hsub
  intro a ha
  let α := L.normalizerMonoidHom ⟨a,D.sylow_normalizes_component ha.1⟩
  have hd (g : L) : α g * g⁻¹ ∈ N :=
    sylow_module_centralizer_commutator_le_chosen D hb
      (commutator_mem_commutator ha g.property)
  have hfix (n : L) (hn : n ∈ N) : α n = n := by
    apply Subtype.ext
    change a * (n : G) * a⁻¹ = n
    rw [← ha.2 n hn,mul_inv_cancel_right]
  have hfixed := BinaryPermutation.SixCoreCentralKernel.automorphism_fixes_kernel
    N f hf hp hNk hcomm e he α hd hfix
  rintro x ⟨p,hp,rfl⟩
  have hh := congrArg Subtype.val (hfixed p (hk.symm ▸ hp))
  change a * (p : G) * a⁻¹ = p at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- If the selected Thompson subgroup centralizes V_H, then O₂(L) centralizes V_H. -/
theorem componentCore_centralizes_orbit_of_centralizing_thompson
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (hb : ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (R : Subgroup G) (hVJ : V ≤ elementaryAbelianMaxJ R)
    (hJ : elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z.val : Set G)) :
    L.pCoreIn 2 ≤ centralizer (centralizerOmegaOrbit T z.val : Set G) := by
  let H := centralizer ({z.val} : Set G)
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  have hUT : centralizerOmegaOrbit T z.val ≤ T :=
    (centralizerOmegaOrbit_le_core h₀ hz (fun he => hzL (he ▸ one_mem _))).trans (by
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] using
        pCoreIn_le_sylow H (T.subtype hTH))
  have hUV : centralizerOmegaOrbit T z.val ≤ centralizer (V : Set G) :=
    le_centralizer_iff.mp (hVJ.trans hJ)
  exact le_centralizer_iff.mp ((le_inf hUT hUV).trans
    (sylow_module_centralizer_centralizes_componentCore D m hb))

/-- The short-block alternative forces Thompson noncentrality on the actual V_H. -/
theorem centralizer_thompson_noncentral_of_short_block
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (hb : ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (R : Subgroup G) (hVJ : V ≤ elementaryAbelianMaxJ R)
    (hkernel : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) =
      pCore 2 (centralizer ({z.val} : Set G))) :
    ¬ elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z.val : Set G) := by
  intro hJ
  have hc := componentCore_centralizes_orbit_of_centralizing_thompson h₀ D m hb
    z hz hzL R hVJ hJ
  exact centralizer_thompson_noncentral_of_short_core_bound h₀ D m hb
    (ordinary_of_short_core_marking D m hb)
    z hz hzL hsolv R hVJ hkernel hc hJ

/-- The short-block argument selects one S₃ factor and its actual moved plane. -/
theorem centralizer_single_factor_data_of_short_block
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (hb : ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (R : Subgroup G) (hRT : R ≤ T)
    (hnR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hQR : (centralizer ({z.val} : Set G)).pCoreIn 2 ≤ R)
    (hVJ : V ≤ elementaryAbelianMaxJ R)
    (hkernel : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) =
      pCore 2 (centralizer ({z.val} : Set G)))
    (hAN : firstCentralizerResidual L z.val ≤ normalizer (R : Set G)) :
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z.val} : Set G))
    Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) ∧
      Representation.BinaryOffender.rank (⁅centralizerOmegaOrbit T z.val,I⁆ : Subgroup G) = 2 := by
  have hJ := centralizer_thompson_noncentral_of_short_block h₀ D m hb
    z hz hzL hsolv R hVJ hkernel
  obtain ⟨eo⟩ := ordinary_of_short_core_marking D m hb
  have hcore : IsPGroup 2 (centralCore L) := by
    rw [centralCore_eq_twoCore_of_ordinary eo]
    exact pCore_isPGroup
  obtain ⟨ho,hthree⟩ := firstCentralizerResidual_order_of_core_marking D m hcore z hzL
  exact centralizer_thompson_single_factor_data_of_firstResidual h₀ hz
    (fun he => hzL (he ▸ one_mem _)) R hRT hnR hQR hJ hsolv hkernel ho hthree hAN

open scoped Pointwise
universe u

/-- The short-block branch gives the literal pair quotient, intersection and set product. -/
theorem centralizer_pair_quotient_of_short_block
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (R : Subgroup G) (hRT : R ≤ T)
    (hnR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hQR : (centralizer ({z.val} : Set G)).pCoreIn 2 ≤ R)
    (hVJ : V ≤ elementaryAbelianMaxJ R)
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hkernel : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) =
      pCore 2 (centralizer ({z.val} : Set G)))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hAN : firstCentralizerResidual L z.val ≤ normalizer (R : Set G))
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ Nat.card (Y ⧸ pCore 2 Y) = 3)
    (h1342 : (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
    Nonempty ((H ⧸ pCore 2 H) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) ∧
      Representation.BinaryOffender.rank (⁅centralizerOmegaOrbit T z.val,I⁆ : Subgroup G) = 2 ∧
      H = firstCentralizerResidual L z.val ⊔ I ⊔ (T : Subgroup G) ∧
      H ⊓ normalizer (L : Set G) = firstCentralizerResidual L z.val ⊔ (T : Subgroup G) ∧
      (H : Set G) = (firstCentralizerResidual L z.val : Set G) * (I : Set G) * (T : Set G) := by
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  have hJ := centralizer_thompson_noncentral_of_short_block h₀ D m hb
    z hz hzL hsolv R hVJ hkernel
  obtain ⟨eo⟩ := ordinary_of_short_core_marking D m hb
  have hcore : IsPGroup 2 (centralCore L) := by
    rw [centralCore_eq_twoCore_of_ordinary eo]
    exact pCore_isPGroup
  obtain ⟨ho,hthree⟩ := firstCentralizerResidual_order_of_core_marking D m hcore z hzL
  have hm := centralizer_thompson_single_factor_of_twoCore_kernel h₀ hz hz1 R hRT hnR hQR hJ
    hsolv hkernel (firstCentralizerResidual L z.val)
    ((firstCentralizerResidual_le L z.val).trans inf_le_right)
    (firstCentralizerResidual_twoPerfect L z.val) ho hAN
    (firstCentralizerResidual_noncentral_of_twoCore_kernel hkernel hthree)
  have hprod := centralizer_thompson_normalizer_product h₀ h structural hz hzL R hRT hQR hJ
    hsolv hindex hm
  obtain ⟨hq,hr⟩ := centralizer_thompson_single_factor_data_of_firstResidual h₀ hz hz1
    R hRT hnR hQR hJ hsolv hkernel ho hthree hAN
  have hi := centralizer_thompson_normalizer_index h structural hz R hRT hq hprod hout
  have hres := firstCentralizerResidual_eq_intersection_residual z.val h1342
  let H := centralizer ({z.val} : Set G)
  let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
  let A := firstCentralizerResidual L z.val
  obtain ⟨hpi,hgen⟩ := centralizer_firstResidual_product_of_normalizer_product
    h structural hz I hprod hi h1339 hres
  have hinter := centralizer_intersection_product_of_twoThree h structural hz hpi hres
  refine ⟨centralizer_pair_quotient_of_source_product D m hcore z hzL hz R hRT
    hq hgen hinter hout,hq,hr,hgen,hinter,?_⟩
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  have hAH : A ≤ H := (firstCentralizerResidual_le L z.val).trans inf_le_right
  have hnA : (T : Subgroup G) ≤ normalizer (A : Set G) := by
    rw [show A = firstCentralizerResidual L z.val from rfl,firstCentralizerResidual_eq]
    have hn : (T : Subgroup G) ≤ normalizer
        ((L ⊓ H : Subgroup G) : Set G) :=
      (le_inf D.sylow_normalizes_component (hTH.trans H.le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
    exact hn.trans (normalizer_le_normalizer_characteristic_image _ (primeToResidual 3 _))
  have hnI : H ≤ normalizer (I : Set G) := le_normalizer_conjugateSpanBy _ _
  have hnAI : (T : Subgroup G) ≤ normalizer ((A ⊔ I : Subgroup G) : Set G) :=
    (le_inf hnA (hTH.trans hnI)).trans (normalizer_inf_normalizer_le_normalizer_sup A I)
  calc
    (H : Set G) = ((A ⊔ I ⊔ (T : Subgroup G) : Subgroup G) : Set G) :=
      congrArg (fun B : Subgroup G => (B : Set G)) hgen
    _ = ((A ⊔ I : Subgroup G) : Set G) * (T : Set G) :=
      coe_mul_of_right_le_normalizer_left _ _ hnAI
    _ = (A : Set G) * (I : Set G) * (T : Set G) := by
      rw [coe_mul_of_left_le_normalizer_right A I (hAH.trans hnI)]

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
