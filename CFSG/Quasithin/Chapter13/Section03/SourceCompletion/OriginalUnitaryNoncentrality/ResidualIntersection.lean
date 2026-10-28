module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.ResidualControl

/-!
# The unitary conjugate-residual intersection

The literal two-residuals of Y intersect Yᵍ and Y intersect M agree.
The latter is L-invariant, while the former is Y-invariant. The unitary
normalizer control then forces their vanishing. A separate lemma records
mutual normalization inside the original plane centralizer.

Source: Aschbacher--Smith 13.3.14(b), printed p.891.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
variable {G : Type*} [Group G] [Finite G] {V : Subgroup G} [IsElementaryAbelian 2 V]

omit [Finite G] [IsElementaryAbelian 2 V] in
private theorem fixed_residual_normalized
    (T : Sylow 2 G) (L Y : Subgroup G)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hLN : L ≤ normalizer (V : Set G))
    (hfaith : L ⊓ centralizer (V : Set G) ≤ L.pCoreIn 2)
    (hY : IsPPerfect 2 Y) (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hYM : Y ≤ normalizer (L : Set G)) (hYC : Y ≤ centralizer (V : Set G)) :
    L ≤ normalizer (Y : Set G) := by
  have hLC : L ≤ normalizer (centralizer (V : Set G) : Set G) :=
    hLN.trans ((normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer _)).mp inferInstance)
  have hcomm : ⁅L,Y⁆ ≤ L.pCoreIn 2 :=
    (le_inf (le_normalizer_iff_commutator_le_left.mp hYM)
      ((commutator_mono le_rfl hYC).trans
        (le_normalizer_iff_commutator_le_right.mp hLC))).trans hfaith
  have hQT : L.pCoreIn 2 ≤ (T : Subgroup G) := by
    apply (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer hTL)).trans
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  exact Noncentrality.normalizes_of_commutator_le_twoGroup L Y (L.pCoreIn 2) hY
    (isPGroup_pCoreIn 2 L) (hQT.trans hTY)
    (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))) hcomm

omit [Finite G] in
/-- The original residual and its plane-normalizing conjugate normalize each other. -/
theorem unitary_residual_conjugate_local_data
    (Z B U H : Subgroup G) (hZB : Z ≤ B) (hBU : B ≤ U)
    (hH : H = normalizer (Z : Set G)) (g : G)
    (hgB : g ∈ normalizer (B : Set G)) :
    let Y := Noncentrality.centralizingResidual (conjugateSpanBy U H)
    let Yg := Y.map (MulAut.conj g).toMonoidHom
    Y ⊔ Yg ≤ centralizer (B : Set G) ∧
      Y ≤ normalizer (Yg : Set G) ∧ Yg ≤ normalizer (Y : Set G) := by
  let Y := Noncentrality.centralizingResidual (conjugateSpanBy U H)
  let c := (MulAut.conj g).toMonoidHom
  let Yg := Y.map c
  have hYB : Y ≤ centralizer (B : Set G) :=
    (Noncentrality.centralizingResidual_le_seed_centralizer U H).trans (centralizer_le hBU)
  have hCBH : centralizer (B : Set G) ≤ H := by
    rw [hH]
    exact (centralizer_le hZB).trans (Subgroup.centralizer_le_normalizer _)
  have hHY := Noncentrality.normalizes_centralizingResidual U H
  have hn : g ∈ normalizer (centralizer (B : Set G) : Set G) :=
    ((normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer (B : Set G))).mp
      inferInstance) hgB
  have hYgB : Yg ≤ centralizer (B : Set G) :=
    (map_mono (f := c) hYB).trans_eq ((mem_normalizer_iff_map_conj_eq).mp hn)
  have hYgN : Yg ≤ normalizer (Y : Set G) := hYgB.trans (hCBH.trans hHY)
  have hYNg : Y ≤ normalizer (Yg : Set G) := by
    have hc : centralizer (B : Set G) ≤ H.map c := by
      rw [← (mem_normalizer_iff_map_conj_eq).mp hn]
      exact map_mono hCBH
    exact (hYB.trans hc).trans ((map_mono (f := c) hHY).trans (le_normalizer_map c))
  exact ⟨sup_le hYB hYgB,hYNg,hYgN⟩

/-- The two-residual intersection vanishes, with the actual unitary centralizer
bound replacing the ordinary branch's equality of the joined module with V. -/
theorem unitary_residual_intersection_isTwoGroup
    (T : Sylow 2 G) (L Z B U H : Subgroup G)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (rho : Automizer V →* Atlas.G2.Model F) (E : Additive V ≃ₗ[F] W)
    (he : ∀ a v, E (automizerRepresentation V a v) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hs : pointCoordinateSubspace E U = seed) (hUV : U ≤ V)
    (hZB : Z ≤ B) (hBU : B ≤ U) (hZT : Z ≤ (T : Subgroup G)) (hZn : Z ≠ ⊥)
    (hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hLN : L ≤ normalizer (V : Set G))
    (hfaith : L ⊓ centralizer (V : Set G) ≤ L.pCoreIn 2)
    (hTI : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨ V.map (MulAut.conj g).toMonoidHom = V)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N →
      N = normalizer (L : Set G))
    (hH : H = normalizer (Z : Set G)) (hescape : ¬ H ≤ normalizer (L : Set G))
    (g : L) (hgB : g.val ∈ normalizer (B : Set G))
    (hjoin : centralizer ((U ⊔ U.map (MulAut.conj g.val).toMonoidHom : Subgroup G) : Set G) ≤
      normalizer (L : Set G)) :
    let Y := Noncentrality.centralizingResidual (conjugateSpanBy U H)
    IsPGroup 2 (Y ⊓ Y.map (MulAut.conj g.val).toMonoidHom : Subgroup G) := by
  let M := normalizer (L : Set G)
  let Y := Noncentrality.centralizingResidual (conjugateSpanBy U H)
  let c := (MulAut.conj g.val).toMonoidHom
  let Yg := Y.map c
  let A := Y ⊓ Yg
  let YM := (pResidual 2 (Y ⊓ M : Subgroup G)).map (Y ⊓ M : Subgroup G).subtype
  let Y1 := (pResidual 2 A).map A.subtype
  have hYC : Y ≤ centralizer (U : Set G) := Noncentrality.centralizingResidual_le_seed_centralizer U H
  have hHY : H ≤ normalizer (Y : Set G) := Noncentrality.normalizes_centralizingResidual U H
  have hTH : (T : Subgroup G) ≤ H := hH ▸ hTZ
  obtain ⟨_,hYNg,hYgN⟩ := unitary_residual_conjugate_local_data Z B U H hZB hBU hH g.val hgB
  have hYN1 : Y ≤ normalizer (Y1 : Set G) :=
    ((le_inf Y.le_normalizer hYNg).trans inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image A (pResidual 2 A))
  have hAg : A ≤ centralizer (U.map c : Set G) :=
    inf_le_right.trans ((map_mono (f := c) hYC).trans (map_centralizer_le_centralizer_image _ c))
  have hAM : A ≤ M := by
    apply le_trans _ hjoin
    exact le_centralizer_iff.mp (sup_le
      (le_centralizer_iff.mpr (inf_le_left.trans hYC)) (le_centralizer_iff.mpr hAg))
  have h1M : Y1 ≤ YM := embedded_pResidual_mono 2 (le_inf inf_le_left hAM)
  have hMY : YM ≤ Y := (map_subtype_le _).trans inf_le_left
  have hMM : YM ≤ M := (map_subtype_le _).trans inf_le_right
  have hTM : (T : Subgroup G) ≤ normalizer (M : Set G) :=
    hTL.trans M.le_normalizer
  have hTYM : (T : Subgroup G) ≤ normalizer (YM : Set G) :=
    ((le_inf (hTH.trans hHY) hTM).trans inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image (Y ⊓ M) (pResidual 2 (Y ⊓ M : Subgroup G)))
  have hUn : U ≠ ⊥ := fun hz => hZn (le_bot_iff.mp ((hZB.trans hBU).trans_eq hz))
  have hLYM : L ≤ normalizer (YM : Set G) :=
    fixed_residual_normalized T L YM hTL hLN hfaith (isPPerfect_embedded_pResidual 2 _)
      hTYM hMM (unitary_twoPerfect_seed_centralizer L U YM rho E he hs hUV hUn
        (isPPerfect_embedded_pResidual 2 _) hMM (hMY.trans hYC) hTI)
  have hMYg : YM ≤ Yg := by
    rw [← (mem_normalizer_iff_map_conj_eq).mp (hLYM g.property)]
    exact map_mono hMY
  have hM1 : YM ≤ Y1 := by
    have hh := embedded_pResidual_mono 2 (le_inf hMY hMYg)
    rw [(pResidual_eq_top_iff 2 YM).mpr (isPPerfect_embedded_pResidual 2 _),
      ← MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have h1bot : Y1 = ⊥ := by
    by_contra hne
    have heq : Y1 = YM := le_antisymm h1M hM1
    have hn := unitary_twoPerfect_seed_normalizer_control T L U Z Y1 hG rho E he hs hUV
      (hZB.trans hBU) hZT hZn hTZ hTL hLN hfaith (isPPerfect_embedded_pResidual 2 _)
      hne (heq.symm ▸ hTYM) (h1M.trans hMM)
      (((map_subtype_le _).trans inf_le_left).trans hYC) hTI hu
    have hYM := hYN1.trans hn
    have hYne : Y ≠ ⊥ := by
      intro hy
      exact hne (le_bot_iff.mp (((map_subtype_le _).trans inf_le_left).trans_eq hy))
    exact hescape (hHY.trans (unitary_twoPerfect_seed_normalizer_control T L U Z Y hG rho E he
      hs hUV (hZB.trans hBU) hZT hZn hTZ hTL hLN hfaith
      (Noncentrality.centralizingResidual_isPPerfect _) hYne (hTH.trans hHY) hYM hYC hTI hu))
  have hp : pResidual 2 A = ⊥ := by
    apply (map_injective A.subtype_injective)
    simpa only [Subgroup.map_bot] using h1bot
  exact (isPGroup_quotient_pResidual (G := A) 2).of_equiv
    ((QuotientGroup.quotientMulEquivOfEq hp).trans
      (QuotientGroup.quotientBot : (A ⧸ (⊥ : Subgroup A)) ≃* A))
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
