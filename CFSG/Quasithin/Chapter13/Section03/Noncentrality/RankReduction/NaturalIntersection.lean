module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.RankReduction.NaturalMover
/-!
# The conjugate intersection in the natural branch of 13.3.14(b)

The odd residual of Y∩Yᵍ equals that of Y∩M. The natural module kernel
and the original TI and maximal-local uniqueness inputs force its
normalizer into M; nontriviality would then put Y in M, a contradiction.
Thus Y∩Yᵍ is a two-group. The mover is the actual element of L and every
conjugation is on the original ambient subgroups.
Source: Aschbacher–Smith, 13.3.14(b), printed p.891.
-/
@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
include d
private theorem natural_normalizes_fixed_actor [Group.IsPerfect L]
    (Y : Subgroup G) (hY : IsPPerfect 2 Y)
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hYC : Y ≤ centralizer (V : Set G))
    (hNVL : normalizer (V : Set G) ≤ normalizer (L : Set G)) :
    L ≤ normalizer (Y : Set G) := by
  have hLV := (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left).trans d.normalizes_V
  have hcomm := perfect_core_commutator L V hLV hNVL (natural_kernel_commutator d)
  have hQT : L.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hn : L ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) :=
      sup_le L.le_normalizer d.normalizes_L
    apply (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) hn).trans
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  exact normalizes_of_commutator_le_twoGroup L Y (L.pCoreIn 2) hY
    (isPGroup_pCoreIn 2 L) (hQT.trans hTY)
    (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
    ((commutator_mono le_rfl hYC).trans hcomm)

/-- The original residual and its moving plane conjugate intersect in a two-group. -/
theorem natural_residual_intersection_isTwoGroup [Group.IsPerfect L]
    (hTI : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨ V.map (MulAut.conj g).toMonoidHom = V)
    (hNVL : normalizer (V : Set G) ≤ normalizer (L : Set G))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N = M)
    (hescape : ¬ H ≤ M)
    (g : L) (hgE : g.val ∈ normalizer (E : Set G))
    (hjoin : U ⊔ U.map (MulAut.conj g.val).toMonoidHom = V) :
    let Y := centralizingResidual (conjugateSpanBy U H)
    IsPGroup 2 (Y ⊓ Y.map (MulAut.conj g.val).toMonoidHom : Subgroup G) := by
  let Y := centralizingResidual (conjugateSpanBy U H)
  let c := (MulAut.conj g.val).toMonoidHom
  let Yg := Y.map c
  let A := Y ⊓ Yg
  let YM := (pResidual 2 (Y ⊓ M : Subgroup G)).map (Y ⊓ M : Subgroup G).subtype
  let Y1 := (pResidual 2 A).map A.subtype
  have hYC : Y ≤ centralizer (U : Set G) := centralizingResidual_le_seed_centralizer U H
  have hYE : Y ≤ centralizer (E : Set G) := hYC.trans (centralizer_le d.plane_le_seed)
  have hCEH : centralizer (E : Set G) ≤ H := by
    rw [d.first_normalizer]
    exact (centralizer_le d.line_le_plane).trans (Subgroup.centralizer_le_normalizer _)
  have hYH : Y ≤ H := hYE.trans hCEH
  have hHY : H ≤ normalizer (Y : Set G) := normalizes_centralizingResidual U H
  have hTH : (T : Subgroup G) ≤ H := d.first_normalizer.symm ▸ d.line_stable
  have hYgE : Yg ≤ centralizer (E : Set G) := by
    have hn : g.val ∈ normalizer (centralizer (E : Set G) : Set G) :=
      ((normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer (E : Set G))).mp
        inferInstance) hgE
    exact (map_mono (f := c) hYE).trans_eq ((mem_normalizer_iff_map_conj_eq).mp hn)
  have hYgN : Yg ≤ normalizer (Y : Set G) := hYgE.trans (hCEH.trans hHY)
  have hYNg : Y ≤ normalizer (Yg : Set G) := by
    have hn : g.val ∈ normalizer (centralizer (E : Set G) : Set G) :=
      ((normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer (E : Set G))).mp
        inferInstance) hgE
    have hc : centralizer (E : Set G) ≤ H.map c := by
      rw [← (mem_normalizer_iff_map_conj_eq).mp hn]
      exact map_mono hCEH
    exact (hYE.trans hc).trans ((map_mono (f := c) hHY).trans
      (le_normalizer_map c))
  have hYN1 : Y ≤ normalizer (Y1 : Set G) :=
    ((le_inf Y.le_normalizer hYNg).trans inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image A (pResidual 2 A))
  have hAg : A ≤ centralizer (U.map c : Set G) :=
    inf_le_right.trans ((map_mono (f := c) hYC).trans
      (map_centralizer_le_centralizer_image _ c))
  have hAM : A ≤ M := by
    have hc : A ≤ centralizer (V : Set G) := by
      rw [← hjoin]
      exact le_centralizer_iff.mp (sup_le
        (le_centralizer_iff.mpr (inf_le_left.trans hYC)) (le_centralizer_iff.mpr hAg))
    exact hc.trans ((Subgroup.centralizer_le_normalizer _).trans
      (hNVL.trans_eq d.local_normalizer.symm))
  have h1M : Y1 ≤ YM := embedded_pResidual_mono 2 (le_inf inf_le_left hAM)
  have hMY : YM ≤ Y := (map_subtype_le _).trans inf_le_left
  have hMM : YM ≤ M := (map_subtype_le _).trans inf_le_right
  have hTM : (T : Subgroup G) ≤ normalizer (M : Set G) := by
    rw [d.local_normalizer]
    exact d.normalizes_L.trans (normalizer (L : Set G)).le_normalizer
  have hTYM : (T : Subgroup G) ≤ normalizer (YM : Set G) :=
    ((le_inf (hTH.trans hHY) hTM).trans inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image (Y ⊓ M) (pResidual 2 (Y ⊓ M : Subgroup G)))
  have hLYM : L ≤ normalizer (YM : Set G) :=
    natural_normalizes_fixed_actor d YM (isPPerfect_embedded_pResidual 2 _) hTYM
      (twoPerfect_seed_centralizer_fixes_module d YM (isPPerfect_embedded_pResidual 2 _)
        hMM (hMY.trans hYC) hTI) hNVL
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
    have he : Y1 = YM := le_antisymm h1M hM1
    have hn := natural_twoPerfect_normalizer_control d Y1
      (isPPerfect_embedded_pResidual 2 _) hne (he.symm ▸ hTYM)
      (h1M.trans hMM) (((map_subtype_le _).trans inf_le_left).trans hYC) hTI hunique
    have hYM := hYN1.trans hn
    have hYne : Y ≠ ⊥ := by
      intro hy
      apply hne
      exact le_bot_iff.mp (((map_subtype_le _).trans inf_le_left).trans_eq hy)
    exact natural_centralizingResidual_not_le d hTI hunique hescape hYne hYM
  have hp : pResidual 2 A = ⊥ := by
    apply (map_injective A.subtype_injective)
    simpa only [Subgroup.map_bot] using h1bot
  exact (isPGroup_quotient_pResidual (G := A) 2).of_equiv
    ((QuotientGroup.quotientMulEquivOfEq hp).trans
      (QuotientGroup.quotientBot : (A ⧸ (⊥ : Subgroup A)) ≃* A))
end CFSG.Quasithin.Chapter13.Section03.Noncentrality
