module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.ResidualControl
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalUnitaryNoncentrality.Applicability
/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalUnitaryNoncentrality.ResidualControl`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {V : Subgroup G} [IsElementaryAbelian 2 V]

/-- TI placement and the actual natural pairing make a two-perfect seed
centralizer fix the original module. -/
theorem unitary_twoPerfect_seed_centralizer
    (L U Y : Subgroup G) (rho : Automizer V →* Atlas.G2.Model F)
    (E : Additive V ≃ₗ[F] W)
    (he : ∀ a v, E (automizerRepresentation V a v) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hs : pointCoordinateSubspace E U = seed) (hUV : U ≤ V) (hUn : U ≠ ⊥)
    (hY : IsPPerfect 2 Y) (hYM : Y ≤ normalizer (L : Set G))
    (hYC : Y ≤ centralizer (U : Set G))
    (hTI : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨ V.map (MulAut.conj g).toMonoidHom = V) :
    Y ≤ centralizer (V : Set G) := by
  have hYN : Y ≤ normalizer (V : Set G) := by
    intro y hy
    exact inf_centralizer_le_normalizer_of_trivial_intersections hTI hUn hUV
      ⟨hYM hy,hYC hy⟩
  have hm : ⁅V,Y⁆ ≤ U :=
    commutator_le_seed_of_point_centralizer V U Y rho E he hs hYN hYC
  apply le_centralizer_iff.mp
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [← commutator_isPPerfect_idempotent Y V hY (IsElementaryAbelian.isPGroup 2 V) hYN]
  exact commutator_eq_bot_iff_le_centralizer.mpr (hm.trans (le_centralizer_iff.mp hYC))

/-- The first normalizer bound of 13.3.14(b), preserving two-perfectness
and normality only in the actual local product with T. -/
theorem unitary_twoPerfect_seed_normalizer_control
    (T : Sylow 2 G) (L U Z Y : Subgroup G)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (rho : Automizer V →* Atlas.G2.Model F) (E : Additive V ≃ₗ[F] W)
    (he : ∀ a v, E (automizerRepresentation V a v) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hs : pointCoordinateSubspace E U = seed) (hUV : U ≤ V)
    (hZU : Z ≤ U) (hZT : Z ≤ (T : Subgroup G)) (hZn : Z ≠ ⊥)
    (hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hLN : L ≤ normalizer (V : Set G))
    (hfaith : L ⊓ centralizer (V : Set G) ≤ L.pCoreIn 2)
    (hY : IsPPerfect 2 Y) (hne : Y ≠ ⊥)
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hYM : Y ≤ normalizer (L : Set G)) (hYC : Y ≤ centralizer (U : Set G))
    (hTI : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨ V.map (MulAut.conj g).toMonoidHom = V)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N →
      N = normalizer (L : Set G)) : normalizer (Y : Set G) ≤ normalizer (L : Set G) := by
  have hUn : U ≠ ⊥ := fun hz => hZn (le_bot_iff.mp (hZU.trans_eq hz))
  have hYV := unitary_twoPerfect_seed_centralizer L U Y rho E he hs hUV hUn hY hYM hYC hTI
  have hLC : L ≤ normalizer (centralizer (V : Set G) : Set G) :=
    hLN.trans ((normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer _)).mp inferInstance)
  have hcomm : ⁅L,Y⁆ ≤ L.pCoreIn 2 :=
    (le_inf (le_normalizer_iff_commutator_le_left.mp hYM)
      ((commutator_mono le_rfl hYV).trans
        (le_normalizer_iff_commutator_le_right.mp hLC))).trans hfaith
  have hQT : L.pCoreIn 2 ≤ (T : Subgroup G) := by
    apply (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer hTL)).trans
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hLY : L ≤ normalizer (Y : Set G) :=
    Noncentrality.normalizes_of_commutator_le_twoGroup L Y (L.pCoreIn 2) hY
      (isPGroup_pCoreIn 2 L) (hQT.trans hTY)
      (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))) hcomm
  let J := Y ⊔ (T : Subgroup G)
  have hZJ : J ≤ normalizer (Z : Set G) :=
    sup_le (hYC.trans ((centralizer_le hZU).trans (Subgroup.centralizer_le_normalizer _))) hTZ
  have hZcore : Z ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le hZT) (hZT.trans le_sup_right) hZJ
  have hJcore : J.pCoreIn 2 ≠ ⊥ := fun hz => hZn (le_bot_iff.mp (hZcore.trans_eq hz))
  have hJ : J ∈ Chapter1.He G := Chapter1.lemma_1_1_4_6 T
    (hG.evenCharacteristic T) ⟨hJcore,fun _ ht => (show (T : Subgroup G) ≤ J from le_sup_right) ht⟩
  have hYn : (Y.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le Y.le_normalizer hTY)
  have hYe : Y ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_3_1 hJ hne le_sup_left hYn.isSubnormal
  have hcore : Y.pCoreIn 2 ≠ ⊥ := by
    intro hz
    apply hne
    apply le_bot_iff.mp
    intro y hy
    have hh := hYe ⟨hy,?_⟩
    · exact hz ▸ hh
    · rw [hz]
      intro x hx
      rw [mem_bot.mp hx]
      simp
  have hncore := normalizer_le_normalizer_characteristic_image Y (pCore 2 Y)
  exact hncore.trans (normalizer_le_of_unique_maximalTwoLocal hu
    (isPGroup_pCoreIn 2 Y) hcore ((sup_le hLY hTY).trans hncore))

/-- The original centralizing two-residual is trivial or escapes M.
Only the universal earlier 12.2 theorems remain as source inputs. -/
theorem unitary_original_centralizingResidual_not_le
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (h : Hypothesis1331 D.T D.L) (chosen : ChosenModule D.T D.L D.V)
    (hmax : D.L ∈ Chapter1.LStar G (D.T : Subgroup G))
    (eL : (D.L ⧸ pCore 2 D.L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (structural : Structural1222At KnownSimple.IsKnownSimple D.T)
    (e : inducedAutomizer D.V D.L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0 : Additive D.V ≃ₗ[F] Atlas.G2.Natural.Space F)
    (he0 : ∀ (l : inducedAutomizer D.V D.L) v,
      E0 (automizerRepresentation D.V l v) =
        Atlas.G2.Natural.derivedAction F (e l) (E0 v))
    (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
    (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
    (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
    (B : Subgroup G) (hBV : B ≤ D.V)
    (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
    (hHfull : D.H = normalizer (D.V₁ : Set G))
    (earlier : Theorem12213At KnownSimple.IsKnownSimple D.T)
    (hne : Noncentrality.centralizingResidual D.UH ≠ ⊥) :
    ¬ Noncentrality.centralizingResidual D.UH ≤ normalizer (D.L : Set G) := by
  intro hYM
  have h12 := unitary_original_hypothesis1223 h hmax eL
  obtain ⟨hTN,hNL⟩ := unitary_original_module_normalizers h hmax eL chosen structural
  obtain ⟨rho,E,he,_,_,hz,_,hs⟩ := exists_unitary_flag_marking D.T D.L D.V₁ B D.Vplus
    chosen.normalizes hNL e E0 he0 hTN hZV hBV hUV hTZ hTB hTU hZ hB hU
  have hZU : D.V₁ ≤ D.Vplus := by
    intro z hz'
    let v : Additive D.V := Additive.ofMul ⟨z,hZV hz'⟩
    have hv : E v ∈ pointLine := hz ▸ (mem_pointCoordinateSubspace E D.V₁ v).mpr hz'
    exact (mem_pointCoordinateSubspace E D.Vplus v).mp (hs.symm ▸ pointLine_le_seed hv)
  have hZn : D.V₁ ≠ ⊥ := D.V₁.one_lt_card_iff_ne_bot.mp (by omega)
  let : IsSimpleGroup Atlas.G2.Natural.BinaryNormalizer.Derived :=
    Atlas.G2.isSimple_commutator_binary
  have hfaith : D.L ⊓ centralizer (D.V : Set G) ≤ D.L.pCoreIn 2 := by
    have hc := congrArg (map D.L.subtype) (chosen.centralizer_eq_core_of_simple eL.isSimpleGroup)
    exact (show D.L ⊓ centralizer (D.V : Set G) = D.L.pCoreIn 2 by
      simpa only [pCoreIn,subgroupOf_map_subtype,inf_comm] using hc).le
  have hTH : (D.T : Subgroup G) ≤ D.H := hHfull ▸ hTZ
  have hHY : D.H ≤ normalizer (Noncentrality.centralizingResidual D.UH : Set G) :=
    Noncentrality.normalizes_centralizingResidual D.Vplus D.H
  have hN := unitary_twoPerfect_seed_normalizer_control D.T D.L D.Vplus D.V₁
    (Noncentrality.centralizingResidual D.UH) h.qtke rho E he hs hUV hZU
    (hZV.trans chosen.le_sylow) hZn hTZ chosen.sylow_normalizes_component chosen.normalizes
    hfaith (Noncentrality.centralizingResidual_isPPerfect D.UH) hne (hTH.trans hHY) hYM
    (Noncentrality.centralizingResidual_le_seed_centralizer D.Vplus D.H)
    (h12.source_chosen_TI_at structural chosen)
    (h12.source_normalizer_maximal_unique_at structural
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))).2
  have hout : ¬ D.H ≤ normalizer (D.L : Set G) := by
    rw [hHfull]
    exact unitary_original_line_escape h h12 earlier chosen e E0 he0 hZV hZ
  exact hout (hHY.trans hN)
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
