module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NonnormalBinarySourceAt.PlaneNormalFactor

/-!
# The same-G,T terminal exchanged-component source argument

The original cubic, nine-group, Sylow and local quotients are retained.
Only the structural and predecessor statements at the original G,T are used.
Generic small-factor and cubic projection lemmas are reused unchanged.
Source: Aschbacher–Smith 14.7.32, printed pp.1058–1059.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
universe u
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.Components Swapped Swapped.LinearTwo ModuleAlternatives
open Chapter15.Section03.AbelianAmalgam
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Representation Representation.BinaryOffender Stellmacher
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The terminal nine-group contradiction excludes every nonnormal local
C-component, using the same constructed Y, I₀, cubic and action quotient. -/
theorem local_cComponent_normal_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent) :
    (K.subgroupOf I).Normal := by
  by_contra hnormal
  obtain ⟨c,hs,hR,ha,hE,hfour,hplane,hRT,hJR,hRN,hSylow,hcore,he,hVW,hWR,hIW,
    hlocal,hproper,hIeq,hcharI,hsqtk,hred,hPVI,hVIW,hmove,hJplus,hsub,hne,hYn,hescape,hres,hgen,
    l,hl,hl3,hlgen,y,hy,hy3,hly,hE9,hcard,hplus,hIgen,hplusNot,
    A,hAJ,hAn,hAsub,hAnormal,hmodel,hresA,hLA,hPA,hTA,hTL,hsplit⟩ :=
    local_nonnormal_component_weakClosure_normal_factor_at d h hab structural previous
      faithful earlier I K hI hKI hK hnormal
  let J := F.Li L 1 ⊔ (T : Subgroup G)
  let R := F.H.pCoreIn 2 ⊔ conjugateSpanBy c.Uα J
  let Y := (F.H.pCoreIn 2 ⊔ c.Qα) ⊔ R
  let I₀ := J ⊔ Y
  let W := conjugateSpanBy (F.Vi 1) I₀
  let : (W.subgroupOf I₀).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let q := QuotientGroup.mk' (centralizer (W.subgroupOf I₀ : Set I₀))
  let E := zpowers y ⊔ zpowers (l : G)
  let Eplus := (E.subgroupOf I₀).map q
  let Bplus := ((zpowers (l : G)).subgroupOf I₀).map q
  let D := (F.Li L 1).subgroupOf I₀
  let Dplus := D.map q
  let : A.Normal := hAnormal
  let : IsElementaryAbelian 3 E := hE9
  have hEI : E ≤ I₀ := le_sup_right.trans_eq hIgen
  let : IsElementaryAbelian 3 (E.subgroupOf I₀) := IsElementaryAbelian.subgroupOf hEI
  let : IsElementaryAbelian 3 Eplus := IsElementaryAbelian.map q
  have hLI : F.Li L 1 ≤ I₀ := le_sup_left.trans le_sup_left
  have hpowL : zpowers (l : G) ≤ F.Li L 1 := le_sup_left.trans_eq hlgen
  have hlI : (l : G) ∈ I₀ := hLI (hpowL (mem_zpowers _))
  let lI : I₀ := ⟨l,hlI⟩
  have hpow : (zpowers (l : G)).subgroupOf I₀ = zpowers lI := by
    apply map_injective I₀.subtype_injective
    rw [map_subgroupOf_eq_of_le (hpowL.trans hLI),MonoidHom.map_zpowers]
    rfl
  have hgenD : zpowers lI ⊔ D.pCoreIn 2 = D := by
    rw [show D = (F.Li L 1).subgroupOf I₀ from rfl,
      pCoreIn_subgroupOf 2 _ I₀ hLI,←hpow,
      ←subgroupOf_sup (hpowL.trans hLI) ((pCoreIn_le 2 _).trans hLI),hlgen]
  have hpD : IsPPerfect 2 D :=
    (show IsPPerfect 2 (F.Li L 1) from isPPerfect_embedded_pResidual 2 _).of_surjective
      (subgroupOfEquivOfLe hLI).symm.toMonoidHom (subgroupOfEquivOfLe hLI).symm.surjective
  have hpDplus : IsPPerfect 2 Dplus := hpD.of_surjective (q.subgroupMap D)
    (q.subgroupMap_surjective D)
  have hRle : (D.pCoreIn 2).map q ≤ Dplus.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 D).map q)
      (map_mono (pCoreIn_le 2 D))
    exact (map_mono (D.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image D (pCore 2 D)))).trans
        ((D.pCoreIn 2).le_normalizer_map q)
  have hgenplus : Bplus ⊔ Dplus.pCoreIn 2 = Dplus := by
    have hh : Bplus ⊔ (D.pCoreIn 2).map q = Dplus := by
      change ((zpowers (l : G)).subgroupOf I₀).map q ⊔ (D.pCoreIn 2).map q = D.map q
      rw [hpow,←Subgroup.map_sup,hgenD]
    apply le_antisymm (sup_le (le_sup_left.trans_eq hh) (pCoreIn_le 2 Dplus))
    calc
      Dplus = Bplus ⊔ (D.pCoreIn 2).map q := hh.symm
      _ ≤ Bplus ⊔ Dplus.pCoreIn 2 := sup_le_sup le_rfl hRle
  have hTI : (T : Subgroup G) ≤ I₀ := le_sup_right.trans le_sup_left
  let S := (T.subtype hTI).mapSurjective (QuotientGroup.mk'_surjective
    (centralizer (W.subgroupOf I₀ : Set I₀)))
  have hS : (S : Subgroup _) = ((T : Subgroup G).subgroupOf I₀).map q := by
    rw [Sylow.coe_mapSurjective,Sylow.coe_subtype]
  apply hplusNot
  exact cubic_factor_split_normalizes S Eplus A Dplus Bplus hsplit hpDplus hgenplus hLA
    (by rwa [hS]) (by rwa [hS]) (hmodel.imp id fun hh => hh.2)
/-- Source 14.7.32: the original Sylow normalizes every local component,
and K L₁ T belongs to the original H_z family. -/
theorem local_component_sylow_normalized_and_mem_Hz_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent) :
    (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      K ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) ∈ F.Hz L (normalizer (L : Set G)) := by
  have hn := local_cComponent_normal_at d h hab structural previous faithful earlier I K hI hKI hK
  have hTN : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (F.sylow_le_of_mem_Hz hI).trans ((normal_subgroupOf_iff_le_normalizer hKI).mp hn)
  have hspan : conjugateSpanBy K (T : Subgroup G) = K :=
    le_antisymm (conjugateSpanBy_le le_rfl hTN) (le_conjugateSpanBy _ _)
  have hm := (local_component_reduced_mem_Hz_at h structural I hI (K.subgroupOf I) hK).2.2
  exact ⟨hTN,by simpa only [map_subgroupOf_eq_of_le hKI,hspan] using hm⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
