module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryPlaneNormalFactor
public import Theory.GroupTheory.DisjointCommutingProduct.CubicSylow

/-!
# The original component-normality theorem

The original faithful nine splits across the selected normal small factor
and its centralizer. Its marked point cubic projects onto both cubic
coordinates. The original Sylow normalizes the point residual and both
factors, so it normalizes the two projections of the point two-core.
Their join is a two-group and lies in that Sylow. The nine normalizes this
join and centralizes the point cubic. Recovering L₁⁺ as the two-residual
of their join forces the nine to normalize L₁⁺, contradicting the original
construction in the same Y, I₀ and point-span action quotient.

This excludes the nonnormal-component branch. The source application gives
T-normalization and literal K L₁ T membership in H_z, the two conclusions
of 14.7.32. Genuine earlier structural, module and 14.7.10 inputs remain
explicit. The same-G,T guarded successor and subsequent reductions through
14.7.52, including the full-residual alternatives, remain separate duties.

Source: Aschbacher–Smith, proof of 14.7.32, printed pp.1055–1059,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
universe u
variable {Q : Type*} [Group Q] [Finite Q]

/-- The faithful double projection forces normalization of the original
point residual once the actual Sylow preserves the selected factor. -/
theorem cubic_factor_split_normalizes
    (S : Sylow 2 Q) (P A L B : Subgroup Q) [IsMulCommutative P]
    (hsplit : CubicFactorSplit P A L B) (hp : IsPPerfect 2 L)
    (hg : B ⊔ L.pCoreIn 2 = L)
    (hLA : L ≤ normalizer (A : Set Q))
    (hSL : (S : Subgroup Q) ≤ normalizer (L : Set Q))
    (hSA : (S : Subgroup Q) ≤ normalizer (A : Set Q))
    (hm : Nonempty (A ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (A ≃* alternatingGroup (Fin 5)) ∨
        Nonempty (A ≃* Matrix.PSL3Two.PSL)) : P ≤ normalizer (L : Set Q) := by
  obtain ⟨hs,hcA,hcC,_,hcB,_,_,_,_,hBP,eP,heP,hi1,hi2⟩ := hsplit
  obtain ⟨hz,_,ho,_,_⟩ := small_thompson_factor_geometry A hm
  let C := centralizer (A : Set Q)
  have hd : Disjoint A C := by
    apply disjoint_def.mpr
    intro x hx hc
    have hzmem : (⟨x,hx⟩ : A) ∈ center A := by
      apply mem_center_iff.mpr
      intro a
      exact Subtype.ext (hc a a.property)
    exact congrArg Subtype.val (mem_bot.mp (hz ▸ hzmem) : (⟨x,hx⟩ : A) = 1)
  have hc : A ≤ centralizer (C : Set Q) := le_centralizer_iff.mpr le_rfl
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A C hd hc
  have hLN : L ≤ A ⊔ C := pPerfect_le_sup_centralizer_of_pGroup_outer A L hp ho hLA
  have hPB : P ≤ normalizer (B : Set Q) := by
    intro p hpP
    apply (Subgroup.centralizer_le_normalizer _)
    intro b hb
    exact congrArg Subtype.val (mul_comm (⟨b,hBP hb⟩ : P) ⟨p,hpP⟩)
  apply normalizes_of_projected_cubic_supplement S A C L B P e he hc hLN hp hg hSA
    (hSA.trans (normalizer_le_normalizer_centralizer A)) hSL hPB
  exact le_sup_projections_of_faithful_cubic_split A C P B e he hc hs hcB hcA hcC hBP
    eP heP hi1 hi2

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
theorem local_cComponent_normal
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
    local_nonnormal_component_weakClosure_normal_factor d h hab structural previous
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
theorem local_component_sylow_normalized_and_mem_Hz
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent) :
    (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      K ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) ∈ F.Hz L (normalizer (L : Set G)) := by
  have hn := local_cComponent_normal d h hab structural previous faithful earlier I K hI hKI hK
  have hTN : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (F.sylow_le_of_mem_Hz hI).trans ((normal_subgroupOf_iff_le_normalizer hKI).mp hn)
  have hspan : conjugateSpanBy K (T : Subgroup G) = K :=
    le_antisymm (conjugateSpanBy_le le_rfl hTN) (le_conjugateSpanBy _ _)
  have hm := (local_component_reduced_mem_Hz h structural I hI (K.subgroupOf I) hK).2.2
  exact ⟨hTN,by simpa only [map_subgroupOf_eq_of_le hKI,hspan] using hm⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
