module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerLocalG2
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerAlternatingGeometry
public import Theory.GroupTheory.MaximumElementaryUniqueLift

/-!
# The two-member maximum family at the G₂ centralizer endpoint

Write Q=O₂(LT) and R=O₂(XT), where X is the actual residual of C_L(Ω₁Z(T)).
Once Q is elementary and lies in R, its self-centrality follows from the
already proved Sylow centralizer of the source omega module. The original
Sylow normalizer preserves R in the G₂ row. A unique nonzero image and a
single element detecting the fixed space therefore give A(R)={Q,Qᵈ}.
An odd escaping subgroup must normalize Q, contradicting local uniqueness.

Only the preceding factorization/elementarity and marked image/fixed-space
inputs remain explicit. No NoEscape premise or later A₆ terminal argument
is used. The main source owner constructs these inputs for the same Q and R.

Source: Aschbacher--Smith 3.3.28, final paragraph, printed p.601, and B.2.21,
printed pp.82--83. Right conjugation by d is map by MulAut.conj d⁻¹.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
universe u v
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem local_core_self_centralizing
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsShort L)
    (hQR : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ blockLocalCore T L)
    (hQe : IsElementaryAbelian 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2)) :
    centralizer (((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf
      (blockLocalCore T L) : Set (blockLocalCore T L)) =
      ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf (blockLocalCore T L) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let R := blockLocalCore T L
  let W := blockOmegaModule T L
  let _ : IsElementaryAbelian 2 Q := hQe
  have hWQ : W ≤ Q := blockOmegaModule_le_core h
  have hRT : R ≤ (T : Subgroup G) := by
    change (blockLocalResidual T L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (blockLocalResidual T L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  apply le_antisymm
  · intro r hr
    apply (sylow_centralizer_blockOmegaModule_eq_local_core h D hescape hb).le
    refine ⟨hRT r.property, ?_⟩
    intro w hw
    exact congrArg Subtype.val (hr (⟨w,hQR (hWQ hw)⟩ : R) (hWQ hw))
  · intro r hr s hs
    apply Subtype.ext
    exact (le_centralizer_iff_isMulCommutative.mpr inferInstance : Q ≤ centralizer (Q : Set G))
      hr s hs

/-- The literal 3.3.28 endpoint: the two source image/fixer facts force an
odd escaping subgroup to normalize the nontrivial local core. -/
theorem false_of_g2_local_unique_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥) (hb : ChapterC.IsG2TwoBlock L)
    (B : Subgroup G) (hBN : B ≤ normalizer (T : Set G)) (hodd : Odd (Nat.card B))
    (d : G) (hd : d ∈ B) (hout : d ∉ normalizer (L : Set G))
    (hQR : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ blockLocalCore T L)
    (hQe : IsElementaryAbelian 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2))
    {H : Type v} [Group H] (q : blockLocalCore T L →* H)
    (hker : q.ker = ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf (blockLocalCore T L))
    (a : blockLocalCore T L)
    (ha : a ∈ (((L ⊔ (T : Subgroup G)).pCoreIn 2).map
      (MulAut.conj d⁻¹).toMonoidHom).subgroupOf (blockLocalCore T L))
    (hfix : ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf (blockLocalCore T L) ⊓
        centralizer ((((L ⊔ (T : Subgroup G)).pCoreIn 2).map
          (MulAut.conj d⁻¹).toMonoidHom).subgroupOf (blockLocalCore T L) : Set (blockLocalCore T L)) =
      ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf (blockLocalCore T L) ⊓
        centralizer ({a} : Set (blockLocalCore T L)))
    (hcommon : ∀ A ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup (blockLocalCore T L)),
      ¬ A ≤ ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf (blockLocalCore T L) →
        A.map q = ((((L ⊔ (T : Subgroup G)).pCoreIn 2).map
          (MulAut.conj d⁻¹).toMonoidHom).subgroupOf (blockLocalCore T L)).map q) : False := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let R := blockLocalCore T L
  let _ : IsElementaryAbelian 2 Q := hQe
  have hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G) :=
    fun hn => hout (hn (hBN hd))
  have hBR : B ≤ normalizer (R : Set G) :=
    hBN.trans (((blockLocalInvariance_of_g2Two h D hfixed hb).1 (Or.inr hb)).2)
  have hself := local_core_self_centralizing h D hescape hb.short hQR hQe
  have hpair := Stellmacher.odd_normalizes_conjugate_pair R B Q hQR d⁻¹
    ((normalizer (R : Set G)).inv_mem (hBR hd)) q hker hself a ha hfix hcommon hBR hodd
  have hQne : Q ≠ ⊥ := fun he => D.ne_bot (bot_unique (D.le_core.trans_eq he))
  have hHQ : L ⊔ (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hQL : normalizer (Q : Set G) ≤ normalizer (L : Set G) :=
    D.normal_subgroup_normalizer_le h.toHypothesis1221 (pCoreIn_le 2 _) hQne hHQ
  exact hout (hQL (hpair.2 hd))

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
