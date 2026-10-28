module
public import CFSG.Quasithin.ChapterC.Section06.SmallBlockOrder
public import CFSG.Quasithin.Chapter14.Section06.SourceNormalSubgroups
public import Theory.GroupTheory.SubgroupEnumerationBinary
public import Mathlib.Order.Atoms.Finite

/-!
# The small-block order bound in original 14.6.9

For an actual member I of the maximal outside family, choose an index-two
overgroup of T ∩ I inside T. The proved IStar normalizer theorem excludes
every nonzero subgroup normal in both this overgroup and I, supplying the
original C.5 configuration. Its small-block order theorem then gives
|T ∩ I| ≤ 2⁹ for an A₃ block, an A₅ block or two commuting A₃ blocks.

The Sylow and unique-maximal-overgroup inputs are the preceding source
14.6.6(2),(5). The strict inclusion in T and the characteristic-two fitting
identity are the current case of 14.6.9; no quotient-model hypothesis is added.
Source: Aschbacher–Smith, 14.6.9, printed p.1025 (refs/quasithin.pdf).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section06
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section06 ChapterC.Section06.Original
variable {G : Type*} [Group G] [Finite G]
/-- The small-block exclusion used in original 14.6.9. The original outside
family discharges normalizer control; the Sylow and unique-overgroup hypotheses
are the preceding 14.6.6(2),(5). No quotient-model premise is added. -/
theorem source_lemma_14_6_9_small_blocks
    (T : Sylow 2 G) (Tu M₀ Mc I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G) Tu Mc M₀))
    (hsq : IsSQTK KnownSimple.IsKnownSimple I)
    (hf : generalizedFitting I = pCore 2 I)
    (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup I) ⊤)
    (hproper : (T : Subgroup G) ⊓ I < (T : Subgroup G))
    (htype : IsAlternatingBlock ((pResidual 2 I).map I.subtype) 3 ∨
      IsAlternatingBlock ((pResidual 2 I).map I.subtype) 5 ∨
      CubicPair ((pResidual 2 I).map I.subtype)) :
    Nat.card ((T : Subgroup G) ⊓ I : Subgroup G) ≤ 2 ^ 9 := by
  let R := (T : Subgroup G) ⊓ I
  let K := (pResidual 2 I).map I.subtype
  have hR : R.subgroupOf (T : Subgroup G) < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    exact fun he => hproper.not_ge (subgroupOf_eq_top.mp he)
  obtain ⟨X,hX,_⟩ := exists_covBy_le_of_lt hR
  have hiX := SubgroupEnumeration.relIndex_two_of_covBy T.isPGroup' hX
  let M := X.map (T : Subgroup G).subtype
  have hRM : R ≤ M := by
    rw [←map_subgroupOf_eq_of_le (show R ≤ (T : Subgroup G) from inf_le_left)]
    exact map_mono hX.le
  have hMT : M ≤ (T : Subgroup G) := map_subtype_le _
  have hi : R.relIndex M = 2 := by
    have he := relIndex_map_map_of_injective (R.subgroupOf (T : Subgroup G)) X
      (T : Subgroup G).subtype_injective
    rw [map_subgroupOf_eq_of_le (show R ≤ (T : Subgroup G) from inf_le_left)] at he
    exact he.trans hiX
  have hn : (R.subgroupOf M).Normal := normal_of_index_eq_two hi
  have hMR : M ≤ normalizer (R : Set G) := (normal_subgroupOf_iff_le_normalizer hRM).mp hn
  have hRH : R ⊔ K = I := by
    have hh := congrArg (Subgroup.map I.subtype) (pResidual_sup_sylow_eq_top S)
    simpa only [Subgroup.map_sup,hS,←MonoidHom.range_eq_map,range_subtype,sup_comm] using hh
  have hSylow : ∃ P : Sylow 2 (R ⊔ K : Subgroup G),
      (P : Subgroup (R ⊔ K : Subgroup G)).map (R ⊔ K).subtype = R := by
    rw [hRH]
    exact ⟨S,hS⟩
  obtain ⟨P,hP⟩ := hSylow
  have c : OriginalHypotheses I M K R R := {
    fitting := hf
    sylow := S
    sylow_image := hS
    unique := hu
    residual := rfl
    R_le := le_rfl
    T_le := hRM
    R_normal := hMR
    residual_sylow := P
    residual_sylow_image := hP
    no_common_normal := by
      intro W hWR hWnormal
      by_contra hW
      have hw : M ⊔ I ≤ normalizer (W : Set G) :=
        (normal_subgroupOf_iff_le_normalizer (hWR.trans (hRM.trans le_sup_left))).mp hWnormal
      have hc := (source_lemma_14_6_9_normalizers T Tu M₀ Mc I hI W hW hWR
        (le_sup_right.trans hw)).2.2.2 M hRM hMT
      have he : M ≤ R := (le_inf le_rfl (le_sup_left.trans hw)).trans hc.le
      have hh : R.relIndex M = 1 := relIndex_eq_one.mpr he
      omega }
  exact small_block_sylow_card_from_original c hsq hi htype

end CFSG.Quasithin.Chapter14.Section06
