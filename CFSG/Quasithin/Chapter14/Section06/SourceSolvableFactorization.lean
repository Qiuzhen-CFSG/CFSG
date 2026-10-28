module
public import CFSG.Quasithin.Chapter14.Section06.SourceBlockOrderBound
public import CFSG.Quasithin.Chapter14.Section06.SourceIntersection
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicCore

/-!
# The solvable specialization of original 14.6.9

Choose an inclusion-minimal outside subgroup inside the given solvable group.
If its intersection residual fails to factor L, 14.6.6(5) supplies the unique
maximal overgroup required in C.5. Its odd radical vanishes by 14.6.7, so
solvability gives characteristic two. Every C.5 block is then A₃; the proved
small-block bound makes its Sylow subgroup have order at most 512, contrary
to the original numerical hypotheses. Factorization passes up to the given
group by monotonicity of the embedded residual.

Source: Aschbacher–Smith, 14.6.9, printed pp.1025–1028. This specialization
supplies precisely the factorizations needed to exclude the solvable
alternatives at the beginning of 14.6.10(5), avoiding its nonsolvable branches.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section06 ChapterC.Section06.Original
variable {G : Type*} [Group G] [Finite G]
private theorem solvable_c5_bound {H M K R : Subgroup G} (c : OriginalHypotheses H M K R R)
    (hsq : IsSQTK KnownSimple.IsKnownSimple H) [Group.IsSolvable H]
    (hi : R.relIndex M = 2) : Nat.card R ≤ 2 ^ 9 := by
  obtain ⟨b⟩ := c.block_decomposition_knownSimple hsq
  have hA (i : Fin b.size) : IsAlternatingBlock ((b.block i).map H.subtype) 3 :=
    RankOne.Solvable.isAlternatingBlock_of_equiv
      (equivMapOfInjective (b.block i) H.subtype H.subtype_injective)
      (chiZero_cubic_of_solvable (b.type i).2)
  apply small_block_sylow_card_from_original c hsq hi
  by_cases hs : b.size = 1
  · left
    let i : Fin b.size := ⟨0,b.positive⟩
    exact (single_block_eq_residual c b i hs) ▸ hA i
  · right; right
    have hs2 : b.size = 2 := by have := b.positive; have := b.size_le; omega
    let i : Fin b.size := ⟨0,by omega⟩
    let j : Fin b.size := ⟨1,by omega⟩
    have hij : i ≠ j := by intro he; have := congrArg Fin.val he; simp [i,j] at this
    refine ⟨(b.block i).map H.subtype,(b.block j).map H.subtype,?_,hA i,hA j,?_,
      c.pair_join b i j hij hs2⟩
    · intro he
      exact hij (b.injective ((map_injective H.subtype_injective) he))
    · apply commutator_eq_bot_iff_le_centralizer.mp
      rw [← map_commutator,commutator_eq_bot_iff_le_centralizer.mpr
        (b.commute (Ne.symm hij)),Subgroup.map_bot]

omit [Finite G] in
private theorem unique_transport (I B S : Subgroup G) (hB : B ≤ I)
    (hS : S ≤ B) (hmax : Maximal (fun Y : Subgroup G => Y < I) B)
    (hu : ∀ J : Subgroup G, S ≤ J → Maximal (fun Y : Subgroup G => Y < I) J → J = B) :
    Order.HasUniqueMaximalOver (S.subgroupOf I) ⊤ := by
  have hmaptop : (⊤ : Subgroup I).map I.subtype = I := by
    rw [←MonoidHom.range_eq_map,range_subtype]
  have hmap (X : Subgroup I) : X.map I.subtype < I ↔ X < ⊤ := by
    simpa only [hmaptop] using
      (map_lt_map_iff_of_injective I.subtype_injective (H := X) (K := ⊤))
  have hcov : B.subgroupOf I ⋖ ⊤ := by
    refine ⟨lt_top_iff_ne_top.mpr (fun he => hmax.1.not_ge (subgroupOf_eq_top.mp he)),?_⟩
    intro X hBX hX
    have he : X.map I.subtype ≤ B := hmax.2 ((hmap X).mpr hX) (by
      rw [←map_subgroupOf_eq_of_le hB]
      exact map_mono hBX.le)
    exact hBX.not_ge (by intro x hx; exact he (mem_map_of_mem I.subtype hx))
  refine ⟨lt_of_le_of_lt (subgroupOf_mono I hS) hcov.lt, B.subgroupOf I,
    ⟨subgroupOf_mono I hS,hcov⟩,?_⟩
  intro X hX
  have he : X.map I.subtype = B := hu _ (by
    rw [←map_subgroupOf_eq_of_le (hS.trans hB)]
    exact map_mono hX.1) ⟨(hmap X).mpr hX.2.lt,by
      intro Y hY hXY
      have hXIY : X ≤ Y.subgroupOf I := by
        intro x hx; exact hXY (mem_map_of_mem I.subtype hx)
      have hYtop : Y.subgroupOf I < ⊤ := lt_top_iff_ne_top.mpr
        (fun he => hY.not_ge (subgroupOf_eq_top.mp he))
      have hYX : Y.subgroupOf I ≤ X :=
        ((hX.2.eq_or_eq hXIY le_top).resolve_right hYtop.ne).le
      rw [←map_subgroupOf_eq_of_le hY.le]
      exact map_mono hYX⟩
  apply map_injective I.subtype_injective
  rw [map_subgroupOf_eq_of_le hB,he]

private theorem solvable_fitting (A : Type*) [Group A] [Finite A]
    [Group.IsSolvable A] (ho : pPrimeCore 2 A = ⊥) :
    generalizedFitting A = pCore 2 A := by
  have hE : componentLayer A = ⊥ := by
    apply sSup_eq_bot.mpr
    intro K hK
    let := hK.2
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
    exact (Group.IsPerfect.not_isSolvable K inferInstance).elim
  rw [generalizedFitting,hE,sup_bot_eq,Fitting_eq_pcore A 2 ho]

private theorem solvable_outside_bound
    (T : Sylow 2 G) (Tu M₀ Mc I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G) Tu Mc M₀))
    (hsq : IsSQTK KnownSimple.IsKnownSimple I) [Group.IsSolvable I]
    (hf : generalizedFitting I = pCore 2 I)
    (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup I) ⊤)
    (hproper : (T : Subgroup G) ⊓ I < (T : Subgroup G))
    :
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
  exact solvable_c5_bound c hsq hi


open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))
    (hlocal : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (H ⊓ centralizer ({u} : Set G)))

include hG hempty hM hunique hmany hcard e hab H hH hu hindex hmove hproduct hU3 hlocal


theorem source_lemma_14_6_9_of_solvable
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (I : Subgroup G) [Group.IsSolvable I]
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)) :
    (sourceResidual M Mc : Set G) =
      ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
        (sourceResidual M Mc ⊓ I).subtype : Set G) *
          ((sourceResidual M Mc).pCoreIn 2 : Set G) := by
  let : Finite (Subgroup G) :=
    Finite.of_injective (fun A : Subgroup G => (A : Set G)) SetLike.coe_injective
  obtain ⟨J,hJI,hJ,hSJ⟩ := exists_iMin_le_same_intersection (Set.toFinite _) hI
  let : Group.IsSolvable J := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hJI) (inclusion_injective _)
  obtain ⟨hSyl,hproper⟩ := source_suitable_intersection_sylow hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal J hJ.1.1
  rcases source_lemma_14_6_6_5 hG T hempty hM hunique hmany hcard e hab H hH
    u hu hindex hmove hproduct J hJ hSyl with hun | hf
  · obtain ⟨S,hS⟩ := hSyl
    have hu' : Order.HasUniqueMaximalOver (S : Subgroup J) ⊤ := by
      have hh := unique_transport J (J ⊓ Mc) ((T : Subgroup G) ⊓ J)
        inf_le_left hun.1 hun.2.1 hun.2.2
      have he : ((T : Subgroup G) ⊓ J).subgroupOf J = (S : Subgroup J) := by
        rw [←hS]
        exact comap_map_eq_self_of_injective J.subtype_injective _
      exact he ▸ hh
    have ho := (source_lemma_14_6_7_initial hG T hempty hM hunique hmany hcard e
      hab H hH u hu J hJ.1.1 S hS).2.2
    have hsq : IsSQTK KnownSimple.IsKnownSimple J := by
      let N := normalizer (J.pCoreIn 2 : Set G)
      have hJN : J ≤ N := J.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
      have hN : IsTwoLocal N := ⟨J.pCoreIn 2,hJ.1.1.1,isPGroup_pCoreIn 2 J,rfl⟩
      exact (IsSQTK.equiv (subgroupOfEquivOfLe hJN)).mp
        ((hG.twoLocal_sqtk hN).subgroup (J.subgroupOf N))
    have hb := solvable_outside_bound T _ M Mc J hJ.1 hsq
      (solvable_fitting J ho) S hS hu' hproper
    have hTcard := (source_lemma_14_6_9_order hG T hempty hM hunique hmany hcard e hab H hH
      hcoreIndex hrank).2
    let Tu := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
    have hi := source_lemma_14_6_3_1 hG T hempty hM hunique hmany hcard e hab H hH
      u hu hindex hmove hproduct
    have hTuIndex : Tu.relIndex (T : Subgroup G) = 4 := hi.2.1
    have hc : Nat.card Tu * 4 = Nat.card T := by
      simpa only [relIndex_bot_left,hTuIndex] using
        relIndex_mul_relIndex (⊥ : Subgroup G) Tu (T : Subgroup G) bot_le inf_le_left
    have hTuS : Tu ≤ (T : Subgroup G) ⊓ J := le_inf inf_le_left hJ.1.1.2.1
    have hle : Nat.card Tu ≤ Nat.card ((T : Subgroup G) ⊓ J : Subgroup G) :=
      Nat.card_le_card_of_injective (inclusion hTuS) (inclusion_injective _)
    change 2048 < Nat.card T at hTcard
    change Nat.card ((T : Subgroup G) ⊓ J : Subgroup G) ≤ 512 at hb
    omega
  · apply Set.Subset.antisymm
    · rw [hf.1]
      exact Set.mul_subset_mul
        (embedded_pResidual_mono 2 (inf_le_inf_left _ hJI)) (Set.Subset.refl _)
    · rintro x ⟨a,ha,b,hb,rfl⟩
      exact (sourceResidual M Mc).mul_mem
        (((map_subtype_le _).trans inf_le_left) ha) (pCoreIn_le _ _ hb)


end CFSG.Quasithin.Chapter14.Section06
