module
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.Contracts
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure
public import Theory.GroupTheory.ReducedNormal.MovedCentralizer
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
public import Theory.GroupTheory.ConjugateSpanSupplement
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.Commutator.SylowFixedSeed
public import Theory.GroupTheory.SylowFixedConjugateSpanSplitting
public import Theory.GroupTheory.Commutator.SimpleSubnormal

/-!
# Maximal local enlargement and the literal omega-module

Source 1.2.4 preserves Sylow normalization when enlarging the witnessed local
component. The actual omega-span is reduced by B.2.14. Its commutator with
the local component is reduced as well, because that component is the
literal two-residual of its Sylow join. Sylow averaging then gives the
source splitting with the fixed factor in the original omega-center.
Irreducibility, when established, eliminates the fixed space of the nonzero
commutator by perfectness. No module marking or classification is assumed.

Source: Aschbacher--Smith 1.2.4, p.505, B.2.14, p.78, and the construction
in the proof of 5.1.13, p.637.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]

namespace LocalCartanWitness
variable {T : Sylow 2 G} {H A Y X D : Subgroup G}
  (d : LocalCartanWitness T H A Y X D)
include d

/-- Normalization survives passage to any containing local component. -/
theorem overcomponent_sylow_normalizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTH : (T : Subgroup G) ≤ H) (hY : Y ∈ Chapter1.HOver G (H : Set G))
    {K : Subgroup G} (hK : K ∈ Chapter1.L G (T : Subgroup G)) (hXK : X ≤ K) :
    (T : Subgroup G) ≤ normalizer (K : Set G) := by
  let J := K ⊔ (T : Subgroup G)
  have hXJ : X ≤ J := hXK.trans le_sup_left
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hx : X.subgroupOf J ∈ Chapter1.L J (S : Subgroup J) :=
    (Chapter1.mem_LIn_iff_subgroupOf le_sup_right hXJ).mp
      ⟨hXJ, d.mem_localFamily hTH hY⟩
  have hn : (S : Subgroup J) ≤ normalizer (X.subgroupOf J : Set J) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (d.sylow_normalizes hTH hY.2 hs) (x : G)
  have hq := Chapter1.Section02.uniqueness_local_quotient_sqtk hG hK.2.2
  obtain ⟨C, ⟨hC, hXC, hCN⟩, _⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source hq S hx hn
  obtain ⟨C₀, _, hu⟩ := Chapter1.Section02.lemma_1_2_4_containment_of_A_3_12
    (Chapter1.Section02.containment_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)) hq S hx
  have he : K.subgroupOf J = C :=
    (hu _ ⟨hK.1, comap_mono hXK⟩).trans (hu _ ⟨hC, hXC⟩).symm
  have hKN : (K.subgroupOf J).Normal := he.symm ▸ hCN
  exact (show (T : Subgroup G) ≤ J from le_sup_right).trans
    ((normal_subgroupOf_iff_le_normalizer (show K ≤ J from le_sup_left)).mp hKN)

/-- The source witness has a normalized noncentral maximal overcomponent. -/
theorem exists_normalized_maximal_local
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTH : (T : Subgroup G) ≤ H) (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hXC : ¬ X ≤ omegaCentralizer T) :
    ∃ K ∈ Chapter1.LStar G (T : Subgroup G), X ≤ K ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧ ¬ K ≤ omegaCentralizer T := by
  obtain ⟨K,hK,hXK⟩ := d.exists_maximal_local hTH hY
  exact ⟨K,hK,hXK,d.overcomponent_sylow_normalizes hG hTH hY hK.1 hXK,
    fun hc => hXC (hXK.trans hc)⟩
end LocalCartanWitness

namespace LocalOmega
variable (T : Sylow 2 G) (K : Subgroup G)

omit [Finite G] in
private theorem seed_le : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤
    (T : Subgroup G) := by
  intro z hz
  exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).1

omit [Finite G] in
/-- The Sylow supplement does not enlarge the literal omega-span. -/
theorem span_join (hn : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
      (K ⊔ (T : Subgroup G)) =
    conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) K := by
  exact conjugateSpanBy_sup_of_normalizes_seed _ _ _
    (sylow_le_omegaCentralizer.trans (Subgroup.centralizer_le_normalizer _)) hn

/-- B.2.14 on the actual maximal-component join, prior to FF classification. -/
theorem span_reduced (hE : IsEvenCharacteristicAt T)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    IsPReduced 2 ((conjugateSpanBy
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) K).subgroupOf
      (K ⊔ (T : Subgroup G))) := by
  let J := K ⊔ (T : Subgroup G)
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hZJ := (seed_le T).trans (show (T : Subgroup G) ≤ J from le_sup_right)
  have hz : Stellmacher.omegaOneCenterAmbient (S : Subgroup J) =
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)).subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [← Stellmacher.omegaOneCenterAmbient_map_injective J.subtype J.subtype_injective,
      map_subgroupOf_eq_of_le hZJ]
    congr 1
    exact map_subgroupOf_eq_of_le le_sup_right
  have hc := Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T hE
    (show J ∈ Chapter1.HOver G (T : Set G) from ⟨hK.2.2,show (T : Subgroup G) ≤ J from le_sup_right⟩))
  have hr := omegaCenter_normalClosure_reduced S hc
  rw [hz, normalClosure_subgroupOf_eq_conjugateSpanBy _ J hZJ] at hr
  simpa only [J, span_join T K hn] using hr

private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hN hp
  let : N.Normal := hN
  by_contra hne
  let : Nontrivial (A ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (A ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (A ⧸ N) := hp.isNilpotent
  exact Group.IsPerfect.not_isSolvable (A ⧸ N) inferInstance

/-- The source's U is reduced; no classification or irreducibility is needed. -/
theorem module_reduced (hE : IsEvenCharacteristicAt T)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    localOmegaModule T K ∈ reducedFamily (K ⊔ (T : Subgroup G)) := by
  let J := K ⊔ (T : Subgroup G)
  let V := conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) K
  let K' := K.subgroupOf J
  let V' := V.subgroupOf J
  have hVJ : V ≤ J := conjugateSpanBy_le_self ((seed_le T).trans le_sup_right) |>.trans'
    (conjugateSpanBy_mono le_rfl (show K ≤ J from le_sup_left))
  have hv : IsPReduced 2 V' := span_reduced T K hE hK hn
  let : V'.Normal := hv.normal
  let : IsElementaryAbelian 2 V' := hv.elementary
  let : K'.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hn)
  let : Group.IsPerfect K' := hK.1.perfect
  have hres : pResidual 2 J = K' := by
    apply pResidual_eq_of_isPPerfect_sup K' ((T : Subgroup G).subgroupOf J)
      perfect_twoPerfect T.isPGroup'.comap_subtype
    rw [← subgroupOf_sup (show K ≤ J from le_sup_left) le_sup_right, subgroupOf_self]
  have hr : IsPReduced 2 ⁅V',K'⁆ := by
    rw [← hres]
    exact hv.moved V'
  have he : (⁅V',K'⁆).map J.subtype = localOmegaModule T K := by
    rw [map_commutator, map_subgroupOf_eq_of_le hVJ,
      map_subgroupOf_eq_of_le (show K ≤ J from le_sup_left)]
  have huJ : localOmegaModule T K ≤ J := he ▸ map_subtype_le _
  have he' : (localOmegaModule T K).subgroupOf J = ⁅V',K'⁆ := by
    rw [← he]
    exact comap_map_eq_self_of_injective J.subtype_injective _
  have hr' : IsPReduced 2 ((localOmegaModule T K).subgroupOf J) := he'.symm ▸ hr
  refine ⟨huJ, ?_, hr'.normal, hr'.quotient_pCore_eq_bot⟩
  let := hr.elementary
  rw [← he]
  exact IsElementaryAbelian.map _

omit [Finite G] in
/-- Noncentrality of the original omega-center makes the same U nonzero. -/
theorem module_ne_bot (hC : ¬ K ≤ omegaCentralizer T) : localOmegaModule T K ≠ ⊥ := by
  intro hz
  apply hC
  exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)).trans
    (centralizer_le (le_conjugateSpanBy _ _))

/-- The omega-span is already elementary and lies in the original Sylow. -/
theorem span_elementary_le_sylow (hE : IsEvenCharacteristicAt T)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    IsElementaryAbelian 2
      (conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) K) ∧
      conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) K ≤
        (T : Subgroup G) := by
  let J := K ⊔ (T : Subgroup G)
  let V := conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) K
  have hVJ : V ≤ J := (conjugateSpanBy_mono le_rfl le_sup_left).trans
    (conjugateSpanBy_le_self ((seed_le T).trans (show (T : Subgroup G) ≤ J from le_sup_right)))
  have hv := span_reduced T K hE hK hn
  let := hv.elementary
  refine ⟨?_,?_⟩
  · change IsElementaryAbelian 2 V
    rw [← map_subgroupOf_eq_of_le hVJ]
    exact IsElementaryAbelian.map _
  · have hm := map_mono (f := J.subtype) hv.le_pCore
    rw [map_subgroupOf_eq_of_le hVJ] at hm
    exact hm.trans ((pCoreIn_le_sylow J (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right))

/-- B.2.14 gives the exact source splitting, with its fixed factor in Z(T). -/
theorem span_eq (hE : IsEvenCharacteristicAt T)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) K =
      localOmegaModule T K ⊔
        (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G)) := by
  let J := K ⊔ (T : Subgroup G)
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  let V := conjugateSpanBy Z K
  have he := span_join T K hn
  have hv := span_elementary_le_sylow T K hE hK hn
  let : IsElementaryAbelian 2 V := hv.1
  have hfull : conjugateSpanBy Z J = V := he
  let : IsElementaryAbelian 2 (conjugateSpanBy Z J) := hfull.symm ▸ hv.1
  have hsplit := conjugateSpan_split_of_sylow_fixed
    (Z := Z) (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)) (by
      rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right)]
      exact le_centralizer_iff.mp sylow_le_omegaCentralizer)
  have hm := commutator_conjugateSpan_eq_of_fixed_supplement Z J J K (T : Subgroup G)
    ((seed_le T).trans le_sup_right) le_sup_left le_sup_right J.le_normalizer
    (sup_le K.le_normalizer hn) le_sup_left le_rfl
    (le_centralizer_iff.mp sylow_le_omegaCentralizer)
  rw [hfull] at hsplit hm
  have hf : V ⊓ centralizer (J : Set G) = Z ⊓ centralizer (K : Set G) := by
    apply le_antisymm
    · intro z hz
      refine ⟨?_, centralizer_le (show K ≤ J from le_sup_left) hz.2⟩
      apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
      exact ⟨hv.2 hz.1, elemPow_eq_one_of_isElementaryAbelian z hz.1,
        fun t ht => hz.2 t (mem_sup_right ht)⟩
    · intro z hz
      refine ⟨le_conjugateSpanBy Z K hz.1,?_⟩
      have hzT := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz.1
      have hKc : K ≤ centralizer ({z} : Set G) := by
        intro k hk
        exact mem_centralizer_singleton_iff.mpr (hz.2 k hk)
      have hTc : (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
        intro t ht
        exact mem_centralizer_singleton_iff.mpr (hzT.2.2 t ht)
      intro j hj
      exact mem_centralizer_singleton_iff.mp ((sup_le hKc hTc) hj)
  rw [hm,hf] at hsplit
  exact hsplit

omit [Finite G] in
/-- For this nonzero perfect-actor commutator, irreducibility kills fixed points. -/
theorem fixed_eq_bot_of_irreducible
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hC : ¬ K ≤ omegaCentralizer T)
    (hi : ∀ E : Subgroup G, E ≤ localOmegaModule T K →
      K ≤ normalizer (E : Set G) → E = ⊥ ∨ E = localOmegaModule T K) :
    localOmegaModule T K ⊓ centralizer (K : Set G) = ⊥ := by
  let := Chapter1.mem_L_isPerfect hK
  have hnU : K ≤ normalizer (localOmegaModule T K : Set G) :=
    normalizer_commutator_ge_right _ _
  have hnC : K ≤ normalizer (centralizer (K : Set G) : Set G) :=
    (le_centralizer_iff.mp le_rfl).trans (Subgroup.centralizer_le_normalizer _)
  rcases hi _ inf_le_left ((le_inf hnU hnC).trans inf_normalizer_le_normalizer_inf) with hz | he
  · exact hz
  · exfalso
    have hc : localOmegaModule T K ≤ centralizer (K : Set G) := he ▸ inf_le_right
    exact module_ne_bot T K hC (commutator_eq_bot_of_iterated_eq_bot _ K
      (commutator_eq_bot_iff_le_centralizer.mpr hc))

end LocalOmega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
