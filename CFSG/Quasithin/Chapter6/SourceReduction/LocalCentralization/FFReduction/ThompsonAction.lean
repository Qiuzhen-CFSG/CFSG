module
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction.ExceptionalModelsSource
public import CFSG.Quasithin.Chapter5.RankOneBaumannSource
public import Theory.GroupTheory.ElementaryThompsonQuasisimpleCore
public import CFSG.Quasithin.ChapterB.QuasisimpleOffenderModels
/-!
# Thompson movement and the genuine FF action in the local Cartan argument

The reduced omega-span commutator detects the full two-core of KT. If J(T)
centralized it, Baumann heredity would make Baum(T) normal in KT, contrary
to the source escape. A normal J(T) would lie in O₂(KT), so the quasisimple
core commutator theorem gives K=[K,J(T)]. The literal centralizer quotient
therefore supports the genuine FF action and complete B.5.1 conclusion.

Source: Aschbacher--Smith 5.1.13, p.637, using B.2.7 and B.5.1.
The independent Baumann input is qt-d-1222-rankone-baumann-control-source.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- Each original exceptional quotient is simple; no covering center is removed. -/
theorem LocalExceptionalQuotient.simple {K : Subgroup G}
    (h : LocalExceptionalQuotient K) : IsSimpleGroup (K ⧸ pCore 2 K) := by
  rcases h with h | h | h
  · let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact h.some.isSimpleGroup
  · exact ChapterA.Section03.SourceEmbeddings.Exceptional.IsModel.isSimple (Or.inl h)
  · exact ChapterA.Section03.SourceEmbeddings.Exceptional.IsModel.isSimple (Or.inr (Or.inl h))

namespace LocalOmega
variable {T : Sylow 2 G} {K : Subgroup G}

omit [Finite G] in
/-- The ambient reduced-family assertion restricts to the literal Sylow join. -/
theorem reduced_internal (hU : localOmegaModule T K ∈ reducedFamily (K ⊔ (T : Subgroup G))) :
    IsPReduced 2 ((localOmegaModule T K).subgroupOf (K ⊔ (T : Subgroup G))) := by
  let := hU.2.1
  exact ⟨hU.2.2.choose, IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hU.1).toMonoidHom (subgroupOfEquivOfLe hU.1).injective,
    hU.2.2.choose_spec⟩

omit [Finite G] in
/-- The literal exceptional quotient has trivial center. -/
theorem quotient_center (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hm : LocalExceptionalQuotient K) : center (K ⧸ pCore 2 K) = ⊥ := by
  let := Chapter1.mem_L_isPerfect hK
  let : Group.IsPerfect (K ⧸ pCore 2 K) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (pCore 2 K)) (QuotientGroup.mk'_surjective _)
  let := hm.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (K ⧸ pCore 2 K)) inferInstance with hb | ht
  · exact hb
  · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp ht)).elim

omit [Finite G] in
/-- The original two-core quotient is quasisimple. -/
theorem quotient_quasisimple (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hm : LocalExceptionalQuotient K) : IsQuasisimple (K ⧸ pCore 2 K) := by
  let := Chapter1.mem_L_isPerfect hK
  let := hm.simple
  exact { toIsPerfect := Group.IsPerfect.ofSurjective
            (f := QuotientGroup.mk' (pCore 2 K)) (QuotientGroup.mk'_surjective _)
          simple := ((QuotientGroup.quotientMulEquivOfEq (quotient_center hK hm)).trans
            QuotientGroup.quotientBot).isSimpleGroup }

/-- The actual omega commutator is moved by the original Thompson subgroup. -/
theorem thompson_moves (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : LocalExceptionalQuotient K)
    (hU : localOmegaModule T K ∈ reducedFamily (K ⊔ (T : Subgroup G)))
    (hne : localOmegaModule T K ≠ ⊥)
    (hout : ¬ K ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G)) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localOmegaModule T K : Set G) := by
  intro hj
  let M := K ⊔ (T : Subgroup G)
  let U := localOmegaModule T K
  let := Chapter1.mem_L_isPerfect hK
  let := quotient_quasisimple hK hm
  let := hU.2.1
  have hr := reduced_internal hU
  have hmove : ⁅U,K⁆ ≠ ⊥ := fun hz => hne (commutator_eq_bot_of_iterated_eq_bot _ K hz)
  have hUT : U ≤ (T : Subgroup G) :=
    (reduced_le_core hU).trans ((pCoreIn_le_sylow M (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right))
  have he : ChapterB.baumann (T : Subgroup G) = ChapterB.baumann (M.pCoreIn 2) := by
    rw [ChapterB.lemma_B_2_3_5 (T : Subgroup G) U hUT hj,
      Chapter5.RankOneBaumannSource.reduced_sylow_centralizer hn hU.1 hr
        (quotient_center hK hm) hmove]
  apply hout
  rw [he]
  exact (show K ≤ M from le_sup_left).trans
    ((M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))).trans
      (normalizer_le_normalizer_baumann _))

/-- The whole original maximal component is its Thompson commutator. -/
theorem thompson_commutator (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : LocalExceptionalQuotient K)
    (hU : localOmegaModule T K ∈ reducedFamily (K ⊔ (T : Subgroup G)))
    (hne : localOmegaModule T K ≠ ⊥)
    (hout : ¬ K ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G)) :
    ⁅K, elementaryAbelianMaxJ (T : Subgroup G)⁆ = K := by
  let M := K ⊔ (T : Subgroup G)
  let B := K.subgroupOf M
  let U := (localOmegaModule T K).subgroupOf M
  let S := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  let J := elementaryAbelianMaxJ (S : Subgroup M)
  let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hn)
  have hr : IsPReduced 2 U := reduced_internal hU
  let := hr.normal
  let := hr.elementary
  have hB : B.IsCComponent := hK.1
  let e : B ≃* K := subgroupOfEquivOfLe le_sup_left
  let eqv := QuotientGroup.congr (pCore 2 B) (pCore 2 K) e (pCore_map_iso 2 e)
  let := quotient_quasisimple hK hm
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv eqv.symm
  have hgen : B ⊔ (S : Subgroup M) = ⊤ := by
    change K.subgroupOf M ⊔ (T : Subgroup G).subgroupOf M = ⊤
    rw [← subgroupOf_sup (show K ≤ M from le_sup_left) le_sup_right, subgroupOf_self]
  have hjmap : J.map M.subtype = elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective]
    congr 1
    exact map_subgroupOf_eq_of_le le_sup_right
  have hj : ¬ J ≤ centralizer (U : Set M) := by
    intro hc
    apply thompson_moves hK hn hm hU hne hout
    rw [← hjmap]
    rintro _ ⟨x,hx,rfl⟩ y hy
    exact congrArg M.subtype (hc hx ⟨y,hU.1 hy⟩ hy)
  have hnot : ¬ B ≤ normalizer (J : Set M) := by
    intro hb
    let : J.Normal := normalizer_eq_top_iff.mp (top_unique (by
      rw [←hgen]
      exact sup_le hb ((S : Subgroup M).le_normalizer.trans
        (normalizer_le_normalizer_elementaryAbelianMaxJ _))))
    have hp : IsPGroup 2 J := S.isPGroup'.to_le (sSup_le fun _ hA => hA.1)
    exact hj ((show J ≤ pCore 2 M from le_sSup ⟨inferInstance,hp⟩).trans
      (le_centralizer_iff.mp hr.le_centralizer_pCore))
  have hh := congrArg (map M.subtype)
    (eq_commutator_maxJ_of_quasisimple_core_of_not_normalizes S B hB hgen hnot)
  rw [map_commutator,hjmap,map_subgroupOf_eq_of_le (show K ≤ M from le_sup_left)] at hh
  exact hh.symm

open ChapterB.InternalThompsonAction Representation Representation.BinaryOffender
open scoped IsMulCommutative

/-- The actual FF action and complete B.5.1 output on its original quotient. -/
def ClassifiedAction
    (hU : localOmegaModule T K ∈ reducedFamily (K ⊔ (T : Subgroup G))) : Prop :=
    let M := K ⊔ (T : Subgroup G)
    let U := (localOmegaModule T K).subgroupOf M
    letI := (reduced_internal hU).normal
    letI := (reduced_internal hU).elementary
    IsFFModule (action U) ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((action U).comp (offenderSubgroup (action U)).subtype)
        (((K.subgroupOf M).map (actionMk U)).subgroupOf (offenderSubgroup (action U))))

/-- The genuine B.5.1 classification of the original omega commutator action.
The component is mapped by the literal centralizer quotient and restricted
only to its actual best-offender subgroup. -/
theorem source_classification
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : LocalExceptionalQuotient K)
    (hU : localOmegaModule T K ∈ reducedFamily (K ⊔ (T : Subgroup G)))
    (hne : localOmegaModule T K ≠ ⊥)
    (hout : ¬ K ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G)) :
    ClassifiedAction hU := by
  let M := K ⊔ (T : Subgroup G)
  let U := (localOmegaModule T K).subgroupOf M
  let B := K.subgroupOf M
  let S := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  have hr : IsPReduced 2 U := reduced_internal hU
  let := hr.normal
  let := hr.elementary
  let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hn)
  have hgen : B ⊔ (S : Subgroup M) = ⊤ := by
    change K.subgroupOf M ⊔ (T : Subgroup G).subgroupOf M = ⊤
    rw [← subgroupOf_sup (show K ≤ M from le_sup_left) le_sup_right, subgroupOf_self]
  have hSm : (S : Subgroup M).map M.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hjmap : (elementaryAbelianMaxJ (S : Subgroup M)).map M.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective, hSm]
  have hj : ¬ elementaryAbelianMaxJ (S : Subgroup M) ≤ centralizer (U : Set M) := by
    intro hc
    apply thompson_moves hK hn hm hU hne hout
    rw [← hjmap]
    rintro _ ⟨x,hx,rfl⟩ y hy
    exact congrArg M.subtype (hc hx ⟨y,hU.1 hy⟩ hy)
  have hsq : IsSQTK KnownSimple.IsKnownSimple M := by
    let R := M.pCoreIn 2
    let N := normalizer (R : Set G)
    have hMN : M ≤ N := M.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
    have hN : IsTwoLocal N := ⟨R,hK.2.2,isPGroup_pCoreIn 2 M,rfl⟩
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hMN)).mp
      ((hG.twoLocal_sqtk hN).subgroup (M.subgroupOf N))
  exact ⟨isFFModule_of_thompson_movement S U hj,
    quasisimple_source_conclusion_of_thompson_movement hsq S B U hK.1 hgen
      hr.quotient_pCore_eq_bot hj⟩

end LocalOmega

/-- Actual Cartan consumer of the Thompson and FF argument: the original
maximal local witness now has its full Thompson commutator and actual B.5.1
action, with only the independently owned Baumann premise retained. -/
theorem localCartan_maximal_thompson_source
    (hbaum : RankOneBaumannNormalizerControl G)
    {T : Sylow 2 G} {L W H A Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hXC : ¬ X ≤ omegaCentralizer T) :
    ∃ K : Subgroup G, X ≤ K ∧ K ∈ Chapter1.LStar G (T : Subgroup G) ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧ LocalExceptionalQuotient K ∧
      ¬ K ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ∧
      ⁅K, elementaryAbelianMaxJ (T : Subgroup G)⁆ = K ∧
      ∃ hU : localOmegaModule T K ∈ reducedFamily (K ⊔ (T : Subgroup G)),
      localOmegaModule T K ≠ ⊥ ∧
      conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K =
        localOmegaModule T K ⊔ (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G)) ∧
      LocalOmega.ClassifiedAction hU := by
  obtain ⟨K,hXK,hK,hn,hm,hout,hU,hne,hspan⟩ := localCartan_maximal_models_source hbaum h hH hY d hXC
  exact ⟨K,hXK,hK,hn,hm,hout,LocalOmega.thompson_commutator hK.1 hn hm hU hne hout,
    hU,hne,hspan,LocalOmega.source_classification h.qtke hK.1 hn hm hU hne hout⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
