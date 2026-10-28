module
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction.ThompsonAction
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction.ExceptionalActions
public import Theory.GroupTheory.ReducedNormal.QuasisimpleImage
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.Representation.NormalElementaryQuotient.SubgroupSpace
public import Theory.Representation.BinaryOffender.MovedDimension
/-!
# The genuine FF action on the original omega commutator

The kernel of the local component on a reduced noncentral module is its
full two-core. Its literal image in the offender actor therefore retains
that quotient, and the component's perfectness gives full movement. The
exceptional FF alternatives now yield A7 and the original irreducible
subgroup of order 16 or 64, without a constituent or action callback.
Source: Aschbacher--Smith 5.1.13, printed p.637.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open ChapterB.InternalThompsonAction

private theorem center_trivial_transfer {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center B = ⊥) : center A = ⊥ := by
  apply bot_unique
  intro a ha
  apply e.injective
  have hh : e a ∈ center B := MulEquivClass.apply_mem_center e ha
  simpa only [hz,mem_bot,map_one] using hh

private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hN hp
  let : N.Normal := hN
  by_contra hne
  let : Nontrivial (A ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (A ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (A ⧸ N) := hp.isNilpotent
  exact Group.IsPerfect.not_isSolvable (A ⧸ N) inferInstance

private theorem invariant_subgroup_of_irreducible
    {H Q D : Type*} [Group H] [Group Q] [Group D]
    (U B : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (q : H →* Q) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set H))
    (f : D →* Q) (himage : ∀ d, f d ∈ B.map q)
    (hi : IsIrreducible ((NormalElementaryQuotient.representation U q hq hk).comp f))
    (E : Subgroup H) (hEU : E ≤ U) (hBE : B ≤ normalizer (E : Set H)) :
    E = ⊥ ∨ E = U := by
  let ρ := NormalElementaryQuotient.representation U q hq hk
  let s : Subrepresentation (ρ.comp f) := {
    toSubmodule := NormalElementaryQuotient.subgroupSpace U E
    apply_mem_toSubmodule := by
      intro d v hv
      obtain ⟨b,hb,he⟩ := himage d
      change ((ρ (f d) v).toMul : H) ∈ E
      rw [←he,NormalElementaryQuotient.representation_apply]
      exact (hBE hb v.toMul).mp hv }
  let := hi
  rcases eq_bot_or_eq_top s with hs | hs
  · left
    apply bot_unique
    intro e he
    have hh : Additive.ofMul (⟨e,hEU he⟩ : U) ∈ s := he
    rw [hs] at hh
    exact congrArg (fun v : Additive U => (v.toMul : H)) (show _ = 0 from hh)
  · right
    apply le_antisymm hEU
    intro u hu
    have hh : Additive.ofMul (⟨u,hu⟩ : U) ∈ s := hs.ge (by trivial)
    exact hh

private theorem reduced_classified_action
    {H : Type*} [Group H] [Finite H] (P : Sylow 2 H) (B U : Subgroup H)
    [B.Normal] [U.Normal] [IsElementaryAbelian 2 U]
    [IsQuasisimple (B ⧸ pCore 2 B)]
    (hr : IsPReduced 2 U) (hz : center (B ⧸ pCore 2 B) = ⊥)
    (ho : ExceptionalActions.ExceptionalOrder (B ⧸ pCore 2 B))
    (hne : U ≠ ⊥) (hm : ⁅U,B⁆ = U)
    (hth : ⁅B,elementaryAbelianMaxJ (P : Subgroup H)⁆ = B)
    (hc : Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((action U).comp (offenderSubgroup (action U)).subtype)
      ((B.map (actionMk U)).subgroupOf (offenderSubgroup (action U))))) :
    Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)) ∧
      (Nat.card U = 2^4 ∨ Nat.card U = 2^6) ∧
      (∀ E : Subgroup H, E ≤ U → B ≤ normalizer (E : Set H) → E = ⊥ ∨ E = U) := by
  let q := actionMk U
  let C := B.map q
  let N := offenderSubgroup (action U)
  let D := C.subgroupOf N
  let : N.Normal := offenderSubgroup_normal _
  have hCN : C ≤ N := by
    change B.map q ≤ N
    rw [←hth,map_commutator]
    exact (commutator_mono le_rfl (thompson_image_le P U)).trans (commutator_le_right _ _)
  let e := (reducedQuasisimpleImageEquiv U B hr hz (by rwa [hm])).trans
    (subgroupOfEquivOfLe hCN).symm
  have horder : ExceptionalActions.ExceptionalOrder D := by
    unfold ExceptionalActions.ExceptionalOrder at ho ⊢
    rwa [←Nat.card_congr e.toEquiv]
  have hcenter : center D = ⊥ := center_trivial_transfer e.symm hz
  have hmove : ChapterB.QuasisimpleSource.moved ((action U).comp N.subtype) D = ⊤ := by
    change subspaceCommutator ((action U).comp N.subtype) ⊤ D = ⊤
    rw [Representation.BinaryOffender.subspaceCommutator_comp_map,
      map_subgroupOf_eq_of_le hCN]
    change subspaceCommutator (NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ⊤ (B.map q) = ⊤
    rw [←NormalElementaryQuotient.commutatorSpace_eq U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) B]
    apply top_unique
    intro v _
    change (v.toMul : H) ∈ ⁅U,B⁆
    rw [hm]
    exact v.toMul.property
  obtain ⟨c⟩ := hc
  obtain ⟨he,hi,_,hcard⟩ := ExceptionalActions.fully_moved_source _ c horder hcenter hmove
  refine ⟨⟨e.trans he.some⟩,hcard,?_⟩
  intro E hEU hBE
  exact invariant_subgroup_of_irreducible U B q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) (N.subtype.comp D.subtype) (fun d => d.property) hi E hEU hBE

namespace LocalOmega
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {K : Subgroup G}

/-- The literal omega commutator is fully moved by the original component. -/
theorem full_movement (hE : IsEvenCharacteristicAt T)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    ⁅localOmegaModule T K,K⁆ = localOmegaModule T K := by
  let := Chapter1.mem_L_isPerfect hK
  have hv := span_elementary_le_sylow T K hE hK hn
  let := hv.1
  simpa only [localOmegaModule] using (commutator_isPPerfect_idempotent K
    (conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) K)
    perfect_twoPerfect (IsElementaryAbelian.isPGroup 2 _) (le_normalizer_conjugateSpanBy _ _))

omit [Finite G] in
/-- The actual exceptional quotient has one of the three native orders. -/
theorem exceptional_order (hm : LocalExceptionalQuotient K) :
    ExceptionalActions.ExceptionalOrder (K ⧸ pCore 2 K) := by
  unfold ExceptionalActions.ExceptionalOrder
  rcases hm with h | h | h
  all_goals obtain ⟨e⟩ := h
  · left
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  · exact Or.inr (Or.inl ((Nat.card_congr e.toEquiv).trans
      Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier))
  · exact Or.inr (Or.inr ((Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.m23_order))

/-- B.5.1 on the literal omega module gives the A7 quotient, actual orders
16 or 64, and irreducibility stated on its original invariant subgroups. -/
theorem action_consequences (hE : IsEvenCharacteristicAt T)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : LocalExceptionalQuotient K)
    (hU : localOmegaModule T K ∈ reducedFamily (K ⊔ (T : Subgroup G)))
    (hne : localOmegaModule T K ≠ ⊥)
    (hth : ⁅K,elementaryAbelianMaxJ (T : Subgroup G)⁆ = K)
    (ha : ClassifiedAction hU) :
    Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) ∧
      (Nat.card (localOmegaModule T K) = 2^4 ∨ Nat.card (localOmegaModule T K) = 2^6) ∧
      (∀ E : Subgroup G, E ≤ localOmegaModule T K → K ≤ normalizer (E : Set G) →
        E = ⊥ ∨ E = localOmegaModule T K) := by
  let M := K ⊔ (T : Subgroup G)
  let B := K.subgroupOf M
  let U := (localOmegaModule T K).subgroupOf M
  let P := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  have hr : IsPReduced 2 U := reduced_internal hU
  let := hr.normal
  let := hr.elementary
  let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hn)
  let e := QuotientGroup.congr (pCore 2 B) (pCore 2 K)
    (subgroupOfEquivOfLe (show K ≤ M from le_sup_left))
    (pCore_map_iso 2 (subgroupOfEquivOfLe (show K ≤ M from le_sup_left)))
  let := quotient_quasisimple hK hm
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv e.symm
  have hz := center_trivial_transfer e (quotient_center hK hm)
  have ho : ExceptionalActions.ExceptionalOrder (B ⧸ pCore 2 B) := by
    unfold ExceptionalActions.ExceptionalOrder
    rw [Nat.card_congr e.toEquiv]
    exact exceptional_order hm
  have hnon : U ≠ ⊥ := by
    intro he
    apply hne
    apply bot_unique
    intro x hx
    have hh : (⟨x,hU.1 hx⟩ : M) ∈ U := hx
    exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp (he.le hh)))
  have hmove : ⁅U,B⁆ = U := by
    apply map_injective M.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hU.1,
      map_subgroupOf_eq_of_le (show K ≤ M from le_sup_left),full_movement hE hK hn]
  have hPmap : (P : Subgroup M).map M.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hth' : ⁅B,elementaryAbelianMaxJ (P : Subgroup M)⁆ = B := by
    apply map_injective M.subtype_injective
    rw [map_commutator,←elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective,
      hPmap,
      map_subgroupOf_eq_of_le (show K ≤ M from le_sup_left),hth]
  obtain ⟨he,hcard,hi⟩ := reduced_classified_action P B U hr hz ho hnon hmove hth' ha.2
  refine ⟨⟨e.symm.trans he.some⟩,?_,?_⟩
  · rwa [Nat.card_congr (subgroupOfEquivOfLe hU.1).toEquiv] at hcard
  · intro E hEU hKE
    have hEM := hEU.trans hU.1
    have hn' : B ≤ normalizer (E.subgroupOf M : Set M) := by
      intro b hb
      apply mem_normalizer_iff.mpr
      intro x
      exact mem_normalizer_iff.mp (hKE hb) (x : G)
    rcases hi (E.subgroupOf M) (comap_mono hEU) hn' with hb | he
    · left
      apply bot_unique
      intro x hx
      have hh : (⟨x,hEM hx⟩ : M) ∈ E.subgroupOf M := hx
      exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp (hb.le hh)))
    · right
      apply le_antisymm hEU
      intro x hx
      exact he.ge (show (⟨x,hU.1 hx⟩ : M) ∈ U from hx)
end LocalOmega
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original Cartan witness now yields the actual A7 quotient and
irreducible omega commutator, including its literal fixed-space splitting.
Only the independently produced original Baumann premise remains. -/
theorem localCartan_maximal_omega_action_source
    (hbaum : RankOneBaumannNormalizerControl G)
    {T : Sylow 2 G} {L W H A Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hXC : ¬ X ≤ omegaCentralizer T) :
    ∃ K : Subgroup G, X ≤ K ∧ K ∈ Chapter1.LStar G (T : Subgroup G) ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) ∧
      ⁅K,elementaryAbelianMaxJ (T : Subgroup G)⁆ = K ∧
      localOmegaModule T K ∈ reducedFamily (K ⊔ (T : Subgroup G)) ∧
      (Nat.card (localOmegaModule T K) = 2^4 ∨ Nat.card (localOmegaModule T K) = 2^6) ∧
      (∀ E : Subgroup G, E ≤ localOmegaModule T K → K ≤ normalizer (E : Set G) →
        E = ⊥ ∨ E = localOmegaModule T K) ∧
      conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K =
        localOmegaModule T K ⊔ (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G)) ∧
      localOmegaModule T K ⊓ centralizer (K : Set G) = ⊥ := by
  obtain ⟨K,hXK,hK,hn,hm,_,hth,hU,hne,hspan,ha⟩ :=
    localCartan_maximal_thompson_source hbaum h hH hY d hXC
  obtain ⟨he,hcard,hi⟩ := LocalOmega.action_consequences
    (h.qtke.evenCharacteristic T) hK.1 hn hm hU hne hth ha
  exact ⟨K,hXK,hK,hn,he,hth,hU,hcard,hi,hspan,
    LocalOmega.fixed_eq_bot_of_irreducible T K hK.1 (fun hc => hXC (hXK.trans hc)) hi⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
