module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceQuadratic
public import CFSG.Quasithin.Chapter6.Section01.SourceBasic
public import Theory.Representation.BinaryConjugationSection.PairedAction
public import Theory.GroupTheory.PCoreRestriction

/-!
# Excluding the original one-or-two A₅-module branch of 12.2.19

Write K=O²(H), Q=O₂(H), and S=[V_H,K]. The original model on S provides
K/O₂(K)≃A₅ and hence the quotient-rank bound and movement of V. The second
isomorphism theorem constructs the literal map KQ→A₅, with kernel Q and
its prescribed restriction to K. As Q centralizes V_H, the original S
coordinates extend across KQ with that same map.

Provided V≤KQ, the preceding TI-pair argument gives a quadratic Sylow
four-group on S. One or two copies of the five-point module each contain
the five-point core, which rules this out. The proof thus discharges the
A₅ alternative directly, without a natural SL₂(4)-module premise.

The source containment V≤KQ and the production of the 12.2.7 alternatives
remain with qt-d-12213-hstar-natural, as does the A₇ branch. This result
is the conditional exclusion of case (3i), not the full 12.2.19 theorem.

Source: Aschbacher–Smith, 12.2.7(3i) and 12.2.19, printed pp.797,801–802.
The A₅ module is the binary deleted-permutation module of Chapter6.Source.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08 Representation
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H : Subgroup G}

omit [Finite G] in
private theorem core_join_projection (K Q : Subgroup G)
    (hn : K ≤ normalizer (Q : Set G))
    (hc : Q.subgroupOf K = pCore 2 K)
    {A : Type*} [Group A] (e : (K ⧸ pCore 2 K) ≃* A) :
    ∃ f : (K ⊔ Q : Subgroup G) →* A,
      Function.Surjective f ∧ f.ker = Q.subgroupOf (K ⊔ Q) ∧
      ∀ k : K, f (inclusion le_sup_left k) = e (QuotientGroup.mk' (pCore 2 K) k) := by
  let : (Q.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer hn
  let : (Q.subgroupOf (K ⊔ Q)).Normal := normal_subgroupOf_sup_of_le_normalizer hn
  let c := QuotientGroup.quotientInfEquivProdNormalizerQuotient K Q hn
  let d := (QuotientGroup.quotientMulEquivOfEq hc).trans e
  let E := c.symm.trans d
  let f := E.toMonoidHom.comp (QuotientGroup.mk' (Q.subgroupOf (K ⊔ Q)))
  refine ⟨f,E.surjective.comp (QuotientGroup.mk'_surjective _),?_,?_⟩
  · ext x
    change E (QuotientGroup.mk' (Q.subgroupOf (K ⊔ Q)) x) = 1 ↔ _
    rw [map_eq_one_iff E E.injective]
    exact QuotientGroup.eq_one_iff x
  · intro k
    have he : c (QuotientGroup.mk' (Q.subgroupOf K) k) =
        QuotientGroup.mk' (Q.subgroupOf (K ⊔ Q)) (inclusion le_sup_left k) := rfl
    change d (c.symm _) = _
    rw [← he, c.symm_apply_apply]
    rfl

omit [Finite G] in
private def model_section (K S : Subgroup G) (hSK : S ≤ K)
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W)
    (e : (K ⧸ pCore 2 K) ≃* A) (b : S ≃* Multiplicative W)
    (hb : ∀ (k : K) (s : S),
      ((b.symm (Multiplicative.ofAdd (ρ (e (QuotientGroup.mk' (pCore 2 K) k)) (b s).toAdd))) : G) =
        (k : G) * (s : G) * (k : G)⁻¹) :
    BinaryConjugationSection K S ⊥ (ρ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))) := by
  have hm : Chapter6.Source.IsConjugationModel K S ρ := ⟨e,b,hb⟩
  refine ⟨hSK,bot_le,hm.normalizes,b.toMonoidHom,b.surjective,?_,?_⟩
  · rw [b.toMonoidHom.ker_eq_bot b.injective, bot_subgroupOf]
  · intro k s
    apply Multiplicative.ofAdd.injective
    apply b.symm.injective
    change b.symm (b _) = _
    rw [b.symm_apply_apply]
    exact Subtype.ext (hb k s).symm

omit [Finite G] in
private def extend_section (K Q S : Subgroup G) [IsElementaryAbelian 2 S]
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W)
    (q : K →* A) (C : BinaryConjugationSection K S ⊥ (ρ.comp q))
    (hQS : Q ≤ centralizer (S : Set G))
    (f : (K ⊔ Q : Subgroup G) →* A)
    (hf : ∀ k : K, f (inclusion le_sup_left k) = q k)
    (hker : f.ker = Q.subgroupOf (K ⊔ Q)) :
    BinaryConjugationSection (K ⊔ Q) S ⊥ (ρ.comp f) := by
  have hn : K ⊔ Q ≤ normalizer (S : Set G) :=
    sup_le C.normalized (hQS.trans (Subgroup.centralizer_le_normalizer _))
  refine ⟨C.section_le.trans le_sup_left,bot_le,hn,C.coordinates,C.onto,C.kernel_eq,?_⟩
  intro n s
  exact C.original_action_eq_quotient rfl hn hQS f ρ
    (fun k => by change ρ (f (inclusion le_sup_left k)) = ρ (q k); rw [hf])
    (fun q => by change _ ∈ f.ker; rw [hker]; exact q.property) n s

omit [Finite G] in
private theorem residual_core_intersection :
    (H.pCoreIn 2).subgroupOf ((pResidual 2 H).map H.subtype) =
      pCore 2 ((pResidual 2 H).map H.subtype) := by
  let K := (pResidual 2 H).map H.subtype
  have hKH : K ≤ H := map_subtype_le _
  have hHK : H ≤ normalizer (K : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pResidual 2 H))
  have hHQ : H ≤ normalizer (H.pCoreIn 2 : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hKQ : K.pCoreIn 2 ≤ H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 K) ((pCoreIn_le 2 K).trans hKH)
      (hHK.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
  let : ((H.pCoreIn 2).subgroupOf K).Normal :=
    normal_subgroupOf_of_le_normalizer (hKH.trans hHQ)
  have hle : (H.pCoreIn 2).subgroupOf K ≤ pCore 2 K :=
    le_sSup ⟨inferInstance, (isPGroup_pCoreIn 2 H).comap_subtype⟩
  apply le_antisymm hle
  intro k hk
  exact hKQ (mem_map_of_mem K.subtype hk)

private theorem no_five_model_on_omega_subgroup
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hVN : V ≤ (pResidual 2 H).map H.subtype ⊔ H.pCoreIn 2)
    (S : Subgroup G) (hSω : S ≤ hstarOmegaModule T H)
    (hSK : S ≤ (pResidual 2 H).map H.subtype)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 5)) W)
    (hmodel : Chapter6.Source.IsConjugationModel ((pResidual 2 H).map H.subtype) S ρ)
    (j : BinaryPermutation.core (Fin 5) →ₗ[ZMod 2] W) (hj : Function.Injective j)
    (he : ∀ a v, j (BinaryPermutation.alternatingCoreRepresentation (Fin 5) a v) = ρ a (j v)) :
    False := by
  let K := (pResidual 2 H).map H.subtype
  let Q := H.pCoreIn 2
  let N := K ⊔ Q
  have hKH : K ≤ H := map_subtype_le _
  have hHQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  let := chosen_hstar_omega_elementary h hH
  let : IsElementaryAbelian 2 S := IsElementaryAbelian.of_le hSω
  obtain ⟨e,b,hb⟩ := hmodel
  let eK : pResidual 2 H ≃* K := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let eR := (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)).trans e
  have hm := chosen_movement_of_quotient_rank_at h D structural hnone hTI hH
    (chosen_hstar_quotient_rank_of_residual_identification_at h D structural hTI hH (fun _ => ⟨eR⟩))
  obtain ⟨f,hf,hker,hfk⟩ := core_join_projection K Q (hKH.trans hHQ) residual_core_intersection e
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let C := model_section K S hSK ρ e b hb
  have hQS : Q ≤ centralizer (S : Set G) :=
    (chosen_hstar_core_centralizes_omega h hH).trans (centralizer_le hSω)
  let C' := extend_section K Q S ρ q C hQS f hfk hker
  have hm' : ¬ V.subgroupOf N ≤ f.ker := by
    intro hv
    apply hm
    intro v hv'
    exact hker.le (hv (show (⟨v,hVN hv'⟩ : N) ∈ V.subgroupOf N from hv'))
  exact chosen_hstar_no_five_permutation_summand_at h D structural hTI hH N
    (sup_le hKH (pCoreIn_le 2 H)) hVN f hf hker.le hm' ρ S ⊥
    (hSω.trans (chosen_hstar_omega_le_core h hH)) C' j hj he

/-- The source A₅-module alternative on [V_H,K] is impossible once V lies
in K O₂(H). Both one and two copies use their original conjugation marking;
no natural SL₂(4) recognition or quadratic-action premise is assumed. -/
theorem chosen_hstar_not_one_or_two_five_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hVN : V ≤ (pResidual 2 H).map H.subtype ⊔ H.pCoreIn 2) :
    ¬ Chapter6.Source.IsOneOrTwoA5Modules ((pResidual 2 H).map H.subtype)
      ⁅hstarOmegaModule T H, (pResidual 2 H).map H.subtype⁆ := by
  let K := (pResidual 2 H).map H.subtype
  let S := ⁅hstarOmegaModule T H,K⁆
  have hKH : K ≤ H := map_subtype_le _
  have hHK : H ≤ normalizer (K : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pResidual 2 H))
  have hHω : H ≤ normalizer (hstarOmegaModule T H : Set G) :=
    le_normalizer_conjugateSpanBy _ _
  have hSω : S ≤ hstarOmegaModule T H :=
    le_normalizer_iff_commutator_le_left.mp (hKH.trans hHω)
  have hSK : S ≤ K :=
    le_normalizer_iff_commutator_le_right.mp ((hstarOmegaModule_le hH.1.1.2).trans hHK)
  let E := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  have he : ∀ a v, E (BinaryPermutation.alternatingCoreRepresentation (Fin 5) a v) =
      Chapter6.Source.a5Module a (E v) := fun a v =>
    BinaryPermutation.coreEquivNatural_equivariant (Fin 5) (by decide) a.val v
  rintro (hm | hm)
  · exact no_five_model_on_omega_subgroup h D structural hnone hTI hH hVN S hSω hSK
      _ hm E.toLinearMap E.injective he
  · let j : BinaryPermutation.core (Fin 5) →ₗ[ZMod 2]
        BinaryPermutation.natural (Fin 5) × BinaryPermutation.natural (Fin 5) :=
      (LinearMap.inl (ZMod 2) _ _).comp E.toLinearMap
    have hj : Function.Injective j := fun v w hvw => E.injective (congrArg Prod.fst hvw)
    apply no_five_model_on_omega_subgroup h D structural hnone hTI hH hVN S hSω hSK
      _ hm j hj
    intro a v
    apply Prod.ext
    · exact he a v
    · exact (map_zero (Chapter6.Source.a5Module a)).symm
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
