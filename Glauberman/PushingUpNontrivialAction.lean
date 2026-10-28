module

public import Glauberman.PushingUpPSL2FourOffender
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.PGroup.CharacteristicPairReduction
public import Theory.GroupTheory.Commutator.NormalClosure
public import Theory.GroupTheory.NormalGenerationFixedQuotient

/-!
# Nontrivial fixed-space inequalities in pushing up

For a group of characteristic two, the Sylow center lies in the two-core.
Its central omega subgroup is therefore the Sylow-fixed subgroup of the
core's central omega layer. The source prohibition on characteristic Sylow
subgroups normal in the ambient group excludes equality with the ambient
fixed subgroup.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 2.9, printed p.33,
assertions (1) and (3). The natural-module recognition of Lemma 2.8 is separate.
-/

public section
open Subgroup Theory.GroupTheory
namespace Glauberman
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem omegaCenterIn_normal_of_normal (Q : Subgroup G) [Q.Normal] :
    (omegaCenterIn Q).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [←normalizer_eq_top (H := Q)]
  exact normalizer_le_normalizer_omegaCenterIn Q

/-- Niles 2.9(1), retaining the actual Sylow and core omega subgroup. -/
theorem pushingUp_sylow_fixed_ne_ambient_fixed (S : Sylow 2 G)
    (hS : (S : Subgroup G) ≠ ⊥)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hno : NoCharacteristicNormal (S : Subgroup G)) :
    omegaCenterIn (pCore 2 G) ⊓ centralizer (S : Set G) ≠
      omegaCenterIn (pCore 2 G) ⊓ center G := by
  let Q := pCore 2 G
  have hQS : Q ≤ (S : Subgroup G) := pCore_isPGroup.le_sylow_of_normal S
  have hz : centerIn (S : Subgroup G) ≤ Q :=
    inf_le_right.trans ((centralizer_le hQS).trans hc)
  have he := omegaCenterIn_eq_inf_of_center_le Q (S : Subgroup G) hQS hz
  intro hfix
  let E : Subgroup S := (omega₁ (center S) (p := 2)).map (center S).subtype
  have hEchar : E.Characteristic := by
    let _ : (omega₁ (center S) (p := 2)).Characteristic := omega₁_characteristic _
    exact characteristic_map_subtype_of_characteristic _ _
  have hEnormal : (E.map (S : Subgroup G).subtype).Normal := by
    change (omegaCenterIn (S : Subgroup G)).Normal
    rw [he]
    change (omegaCenterIn (pCore 2 G) ⊓ centralizer (S : Set G)).Normal
    rw [hfix]
    let _ := omegaCenterIn_normal_of_normal Q
    infer_instance
  have hEb := hno E hEchar hEnormal
  have hSne : Nontrivial S := (nontrivial_iff_ne_bot _).mpr hS
  let _ := hSne
  exact omega_center_ne_bot S.isPGroup' hEb

omit [Finite G] in
/-- A subgroup with central action commutators is centralized
by the derived subgroup, by the three-subgroups lemma. -/
theorem derived_centralizes_of_central_action_commutators (V : Subgroup G)
    (hcomm : ⁅V, (⊤ : Subgroup G)⁆ ≤ center G) :
    V ≤ centralizer (_root_.commutator G : Set G) := by
  have hh : ⁅⁅V, (⊤ : Subgroup G)⁆, (⊤ : Subgroup G)⁆ = ⊥ :=
    commutator_top_right_eq_bot_iff_le_center.mpr hcomm
  have hd : ⁅⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆, V⁆ = ⊥ := by
    apply commutator_commutator_eq_bot_of_rotate
    · simpa only [commutator_comm (⊤ : Subgroup G) V] using hh
    · exact hh
  rw [commutator_comm] at hd
  exact commutator_eq_bot_iff_le_centralizer.mp hd

omit [Finite G] in
/-- Normal generation modulo a centralizing core makes a quadratic actor
have strictly more fixed points than the ambient group. -/
theorem quadratic_fixed_ne_of_normal_generation (S Q V A : Subgroup G)
    [V.Normal] (hNQ : normalClosure (A : Set G) ⊔ Q = ⊤)
    (hDQ : _root_.commutator G ⊔ Q = ⊤)
    (hVQ : V ≤ centralizer (Q : Set G))
    (hquad : ⁅⁅V,A⁆,A⁆ = ⊥)
    (hSfix : V ⊓ centralizer (S : Set G) ≠ V ⊓ center G) :
    V ⊓ centralizer (A : Set G) ≠ V ⊓ center G := by
  intro he
  let Z := V ⊓ center G
  have hVA : ⁅V,A⁆ ≤ Z := by
    change ⁅V,A⁆ ≤ V ⊓ center G
    rw [←he]
    exact le_inf (commutator_le_left _ _)
      (commutator_eq_bot_iff_le_centralizer.mp hquad)
  have hQV : ⁅Q,V⁆ ≤ Z := by
    rw [commutator_comm]
    exact (commutator_eq_bot_iff_le_centralizer.mpr hVQ).le.trans bot_le
  have hTV : ⁅(⊤ : Subgroup G),V⁆ ≤ Z :=
    commutator_le_of_normal_generation A Q V V Z (normalClosure_eq_self V).symm
      hNQ (by rwa [commutator_comm]) hQV
  have hVD : V ≤ centralizer (_root_.commutator G : Set G) :=
    derived_centralizes_of_central_action_commutators V
      ((commutator_comm V ⊤).trans_le (hTV.trans inf_le_right))
  have hcentral : V ≤ center G := by
    apply centralizer_eq_top_iff_subset.mp
    apply top_unique
    rw [←hDQ]
    exact sup_le (le_centralizer_iff.mp hVD) (le_centralizer_iff.mp hVQ)
  apply hSfix
  rw [inf_eq_left.mpr (hcentral.trans (center_le_centralizer _)),
    inf_eq_left.mpr hcentral]

variable {F : Type*} [Field F] [Finite F]

/-- Both fixed-space inequalities for an actual offender from the original
PSL₂(4) quotient, without assuming a natural-module recognition. -/
theorem original_psl2_four_offender_fixed_ne
    (hF : Nat.card F = 4) (S : Sylow 2 G)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup G) ⊤)
    (K : Subgroup G) [K.Normal]
    (e : (G ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting G = pCore 2 G)
    (hno : NoCharacteristicNormal (S : Subgroup G))
    (A : Subgroup G) (hAS : A ≤ (S : Subgroup G)) (hAK : ¬ A ≤ K)
    (hquad : ⁅⁅omegaCenterIn (pCore 2 G),A⁆,A⁆ = ⊥) :
    omegaCenterIn (pCore 2 G) ⊓ centralizer (S : Set G) ≠
        omegaCenterIn (pCore 2 G) ⊓ center G ∧
    omegaCenterIn (pCore 2 G) ⊓ centralizer (A : Set G) ≠
        omegaCenterIn (pCore 2 G) ⊓ center G := by
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let b := e.trans a
  let f := b.toMonoidHom.comp (QuotientGroup.mk' K)
  have hfs : Function.Surjective f := b.surjective.comp (QuotientGroup.mk'_surjective K)
  have hker : f.ker = K := by
    ext x
    change b (QuotientGroup.mk' K x) = 1 ↔ x ∈ K
    rw [←b.map_one, b.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  let _ : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let N := normalClosure (A : Set G)
  have hNmap : N.map f = ⊤ := by
    have hn : (N.map f).Normal := (inferInstance : N.Normal).map f hfs
    apply hn.eq_bot_or_eq_top.resolve_left
    intro he
    apply hAK
    rw [←hker]
    exact le_normalClosure.trans ((map_eq_bot_iff N).mp he)
  have hNK : N ⊔ K = ⊤ := by
    have hh := congrArg (Subgroup.comap f) hNmap
    simpa only [comap_map_eq,hker,comap_top] using hh
  have hDmap : (_root_.commutator G).map f = ⊤ := by
    change Subgroup.map f ⁅(⊤ : Subgroup G),(⊤ : Subgroup G)⁆ = ⊤
    rw [map_commutator,map_top_of_surjective f hfs]
    exact commutator_alternatingGroup_eq_top (by simp)
  have hDK : _root_.commutator G ⊔ K = ⊤ := by
    have hh := congrArg (Subgroup.comap f) hDmap
    simpa only [comap_map_eq,hker,comap_top] using hh
  have hreduce := (Theory.SpecificGroups.SL2.original_kernel_reduction_of_psl2_four
    hF S hu K e).2.2.2.2
  have hNQ := hreduce N hNK
  have hDQ := hreduce (_root_.commutator G) hDK
  have hSne : (S : Subgroup G) ≠ ⊥ := by
    intro he
    exact hAK ((hAS.trans_eq he).trans bot_le)
  have hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G := by
    rw [←hf]
    exact centralizer_generalizedFitting_le G
  have hfirst := pushingUp_sylow_fixed_ne_ambient_fixed S hSne hc hno
  let _ := omegaCenterIn_normal_of_normal (pCore 2 G)
  refine ⟨hfirst,quadratic_fixed_ne_of_normal_generation _ (pCore 2 G) _ A
    hNQ hDQ ?_ hquad hfirst⟩
  exact fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1

/-- The complete offender input from Niles 2.9 for the actual PSL₂(4)
quotient: selection, quadraticity, both nontrivial fixed-space clauses,
and the numerical bound, all under the original hypotheses. -/
theorem original_psl2_four_nontrivial_quadratic_offender
    (hF : Nat.card F = 4) (S : Sylow 2 G)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup G) ⊤)
    (K : Subgroup G) [K.Normal]
    (e : (G ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting G = pCore 2 G)
    (hno : NoCharacteristicNormal (S : Subgroup G)) :
    ∃ A : Subgroup G, A ∈ thompsonAbelianSubgroups (S : Subgroup G) ∧
      ¬ A ≤ K ∧
      ⁅⁅omegaCenterIn (pCore 2 G),A⁆,A⁆ = ⊥ ∧
      (omegaCenterIn (pCore 2 G) ⊓ centralizer (S : Set G) ≠
        omegaCenterIn (pCore 2 G) ⊓ center G) ∧
      (omegaCenterIn (pCore 2 G) ⊓ centralizer (A : Set G) ≠
        omegaCenterIn (pCore 2 G) ⊓ center G) ∧
      (omegaCenterIn (pCore 2 G) ⊓ centralizer (A : Set G)).relIndex
        (omegaCenterIn (pCore 2 G)) ≤
          Nat.card (A.map (QuotientGroup.mk' (pCore 2 G))) ∧
      Nat.card (A.map (QuotientGroup.mk' (pCore 2 G))) =
        Nat.card (A.map (QuotientGroup.mk' K)) ∧
      Nat.card (A.map (QuotientGroup.mk' K)) ≤ 4 := by
  obtain ⟨A,hA,hAK,hquad,hbound,hcard,hsmall⟩ :=
    original_psl2_four_quadratic_offender hF S hu K e hno
  obtain ⟨hfirst,hsecond⟩ :=
    original_psl2_four_offender_fixed_ne hF S hu K e hf hno A hA.1 hAK hquad
  exact ⟨A,hA,hAK,hquad,hfirst,hsecond,hbound,hcard,hsmall⟩

end Glauberman
