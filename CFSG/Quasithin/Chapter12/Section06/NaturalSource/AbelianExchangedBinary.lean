module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianLieSieve
public import Theory.SpecificGroups.PSL3Two.Parabolics.ExchangedSolvableOvergroup
public import Theory.GroupTheory.WreathTwoThreeCore

/-!
# Excluding the exchanged binary linear-three row on the original actor

The literal K-star is an ordinary component of H/O₂(H). Its index-two
normalizer gives the actual exchanged pair. The original E₉ quotient of
L₁, its two-perfectness and the ambient three-rank bound put L₁-star in
the pair. The solvable L₁T image contains a full cubic plane, so the native
square-parabolic calculation identifies H/O₂(H) with SL₃(2) wr C₂.

The two parabolic wreaths lift through the same O₂(H) to solvable
overgroups of the original T. By 12.6.29 both lie in M, and they generate
H. This contradicts H in Hz. The final application eliminates this row
from the reduced actor J=K₀L₁T, retaining K/O₂(K), K-star and relative
C-component status in both H and J.

Earlier geometry remains explicit. The remaining field restrictions,
subgroup and module identifications, SL₃(4) and wreath exclusions, and
universal NaturalReduction still belong to the source assembly.
Source: Aschbacher--Smith 12.6.30--31, printed pp.835--836; the native
PSL₃(2) parabolic calculations replace the generation-one step for this row.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06

open Chapter13.Section08.Components
open Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The actual exchanged binary-three row has the full inner wreath quotient.
The original E₉ in L₁T excludes graph automorphisms on its two components. -/
theorem SourceHypothesis.original_abelian_exchanged_binary_wreath
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 2) :
    Nonempty ((H ⧸ pCore 2 H) ≃* Matrix.PSL3Two.WreathPair.Actor) := by
  let E := D.fullSetup hZ T z
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hLH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  let P := (T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  let C := actorImage H K
  let A := actorImage H E.L₁
  have hcomp := (S.original_abelian_component_span_actors D hZ z hz hTV hTz hbound hTI hns
    hH hKH hK hgen).1
  obtain ⟨F,hF,hfin,hcard,⟨e₀⟩⟩ := hm
  let := hF
  let := hfin
  let := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hcard)
  let e : C ≃* Matrix.PSL3Two.SL := (componentStarEquiv H K hKH hK).symm.trans
    (e₀.trans ((Atlas.fieldEquivPSL 3 eF).trans Matrix.PSL3Two.equiv.symm))
  have hi := (S.original_abelian_nonnormal_component_models D hZ z hz hTV hTz hbound hTI hns
    hH hKH hK hgen hn).1
  have hTL : (T : Subgroup G) ≤ normalizer (E.L₁ : Set G) :=
    (le_inf hTH hTV).trans
      (S.original_module_normalizer_normalizes_residual D hZ z hTV hH)
  have hPA : (P : Subgroup (H ⧸ pCore 2 H)) ≤ normalizer (A : Set (H ⧸ pCore 2 H)) :=
    Chapter13.Section08.Components.Suzuki.BorelSource.starImage_normalizes H E.L₁ T hTL
  have hOH : conjugateSpanBy K (T : Subgroup G) ≤ H :=
    conjugateSpanBy_le hKH (hTH.trans H.le_normalizer)
  have ho : actorImage H (conjugateSpanBy K (T : Subgroup G)) =
      componentOrbit C (P : Subgroup (H ⧸ pCore 2 H)) := by
    have he : actorImage H (conjugateSpanBy K (T : Subgroup G)) =
        conjugateSpanBy C (P : Subgroup (H ⧸ pCore 2 H)) :=
      star_conjugateSpan H K T hKH hTH
    exact he.trans (conjugateSpanBy_eq_iSup_conj C P)
  have hg : componentOrbit C (P : Subgroup (H ⧸ pCore 2 H)) ⊔ A ⊔
      (P : Subgroup (H ⧸ pCore 2 H)) = ⊤ := by
    rw [←ho]
    change actorImage H (conjugateSpanBy K (T : Subgroup G)) ⊔ actorImage H E.L₁ ⊔
      actorImage H T = ⊤
    unfold actorImage
    rw [←Subgroup.map_sup,←Subgroup.map_sup,←subgroupOf_sup hOH hLH,
      ←subgroupOf_sup (sup_le hOH hLH) hTH,hgen,subgroupOf_self,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let R : Sylow 3 E.L₁ := Classical.choice inferInstance
  let R₀ := (R : Subgroup E.L₁).map E.L₁.subtype
  have h9 : 9 ∣ Nat.card (A ⊔ (P : Subgroup (H ⧸ pCore 2 H)) : Subgroup (H ⧸ pCore 2 H)) := by
    have hh := card_dvd_of_le (show actorImage H R₀ ≤ A ⊔ (P : Subgroup (H ⧸ pCore 2 H)) from
      (map_mono (comap_mono (map_subtype_le _))).trans le_sup_left)
    have hc : Nat.card (actorImage H R₀) = 9 :=
      (S.original_point_sylow_star D hZ z hz hTz hH R).2.1
    rwa [hc] at hh
  exact Matrix.PSL3Two.SquareParabolic.exchanged_full_wreath C A P hcomp e hi (pCore_quotient_pCore_eq_bot 2)
    ((S.original_star_sqtk D hZ z hz hH).stronglyQuasithin 3 Nat.prime_three (by decide))
    (S.original_point_residual_star_twoPerfect D hZ z hH)
    (S.original_point_residual_star_twoThree D hZ z hz hTz hH) hPA hg h9

private theorem binary_plane_wreath_solvable : Group.IsSolvable WreathTwoResidual.Actor := by
  let : Group.IsNilpotent (pCore 3 WreathTwoResidual.Actor) := pCore_isPGroup.isNilpotent
  let : Group.IsNilpotent (WreathTwoResidual.Actor ⧸ pCore 3 WreathTwoResidual.Actor) :=
    WreathTwoResidual.threeCore_quotient_two.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 3 WreathTwoResidual.Actor)).mpr
    ⟨inferInstance,inferInstance⟩

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The two marked parabolic wreaths lift to solvable overgroups of the
original T and generate H, contradicting its membership in Hz. -/
theorem SourceHypothesis.original_abelian_exchanged_binary_impossible
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 2) : False := by
  obtain ⟨e⟩ := S.original_abelian_exchanged_binary_wreath D hZ z hz hTV hTz hbound hTI hns
    hH hKH hK hgen hn hm
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  obtain ⟨B₁,B₂,h₁,h₂,_,_,_,hB,⟨e₁⟩,⟨e₂⟩⟩ :=
    Matrix.PSL3Two.WreathPair.exists_parabolics q hq hk (T.subtype hTH)
  have hlocal (B : Subgroup H) (hTB : (T.subtype hTH : Subgroup H) ≤ B)
      (eB : (B ⧸ pCore 2 B) ≃* WreathTwoResidual.Actor) : B.map H.subtype ≤ M L := by
    let : Group.IsSolvable WreathTwoResidual.Actor := binary_plane_wreath_solvable
    let : Group.IsSolvable (B ⧸ pCore 2 B) :=
      Group.isSolvable_of_isSolvable_injective (f := eB.toMonoidHom) eB.injective
    let : Group.IsNilpotent (pCore 2 B) := pCore_isPGroup.isNilpotent
    let : Group.IsSolvable B :=
      (Group.isSolvable_iff_subgroup_quotient (pCore 2 B)).mpr ⟨inferInstance,inferInstance⟩
    let : Group.IsSolvable (B.map H.subtype) :=
      Group.isSolvable_of_surjective (H.subtype.subgroupMap_surjective B)
    apply S.original_solvable_overgroup_le D hZ z hz hTV hTz hbound hTI hns
    intro t ht
    exact mem_map_of_mem H.subtype (hTB (show (⟨t,hTH ht⟩ : H) ∈ T.subtype hTH from ht))
  have hM : H ≤ M L := by
    have hh := sup_le (hlocal B₁ h₁ e₁) (hlocal B₂ h₂ e₂)
    rwa [←Subgroup.map_sup,hB,←MonoidHom.range_eq_map,range_subtype] at hh
  exact hH.2.2 hM

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- After Suzuki and binary-three exclusion, an exchanged component is
PSL₂ over a binary field of order at least four, in both original quotients. -/
theorem SourceHypothesis.original_abelian_exchanged_linearTwo_models
    (hn : ¬ (K.subgroupOf H).Normal) :
    ∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n) ∧
      ClassicalGroup.IsPSL (actorImage H K) 2 (2 ^ n) := by
  have hm := ((S.original_abelian_nonnormal_component_models D hZ z hz hTV hTz hbound hTI hns
    hH hKH hK hgen hn).2).transport (componentStarEquiv H K hKH hK)
  rcases hm with ⟨n,hn,he⟩ | ⟨m,hm,⟨e⟩⟩ | he
  · exact ⟨n,hn,he,he.of_mulEquiv (componentStarEquiv H K hKH hK).symm⟩
  · exact (S.original_abelian_suzuki_impossible D hZ z hz hTV hTz hbound hTI hns
      hH hKH hK hgen (by omega) e).elim
  · exact (S.original_abelian_exchanged_binary_impossible D hZ z hz hTV hTz hbound hTI hns
      hH hKH hK hgen hn he).elim

include hz hTV hTz hbound hTI hns hH in
/-- The original reduced actor has only higher-field Lie components, and
the exchanged case has only PSL₂. The escaping component remains a
C-component in both the original H and the actual reduced J=K₀L₁T. -/
theorem SourceHypothesis.original_abelian_reduced_Lie_component_models :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧ ¬ K ≤ M L ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧
      (D.fullSetup hZ T z).L₁ ≤ normalizer (K : Set G) ∧
      let K₀ := conjugateSpanBy K (T : Subgroup G)
      let J := K₀ ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)
      (K₀.subgroupOf H).Normal ∧ J ≤ H ∧ J ∈ (D.fullSetup hZ T z).Hz ∧
      (K.subgroupOf J).IsCComponent ∧
      (((K.subgroupOf J).Normal ∧
          AbelianLieHigherFieldModel (K ⧸ pCore 2 K) ∧
          AbelianLieHigherFieldModel (actorImage J K)) ∨
        (¬ (K.subgroupOf J).Normal ∧ (normalizer (K.subgroupOf J : Set J)).index = 2 ∧
          ∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n) ∧
            ClassicalGroup.IsPSL (actorImage J K) 2 (2 ^ n))) := by
  obtain ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ⟩ :=
    S.original_abelian_quasisimple_reduced_actor_exists D hZ z hz hTV hTz hbound hTI hns hH
  have hKle := (le_conjugateSpanBy K (T : Subgroup G)).trans
    (le_sup_left.trans (le_sup_left :
      conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ≤
        conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)))
  refine ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ,?_⟩
  rcases S.original_abelian_component_model_alternatives D hZ z hz hTV hTz hbound hTI hns
      hJ hKle hKJ rfl with ⟨hn,_,_⟩ | ⟨hn,hi,_,_⟩
  · exact Or.inl ⟨hn,S.original_abelian_normal_lie_models D hZ z hz hTV hTz hbound hTI hns
      hJ hKle hKJ hout rfl hn⟩
  · exact Or.inr ⟨hn,hi,S.original_abelian_exchanged_linearTwo_models D hZ z hz hTV hTz
      hbound hTI hns hJ hKle hKJ rfl hn⟩

end CFSG.Quasithin.Chapter12.Section06
