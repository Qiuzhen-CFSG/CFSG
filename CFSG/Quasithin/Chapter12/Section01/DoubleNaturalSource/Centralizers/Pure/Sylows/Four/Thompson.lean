module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Offenders
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Escape
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Stellmacher.CentralizerQuotientRepresentation

/-!
# The original Thompson subgroup in the contrary ambient Sylow branch

Maximum elementary subgroups of T have offender images on the original
normal elementary orbit. The dimension-four offender bound puts those images
in the natural-summand normalizer. Pullback through the actual action quotient
therefore gives J(T) <= T1 and J(T1) = J(T), without a faithfulness assumption
on T itself.

The same escaping Sylow from `Escape` now normalizes J(T). Hence its ambient
normalizer escapes M. If J(T) lay in Q = O2(LT), Thompson heredity would give
J(T) = J(Q); characteristic-normalizer uniqueness would then put its entire
normalizer in M. This proves both J(T) not <= Q and nontrivial action on W,
the source input to the subsequent B.5.1 and parabolic arguments.

These are original chosen-module applications with no MS classification
premise. The ambient Sylow contradiction, component exclusions and final
fusion/closure assembly remain with `qt-d-double-natural-pure-fusion`;
`qt-d-double-natural-centralizers` supplies the earlier source inputs.
Source: Aschbacher--Smith, 12.1.4, printed p.790, using B.2.5--7.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
open Stellmacher
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {B : DoubledBranch T L V 4}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

include S in
/-- The original maximum elementary subgroups preserve the natural summand. -/
theorem four_thompson_le_naturalNormalizer
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hWT : componentOrbit V (T : Subgroup G) ≤ (T : Subgroup G)) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤
      (T : Subgroup G) ⊓ normalizer (B.naturalSummand : Set G) := by
  let W := componentOrbit V (T : Subgroup G)
  let M := normalizer (L : Set G)
  have hWM : W ≤ M := hWT.trans hTM
  have hMW : M ≤ normalizer (W : Set G) := by
    dsimp [W,M]
    rw [B.orbit_eq]
    exact le_normalizer_componentOrbit _ _
  let U := W.subgroupOf M
  let : U.Normal := normal_subgroupOf_of_le_normalizer hMW
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hWM
  let q := B.actionProjection
  have hq : Function.Surjective q := B.actionProjection_surjective
  have hk : q.ker = centralizer (U : Set M) := by
    rw [show q.ker = (normalizerAction T L V B.orbit_eq).ker from QuotientGroup.ker_mk' _,
      normalizerAction_ker]
    ext m
    constructor
    · intro hm u hu
      exact Subtype.ext (hm u hu)
    · intro hm w hw
      exact congrArg M.subtype (hm ⟨w,hWM hw⟩ hw)
  let ρ := NormalElementaryQuotient.representation U q hq hk
  let E : Additive U ≃ₗ[ZMod 2] Additive W :=
    LinearEquiv.ofBijective ((subgroupOfEquivOfLe hWM).toMonoidHom.toAdditive.toZModLinearMap 2)
      (subgroupOfEquivOfLe hWM).bijective
  have hE (a : B.ActionQuotient) (v : Additive U) :
      E (ρ a v) = S.setup.representation a (E v) := by
    obtain ⟨m,rfl⟩ := hq a
    apply Additive.toMul.injective
    apply Subtype.ext
    change (((ρ (q m) v).toMul : M) : G) =
      ((S.setup.representation (q m) (E v)).toMul : G)
    rw [S.representation_eq]
    change (((ρ (q m) v).toMul : M) : G) =
      (B.quotientAction (B.actionProjection m) (E v).toMul : G)
    rw [B.quotientAction_projection_apply]
    exact congrArg M.subtype (NormalElementaryQuotient.representation_apply U q hq hk m v)
  apply sSup_le
  intro A hA
  have hAM : A ≤ M := hA.1.trans hTM
  let A' := A.subgroupOf M
  have hA' : A' ∈ elementaryAbelianMaxSubgroups ((T : Subgroup G).subgroupOf M) := by
    let := hA.2.1
    refine ⟨fun x hx => hA.1 hx,IsElementaryAbelian.subgroupOf hAM,?_⟩
    intro C hC he
    have hCT : C.map M.subtype ≤ (T : Subgroup G) := by
      rintro _ ⟨c,hc,rfl⟩
      exact hC hc
    have hh := hA.2.2 (C.map M.subtype) hCT (he.map M.subtype)
    rw [card_map_of_injective M.subtype_injective] at hh
    exact hh.trans_eq (Nat.card_congr (subgroupOfEquivOfLe hAM).toEquiv).symm
  have hle : A'.map q ≤ componentLayer B.ActionQuotient := by
    by_cases hz : A' ≤ q.ker
    · rw [(map_eq_bot_iff A').mpr hz]
      exact bot_le
    · have ho := NormalElementaryQuotient.maxElementary_isOffender U q hq hk
        ((T : Subgroup G).subgroupOf M) A' (fun x hx => hWT hx) hA' hz
      have ho' := ho.map_equivariant ρ S.setup.representation (MonoidHom.id _)
        (Function.injective_id) E hE
      rw [Subgroup.map_id] at ho'
      exact S.setup.four_offender_le_layer _ ho'
  intro a ha
  refine ⟨hA.1 ha,?_⟩
  have hh := hle (mem_map_of_mem q (show (⟨a,hAM ha⟩ : M) ∈ A' from ha))
  rw [← S.setup.naturalNormalizer_eq_layer] at hh
  have hmem : (⟨a,hAM ha⟩ : M) ∈ S.setup.naturalNormalizer.comap B.actionProjection := hh
  rw [S.naturalNormalizer_comap] at hmem
  exact hmem
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Stellmacher
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Thompson containment and equality at the original marked pure point. -/
theorem doubleNatural_four_pure_thompson_eq_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      elementaryAbelianMaxJ (T : Subgroup G) ≤ B.pointSylow w ∧
        elementaryAbelianMaxJ (B.pointSylow w) = elementaryAbelianMaxJ (T : Subgroup G) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix
  have he := S.marked_centralizer_eq D.sylow_normalizes_component w hw hp hfix
  change B.pointSylow w = _ at he
  have hle : elementaryAbelianMaxJ (T : Subgroup G) ≤ B.pointSylow w := by
    rw [he]
    exact S.four_thompson_le_naturalNormalizer D.sylow_normalizes_component
      (D.doubledOrbit_E322 h).le_sylow
  exact ⟨hle,elementaryAbelianMaxJ_eq_of_intermediate_finite _ _ hle inf_le_left⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Stellmacher
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The same escaping Sylow normalizes the original Thompson subgroup;
its ambient normalizer therefore escapes M. -/
theorem doubleNatural_four_pure_thompson_escape_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      ¬ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) ∧
        ∃ P : Sylow 2 G, B.pointSylow w < (P : Subgroup G) ∧
          (P : Subgroup G) ≤ B.pointCentralizer w ∧
          (P : Subgroup G) ⊓ normalizer (L : Set G) = B.pointSylow w ∧
          ¬ (P : Subgroup G) ≤ normalizer (L : Set G) ∧
          (T : Subgroup G) ⊔ (P : Subgroup G) ≤
            normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf
  have he := S.marked_centralizer_eq D.sylow_normalizes_component w hw hp hfix
  change B.pointSylow w = _ at he
  have hfail : ¬ Chapter1.IsSylowIn 2
      ((T : Subgroup G) ⊓ normalizer (B.naturalSummand : Set G)) (B.pointCentralizer w) :=
    he ▸ hf
  obtain ⟨_,P,hlt,hPC,_,hPN,hPM,hout,hN⟩ :=
    D.doubleNatural_pure_sylow_escape_of_many h hmany B S w hw hp hfix hfail
  rw [←he] at hlt hPN hPM hN
  have hJ := (D.doubleNatural_four_pure_thompson_eq_of_many h hmany B S w hw hp hfix).2
  have hn : normalizer (B.pointSylow w : Set G) ≤
      normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
    rw [←hJ]
    exact normalizer_le_normalizer_elementaryAbelianMaxJ _
  refine ⟨fun hh => hN (hn.trans hh),P,hlt,hPC,hPM,hout,?_⟩
  exact sup_le ((T : Subgroup G).le_normalizer.trans
    (normalizer_le_normalizer_elementaryAbelianMaxJ _)) (hPN.trans hn)

/-- The source Thompson movement needed for B.5.1 follows from the original
normalizer uniqueness and the literal two-core, without an extra local premise. -/
theorem doubleNatural_four_pure_thompson_moves_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
        ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
          centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf
  have hN := (D.doubleNatural_four_pure_thompson_escape_of_many h hmany B S w hw hp hfix hf).1
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hJQ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ Q := by
    intro hc
    have he := elementaryAbelianMaxJ_eq_of_intermediate_finite (T : Subgroup G) Q hc hQT
    have hQne : Q ≠ ⊥ := fun he => D.ne_bot (bot_unique (D.le_core.trans_eq he))
    have hnQ : L ⊔ (T : Subgroup G) ≤ normalizer (Q : Set G) :=
      (L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
    have hnJ := D.normal_subgroup_normalizer_le h.toHypothesis1221
      ((sSup_le fun _ hA => hA.1).trans (map_subtype_le _))
      (elementaryAbelianMaxJ_ne_bot_of_finite_pGroup Q (pCore_isPGroup.map _) hQne)
      (hnQ.trans (normalizer_le_normalizer_elementaryAbelianMaxJ Q))
    exact hN (he ▸ hnJ)
  refine ⟨hJQ,?_⟩
  intro hc
  apply hJQ
  dsimp only [Q]
  rw [←D.doubledOrbit_sylow_centralizer h]
  exact le_inf (sSup_le fun _ hA => hA.1) hc
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
