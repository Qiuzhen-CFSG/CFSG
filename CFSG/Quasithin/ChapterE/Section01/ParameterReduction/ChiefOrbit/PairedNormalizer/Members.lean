module

public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.GeneralizedFitting.ResidualOvergroups
public import CFSG.Quasithin.ChapterE.Section01.Inheritance.IntrinsicTransport
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.Assembly
import all CFSG.Quasithin.ChapterE.Section01.Inheritance.IntrinsicTransport

/-!
# Actual E-members from a full tau orbit

Let X=⟨K,τ(T,A)⟩. If the tau orbit of the component is the ambient
residual and layer, X is a subnormal residual overgroup. Its radical,
residuals and prescribed Sylow intersection are therefore exact. The
intrinsic tau contains the ambient tau, so its component orbit is the
whole layer. Transport through the literal radical quotient then checks
both E.1.2 component-action alternatives and the original rank bound.

The actor may normalize K; only the tau orbit is required to be full.
The paired normalizer consumer supplies a moving rank-one actor.

Source: Aschbacher–Smith, E.1.2 and E.1.11, printed pp.210, 213–214.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ChiefOrbit
variable {G : Type*} [Group G] [Finite G]

theorem eCaseComponent_of_radical_free_orbit (T A X : Subgroup G)
    (hrad : solvableRadical X = ⊥)
    (hres : pResidual 2 X = solvableResidual X)
    (hq : HasTwoGroupQuotient (componentLayer X))
    (L : Subgroup X) (hL : IsComponent X L)
    (ho : componentLayer X = conjugateJoin (tau (T.subgroupOf X) (A.subgroupOf X)) L)
    (ha : L = ⁅L, A.subgroupOf X⁆ ∨
      (¬ A.subgroupOf X ≤ normalizer (L : Set X)) ∧ Group.rank (A.subgroupOf X) = 1) :
    ECaseComponent T A X := by
  let e : X ≃* X ⧸ solvableRadical X :=
    ((QuotientGroup.quotientMulEquivOfEq hrad).trans QuotientGroup.quotientBot).symm
  have he : e.toMonoidHom = QuotientGroup.mk' (solvableRadical X) := by ext x; rfl
  have hc : IsTwoClosed (solvableRadical X) := by
    have : Subsingleton (solvableRadical X) := hrad ▸ inferInstance
    let S : Sylow 2 (solvableRadical X) := default
    refine ⟨S, ?_⟩
    have hb : (S : Subgroup (solvableRadical X)) = ⊥ := Subsingleton.elim _ _
    rw [hb]
    infer_instance
  refine ⟨hc, ?_, hres, L.map e.toMonoidHom, hL.map_equiv e, ?_, ?_⟩
  · have h := hq.intrinsic_equiv e
    rwa [intrinsic_layer_map] at h
  · have h := congrArg (Subgroup.map e.toMonoidHom) ho
    rw [intrinsic_layer_map, intrinsic_conjugateJoin_map, he] at h
    exact h
  · rcases ha with ha | ⟨hn,hr⟩
    · left
      simpa only [map_commutator, he] using congrArg (Subgroup.map e.toMonoidHom) ha
    · right
      refine ⟨?_, ?_⟩
      · intro hh
        apply hn
        rw [← he, ← map_normalizer_eq_of_bijective L e.bijective] at hh
        exact (map_le_map_iff_of_injective e.injective).mp hh
      · exact (Group.rank_congr ((A.subgroupOf X).equivMapOfInjective
          (QuotientGroup.mk' (solvableRadical X)) (he ▸ e.injective))).symm.trans hr


theorem tau_join_component_case_of_full_orbit
    (T : Sylow 2 G) {K A : Subgroup G} (hK : IsComponent G K)
    (hrad : solvableRadical G = ⊥) (hlayer : pResidual 2 G = componentLayer G)
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (horbit : componentOrbit K (tau (T : Subgroup G) A) = pResidual 2 G)
    (halt : K = ⁅K,A⁆ ∨ (¬ A ≤ normalizer (K : Set G)) ∧ Group.rank A = 1) :
    ECaseComponent (T : Subgroup G) A (K ⊔ tau (T : Subgroup G) A) := by
  let X := K ⊔ tau (T : Subgroup G) A
  have hAt : A ≤ tau (T : Subgroup G) A := le_sup_left.trans (sup_pCore_le_tau T A hAT)
  have hAX : A ≤ X := hAt.trans le_sup_right
  have hKX : K ≤ X := le_sup_left
  have hRX : pResidual 2 G ≤ X := by
    rw [← horbit]
    exact componentOrbit_le_sup K (tau (T : Subgroup G) A)
  obtain ⟨hr,he,hp,hs⟩ := residual_overgroup_structure hrad hlayer X hRX
  let C := K.subgroupOf X
  let D := tau ((T : Subgroup G).subgroupOf X) (A.subgroupOf X)
  have hC : IsComponent X C := hK.subgroupOf hKX
  have ho : componentLayer X = conjugateJoin D C := by
    apply le_antisymm
    · apply (map_le_map_iff_of_injective X.subtype_injective).mp
      rw [he, ← horbit]
      have hCD : K ≤ (conjugateJoin D C).map X.subtype := by
        rw [← map_subgroupOf_eq_of_le hKX]
        exact map_mono (le_componentOrbit C D)
      have hAD : tau (T : Subgroup G) A ≤ D.map X.subtype :=
        tau_le_map_tau (T : Subgroup G) A X le_sup_right
      have hn : D.map X.subtype ≤ normalizer ((conjugateJoin D C).map X.subtype : Set G) :=
        (map_mono (le_normalizer_componentOrbit C D)).trans (le_normalizer_map X.subtype)
      exact iSup_conjugates_le_of_le_normalizer K (tau (T : Subgroup G) A) _ hCD (hAD.trans hn)
    · exact iSup_le fun d => le_sSup (hC.map_conj d)
  have hq : HasTwoGroupQuotient (componentLayer X) := by
    rw [← hp]
    exact ⟨inferInstance,isPGroup_quotient_pResidual 2⟩
  apply eCaseComponent_of_radical_free_orbit _ A X hr hs hq C hC ho
  rcases halt with halt | ⟨hm,hra⟩
  · left
    apply map_injective X.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hKX, map_subgroupOf_eq_of_le hAX]
    exact halt
  · right
    refine ⟨?_, (Group.rank_congr (subgroupOfEquivOfLe hAX)).trans hra⟩
    intro hmX
    apply hm
    intro a ha
    have hh := hmX (show (⟨a,hAX ha⟩ : X) ∈ A.subgroupOf X from ha)
    rw [← subgroupOf_normalizer_eq hKX] at hh
    exact hh

theorem tau_join_member_of_full_orbit {n : ℕ}
    (T : Sylow 2 G) {K A : Subgroup G} (hK : IsComponent G K)
    (hrad : solvableRadical G = ⊥) (hlayer : pResidual 2 G = componentLayer G)
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (horbit : componentOrbit K (tau (T : Subgroup G) A) = pResidual 2 G)
    (halt : K = ⁅K,A⁆ ∨ (¬ A ≤ normalizer (K : Set G)) ∧ Group.rank A = 1)
    (hrank : Group.rank A ≤ n) :
    IsEMemberAt n (T : Subgroup G) A (K ⊔ tau (T : Subgroup G) A) := by
  let X := K ⊔ tau (T : Subgroup G) A
  have hAX : A ≤ X := (le_sup_left.trans (sup_pCore_le_tau T A hAT)).trans le_sup_right
  have hRX : pResidual 2 G ≤ X := by
    rw [← horbit]
    exact componentOrbit_le_sup K (tau (T : Subgroup G) A)
  have hc := tau_join_component_case_of_full_orbit T hK hrad hlayer hAT horbit halt
  exact ⟨⟨inferInstance,hAT,hAX,le_inf (tau_le _ _) le_sup_right,
      T.exists_subgroupOf_eq_of_subnormal X (residual_overgroup_subnormal X hRX), Or.inr hc⟩,
    Or.inr ⟨hc,(ValuesEvenClassical.RankOneUpper.rank_quotient_image_le A X hAX _).trans hrank⟩⟩

end CFSG.Quasithin.ChapterE.ChiefOrbit
