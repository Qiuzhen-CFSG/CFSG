module

public import Glauberman.SuzukiCharacterization.NormalCore
public import Theory.GroupTheory.PPrimeCorePGroupQuotient
public import Theory.GroupTheory.WeakClosureFusion

/-!
# Hypothesis inheritance for a normal-subgroup Sylow product

For a nontrivial normal subgroup N, the product H = NP has trivial odd core:
H/N is a two-group, and N already has trivial odd core. A normal Sylow
subgroup in H would restrict to a normal Sylow subgroup in N, which is
excluded by `NormalCore`. Noncommutativity and the normal-complement
condition on involution centralizers descend to every subgroup containing P.

The central intersection N ∩ Z(P), restricted to H, remains weakly closed
and central in P. Its centralizer has a normal two-complement, so the
weak-closure fusion argument of Lemma 2.1(ii–iii) gives normalizer control
of element fusion. Thus H inherits all the characterization hypotheses.

Source: Glauberman, *A Characterization of the Suzuki Groups* (1968),
Lemma 2.1 and Proposition 2.1(ii), pp. 78–80, saved at
`refs/original/n-group-global/odd-core-rank-two-source/glauberman-suzuki-1968-euclid-wayback.pdf`.
-/

namespace Glauberman.SuzukiCharacterization
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The normal-subgroup Sylow product inherits the trivial odd core. -/
public theorem Hypotheses.normalSup_oddCore_eq_bot (P : Sylow 2 G) (h : Hypotheses P)
    (N : Subgroup G) [N.Normal] : pPrimeCore 2 ↥(N ⊔ (P : Subgroup G)) = ⊥ := by
  let H := N ⊔ (P : Subgroup G)
  let e : N.subgroupOf H ≃* N := subgroupOfEquivOfLe le_sup_left
  have hNH : pPrimeCore 2 (N.subgroupOf H) = ⊥ := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [pPrimeCore_map_iso, h.normal_oddCore_eq_bot P N, Subgroup.map_bot]
  apply pPrimeCore_eq_bot_of_isPGroup_quotient 2 (N.subgroupOf H) hNH
  change IsPGroup 2 (↥(N ⊔ (P : Subgroup G)) ⧸ N.subgroupOf (N ⊔ (P : Subgroup G)))
  rw [sup_comm N (P : Subgroup G)]
  exact (P.isPGroup'.to_quotient (N.subgroupOf (P : Subgroup G))).of_equiv
    (QuotientGroup.quotientInfEquivProdNormalQuotient (P : Subgroup G) N)

/-- Normality of the Sylow subgroup in NP would imply normality of its
intersection with N. -/
public theorem Hypotheses.normalSup_sylow_not_normal (P : Sylow 2 G) (h : Hypotheses P)
    (N : Subgroup G) [N.Normal] (hne : N ≠ ⊥) :
    ¬ ((P.subtype (show (P : Subgroup G) ≤ N ⊔ (P : Subgroup G) from le_sup_right)) :
      Subgroup ↥(N ⊔ (P : Subgroup G))).Normal := by
  intro hn
  let H := N ⊔ (P : Subgroup G)
  let PH := P.subtype (show (P : Subgroup G) ≤ H from le_sup_right)
  let : (PH : Subgroup H).Normal := hn
  obtain ⟨T, hT⟩ := P.exists_subgroupOf_eq_of_normal N
  apply h.normal_sylow_not_normal P N hne T
  rw [hT]
  exact (inferInstance : ((PH : Subgroup H).comap
    (Subgroup.inclusion (show N ≤ H from le_sup_left))).Normal)

omit [Finite G] in
/-- Restriction to an overgroup does not change the Sylow subgroup's
noncommutativity. -/
public theorem Hypotheses.subtype_not_commutative (P : Sylow 2 G) (h : Hypotheses P)
    (H : Subgroup G) (hPH : (P : Subgroup G) ≤ H) :
    ¬ IsMulCommutative (P.subtype hPH) := by
  intro hc
  let e : (P.subtype hPH) ≃* P := Subgroup.subgroupOfEquivOfLe hPH
  apply h.not_commutative
  rw [isMulCommutative_iff] at hc ⊢
  intro x y
  obtain ⟨a, rfl⟩ := e.surjective x
  obtain ⟨b, rfl⟩ := e.surjective y
  simpa only [map_mul] using congrArg e (hc a b)

omit [Finite G] in
/-- Normal two-complements in involution centralizers descend to overgroups
of the given Sylow subgroup. -/
public theorem Hypotheses.subtype_involution_complement (P : Sylow 2 G) (h : Hypotheses P)
    (H : Subgroup G) (hPH : (P : Subgroup G) ≤ H) (x : H)
    (hx : x ∈ (P.subtype hPH : Subgroup H)) (hx2 : orderOf x = 2) :
    HasNormalPComplement 2 (centralizer ({x} : Set H)) := by
  apply hasNormalPComplement_of_map_subtype 2 H
  apply hasNormalPComplement_of_le 2 (L := centralizer ({(x : G)} : Set G))
  · rintro y ⟨z, hz, rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hz))
  · exact h.involution_complement x hx (by simpa only [Subgroup.orderOf_coe] using hx2)

/-- A nontrivial normal subgroup supplies a weakly closed central subgroup
with a normal two-complement in its centralizer, in every overgroup of P. -/
public theorem Hypotheses.subtype_fusion_data (P : Sylow 2 G) (h : Hypotheses P)
    (N : Subgroup G) [N.Normal] (hne : N ≠ ⊥)
    (H : Subgroup G) (hPH : (P : Subgroup G) ≤ H) :
    ∃ W : Subgroup H, W ≠ ⊥ ∧ W ≤ (P.subtype hPH : Subgroup H) ∧
      (P.subtype hPH : Subgroup H) ≤ centralizer (W : Set H) ∧
      (∀ g : H, W.map (MulAut.conj g).toMonoidHom ≤ (P.subtype hPH : Subgroup H) →
        g ∈ normalizer (W : Set H)) ∧
      HasNormalPComplement 2 (centralizer (W : Set H)) := by
  let W := normalCenterIntersection P N
  have hWP : W ≤ (P : Subgroup G) := normalCenterIntersection_le_sylow P N
  have hWH : W ≤ H := hWP.trans hPH
  have hWne : W ≠ ⊥ := h.normalCenterIntersection_ne_bot P N hne
  refine ⟨W.subgroupOf H, ?_, ?_, ?_, ?_, ?_⟩
  · intro he
    apply hWne
    rw [← map_subgroupOf_eq_of_le hWH, he, Subgroup.map_bot]
  · intro x hx
    exact hWP hx
  · intro x hx
    apply mem_centralizer_iff.mpr
    intro z hz
    apply Subtype.ext
    obtain ⟨zP, hzP, hzG⟩ := hz
    change (z : G) * (x : G) = (x : G) * (z : G)
    change (zP : G) = (z : G) at hzG
    rw [← hzG]
    exact (congrArg Subtype.val (mem_center_iff.mp hzP.2 ⟨x, hx⟩)).symm
  · intro g hg
    have hgW : (g : G) ∈ normalizer (W : Set G) := by
      apply h.normalCenterIntersection_weakly_closed P N
      rintro x ⟨z, hz, rfl⟩
      exact hg (mem_map_of_mem (MulAut.conj g).toMonoidHom
        (show (⟨z, hWH hz⟩ : H) ∈ W.subgroupOf H from hz))
    apply mem_normalizer_fintype
    intro x hx
    exact (mem_normalizer_iff.mp hgW (x : G)).mp hx
  · obtain ⟨x, hxW, hxne⟩ := W.bot_or_exists_ne_one.resolve_left hWne
    apply hasNormalPComplement_of_map_subtype 2 H
    apply hasNormalPComplement_of_le 2 (L := centralizer ({x} : Set G))
    · rintro y ⟨z, hz, rfl⟩
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_iff.mp hz ⟨x, hWH hxW⟩ hxW)).symm
    · exact h.centralizer_hasNormalPComplement P x (hWP hxW) hxne

/-- Every product of a nontrivial normal subgroup with P inherits the
Suzuki characterization hypotheses. -/
public theorem Hypotheses.normalSup (P : Sylow 2 G) (h : Hypotheses P)
    (N : Subgroup G) [N.Normal] (hne : N ≠ ⊥) :
    Hypotheses (P.subtype
      (show (P : Subgroup G) ≤ N ⊔ (P : Subgroup G) from le_sup_right)) := by
  refine ⟨h.normalSup_oddCore_eq_bot P N, h.normalSup_sylow_not_normal P N hne,
    h.subtype_not_commutative P _ le_sup_right, ?_,
    h.subtype_involution_complement P _ le_sup_right⟩
  obtain ⟨W, _, hWP, hPC, hweak, K, hK, hcop, hquot⟩ :=
    h.subtype_fusion_data P N hne (N ⊔ (P : Subgroup G)) le_sup_right
  exact (P.subtype le_sup_right).normalizer_controls_fusion_of_weakly_closed
    W hWP hPC hweak K hcop hquot

end Glauberman.SuzukiCharacterization
