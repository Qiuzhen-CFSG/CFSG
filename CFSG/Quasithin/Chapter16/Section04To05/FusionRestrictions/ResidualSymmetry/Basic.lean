module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.Residual
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.TwoCentral

/-!
# Residual coherence and the two faithful action quotients

The common-residual argument is specialized to the actual conjugate component.
The involution witnesses come from the chosen central involution and the
16.4.11 equality R = T_C^g. Exceptional two-perfectness remains a local-model
input; the other perfectness and the common-residual equalities are deductions.

The action quotient below is N_G(L)/C_G(L), with normality relative to the
normalizer. Its component image retains the kernel Z(L). A subgroup disjoint
from C_G(L) embeds in this quotient, so its involutions are exactly the lifts
of involutions of its image. This is the bridge needed to state all four
clauses of 16.5.6(4) for the source's H/K and H'/K'.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 16.5.5 and Lemma 16.5.6, printed p.1197.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G]

/-- The actual action quotient H/K. Its kernel is normal in H, not in G. -/
abbrev ActionQuotient (L : Subgroup G) :=
  normalizer (L : Set G) ⧸
    (centralizer (L : Set G)).subgroupOf (normalizer (L : Set G))

/-- The action map for a specified subgroup of H. -/
def actionMap {L A : Subgroup G} (hA : A ≤ normalizer (L : Set G)) :
    A →* ActionQuotient L :=
  (QuotientGroup.mk' ((centralizer (L : Set G)).subgroupOf
    (normalizer (L : Set G)))).comp (inclusion hA)

/-- L* is the actual image of L in H/K, including a possible central kernel. -/
def componentImage (L : Subgroup G) : Subgroup (ActionQuotient L) :=
  (actionMap L.le_normalizer).range

/-- The kernel on the component is exactly its center, so central covers
are retained rather than identified with their simple quotients. -/
theorem component_action_kernel (L : Subgroup G) :
    (actionMap L.le_normalizer).ker = center L := by
  ext x
  change QuotientGroup.mk' _ (inclusion L.le_normalizer x) = 1 ↔ x ∈ center L
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro hx
    exact mem_center_iff.mpr fun y =>
      Subtype.ext (mem_centralizer_iff.mp hx y y.property)
  · intro hx
    exact mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (mem_center_iff.mp hx ⟨y, hy⟩)

/-- Identify L/Z(L) with the actual L* inside H/K by the quotient map. -/
noncomputable def componentImageEquiv (L : Subgroup G) :
    (L ⧸ center L) ≃* componentImage L :=
  (QuotientGroup.quotientMulEquivOfEq (component_action_kernel L).symm).trans
    (QuotientGroup.quotientKerEquivRange (actionMap L.le_normalizer))

/-- The comparison with L/Z(L) sends each class to its specified action image. -/
theorem componentImageEquiv_mk (L : Subgroup G) (x : L) :
    (componentImageEquiv L (QuotientGroup.mk' (center L) x) : ActionQuotient L) =
      actionMap L.le_normalizer x := rfl

/-- Faithfulness on L makes the quotient map injective on the actor. -/
theorem actionMap_injective {L A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G))
    (hfaith : A ⊓ centralizer (L : Set G) = ⊥) :
    Function.Injective (actionMap hA) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro a ha
  have hc : (a : G) ∈ centralizer (L : Set G) :=
    (QuotientGroup.eq_one_iff (inclusion hA a)).mp ha
  apply Subtype.ext
  have hm : (a : G) ∈ A ⊓ centralizer (L : Set G) := ⟨a.property, hc⟩
  simpa only [hfaith, mem_bot, coe_one] using hm

/-- In particular, quotienting does not create or lose actor involutions. -/
theorem actionMap_orderOf {L A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G))
    (hfaith : A ⊓ centralizer (L : Set G) = ⊥) (a : A) :
    orderOf (actionMap hA a) = orderOf (a : G) := by
  rw [orderOf_injective (actionMap hA) (actionMap_injective hA hfaith)]
  exact (orderOf_submonoid a).symm

/-- Existential two-centrality in the source quotient can be tested on actual
involutions of the faithful actor, always after applying the quotient map. -/
theorem exists_twoCentral_image_iff {L A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G))
    (hfaith : A ⊓ centralizer (L : Set G) = ⊥) :
    (∃ a ∈ (actionMap hA).range, IsTwoCentralIn (componentImage L) a) ↔
      ∃ a : A, orderOf (a : G) = 2 ∧
        IsTwoCentralIn (componentImage L) (actionMap hA a) := by
  constructor
  · rintro ⟨a, ⟨r, rfl⟩, ha⟩
    exact ⟨r, (actionMap_orderOf hA hfaith r).symm.trans ha.1, ha⟩
  · rintro ⟨a, _, ha⟩
    exact ⟨_, ⟨a, rfl⟩, ha⟩

/-- Universal two-centrality uses involutions in the quotient image, rather
than assuming every actor element lies in L. -/
theorem forall_twoCentral_image_iff {L A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G))
    (hfaith : A ⊓ centralizer (L : Set G) = ⊥) :
    (∀ a ∈ (actionMap hA).range, orderOf a = 2 →
      IsTwoCentralIn (componentImage L) a) ↔
      ∀ a : A, orderOf (a : G) = 2 →
        IsTwoCentralIn (componentImage L) (actionMap hA a) := by
  constructor
  · intro h a ha
    exact h _ ⟨a, rfl⟩ ((actionMap_orderOf hA hfaith a).trans ha)
  · rintro h a ⟨r, rfl⟩ ha
    exact h r ((actionMap_orderOf hA hfaith r).symm.trans ha)

/-- Centralization passes to the two actual quotient images. -/
theorem actionImages_centralize {L A X : Subgroup G}
    (hA : A ≤ normalizer (L : Set G)) (hX : X ≤ normalizer (L : Set G))
    (hc : A ≤ centralizer (X : Set G)) :
    (actionMap hA).range ≤ centralizer ((actionMap hX).range : Set (ActionQuotient L)) := by
  rintro a ⟨r, rfl⟩
  apply mem_centralizer_iff.mpr
  rintro x ⟨y, rfl⟩
  let q := QuotientGroup.mk' ((centralizer (L : Set G)).subgroupOf
    (normalizer (L : Set G)))
  have he : inclusion hX y * inclusion hA r = inclusion hA r * inclusion hX y :=
    Subtype.ext (mem_centralizer_iff.mp (hc r.property) y y.property)
  exact congrArg q he |>.trans (by simp only [map_mul]; rfl)

variable [Finite G]

/-- Specialize Notation 16.5.5 to L and its actual conjugate. The only
perfectness assumptions left are the exceptional local calculations. -/
theorem exists_common_residual_conjugate {T : Sylow 2 G} {z g : G} {L R : Subgroup G}
    (h : IntersectionSetup T z L g R)
    (htransport : R = (commutingSylow T L).conjBy g)
    (hforward : ∀ u ∈ R, orderOf u = 2 →
      modifiedCentralizerResidual L u ≤ L.conjBy g)
    (hbackward : ∀ i ∈ commutingSylow T L, orderOf i = 2 →
      modifiedCentralizerResidual (L.conjBy g) i ≤ L)
    (hforward2 : HasEvenLinearThreeType L → ∀ u ∈ R, orderOf u = 2 →
      IsPPerfect 2 (modifiedCentralizerResidual L u))
    (hbackward2 : HasEvenLinearThreeType (L.conjBy g) →
      ∀ i ∈ commutingSylow T L, orderOf i = 2 →
        IsPPerfect 2 (modifiedCentralizerResidual (L.conjBy g) i)) :
    ∃ X : Subgroup G, X ≤ L ⊓ L.conjBy g ∧
      R ⊔ commutingSylow T L ≤ centralizer (X : Set G) ∧
      (∀ u ∈ R, orderOf u = 2 → modifiedCentralizerResidual L u = X) ∧
      (∀ i ∈ commutingSylow T L, orderOf i = 2 →
        modifiedCentralizerResidual (L.conjBy g) i = X) := by
  have hz : z ∈ commutingSylow T L := by
    refine ⟨h.mem_sylow, ?_⟩
    exact mem_centralizer_iff.mpr fun x hx =>
      mem_centralizer_singleton_iff.mp (h.component.1 hx)
  have hR : R ≤ centralizer (L.conjBy g : Set G) := by
    have hm := h.sylow.le.trans inf_le_left
    intro r hr
    obtain ⟨k, hk, rfl⟩ := hm hr
    apply mem_centralizer_iff.mpr
    rintro x ⟨y, hy, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, map_mul] using
      congrArg (MulAut.conj g) (mem_centralizer_iff.mp hk y hy)
  apply exists_common_residual inf_le_right hR
    ⟨MulAut.conj g z, htransport ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom hz,
      ((MulAut.conj g).orderOf_eq z).trans h.involution⟩
    ⟨z, hz, h.involution⟩ hforward hbackward
  · intro u hu hu2
    by_cases he : HasEvenLinearThreeType L
    · exact hforward2 he u hu hu2
    · exact modifiedCentralizerResidual_twoPerfect_of_nonexceptional u he
  · intro i hi hi2
    by_cases he : HasEvenLinearThreeType (L.conjBy g)
    · exact hbackward2 he i hi hi2
    · exact modifiedCentralizerResidual_twoPerfect_of_nonexceptional i he
  · exact (hasEvenLinearThreeType_map_iff L (MulAut.conj g)).symm

omit [Finite G] in
/-- A common residual is unique once one involution in the first actor is fixed. -/
theorem common_residual_unique {L R X Y : Subgroup G}
    (hu : ∃ u ∈ R, orderOf u = 2)
    (hX : ∀ u ∈ R, orderOf u = 2 → modifiedCentralizerResidual L u = X)
    (hY : ∀ u ∈ R, orderOf u = 2 → modifiedCentralizerResidual L u = Y) : X = Y := by
  obtain ⟨u, hu, hu2⟩ := hu
  exact (hX u hu hu2).symm.trans (hY u hu hu2)

/-- A perfect two-residual is unchanged by the exceptional three-residual
operation. This covers the perfect outer-centralizer rows. -/
theorem modifiedResidual_eq_of_perfect {L : Subgroup G} (u : G)
    [Group.IsPerfect (involutionTwoResidual L u)] :
    modifiedCentralizerResidual L u = involutionTwoResidual L u := by
  have hp : IsPPerfect 3 (involutionTwoResidual L u) := by
    intro N hN hq
    let := hN
    have hs : Subsingleton (involutionTwoResidual L u ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent _ hq.isNilpotent
    apply eq_top_iff.mpr
    intro x _
    exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
  classical
  unfold modifiedCentralizerResidual
  split_ifs
  · rw [(pResidual_eq_top_iff 3 _).mpr hp, ← MonoidHom.range_eq_map, range_subtype]
  · rfl

/-- The perfect outer-centralizer rows supply exceptional two-perfectness
without an additional assumption about the iterated residual. -/
theorem modifiedResidual_twoPerfect_of_perfect {L : Subgroup G} (u : G)
    [Group.IsPerfect (involutionTwoResidual L u)] :
    IsPPerfect 2 (modifiedCentralizerResidual L u) := by
  rw [modifiedResidual_eq_of_perfect]
  exact isPPerfect_embedded_pResidual 2 _

/-- Once X lies in the opposite component M, it is invariant under every
ambient automorphism preserving L ∩ M. Both residual perfectness conditions
are used in the exceptional branch. -/
theorem map_common_residual_of_intersection {L M : Subgroup G} {u : G}
    (hu : u ∈ centralizer (M : Set G))
    (hXM : modifiedCentralizerResidual L u ≤ M)
    (hX2 : IsPPerfect 2 (modifiedCentralizerResidual L u))
    (e : G ≃* G) (he : (L ⊓ M).map e.toMonoidHom = L ⊓ M) :
    (modifiedCentralizerResidual L u).map e.toMonoidHom =
      modifiedCentralizerResidual L u := by
  let X := modifiedCentralizerResidual L u
  have hXL : X ≤ L := (modifiedCentralizerResidual_le L u).trans
    ((involutionTwoResidual_le L u).trans inf_le_left)
  have hmap : X.map e.toMonoidHom ≤ L ⊓ M := by
    rw [← he]
    exact map_mono (le_inf hXL hXM)
  have h2 : IsPPerfect 2 (X.map e.toMonoidHom) :=
    hX2.of_surjective (e.subgroupMap X).toMonoidHom (e.subgroupMap X).surjective
  have h3 : HasEvenLinearThreeType L → IsPPerfect 3 (X.map e.toMonoidHom) := by
    intro hL
    exact (modifiedCentralizerResidual_threePerfect u hL).of_surjective
      (e.subgroupMap X).toMonoidHom (e.subgroupMap X).surjective
  have hle : X.map e.toMonoidHom ≤ X := by
    apply le_modifiedCentralizerResidual (hmap.trans inf_le_left) _ h2 h3
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hu x ((hmap hx).2))
  exact eq_of_le_of_card_ge hle (by rw [card_map_of_injective e.injective])

/-- The preceding invariance as an ambient normalizer containment. Establishing
that the selected 16.4.2(4) conjugator belongs to the left-hand normalizer
still requires a separate argument. -/
theorem normalizer_intersection_le_residual {L M : Subgroup G} {u : G}
    (hu : u ∈ centralizer (M : Set G))
    (hXM : modifiedCentralizerResidual L u ≤ M)
    (hX2 : IsPPerfect 2 (modifiedCentralizerResidual L u)) :
    normalizer (L ⊓ M : Set G) ≤
      normalizer (modifiedCentralizerResidual L u : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact map_common_residual_of_intersection hu hXM hX2 (MulAut.conj g)
    (mem_normalizer_iff_map_conj_eq.mp hg)

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry
