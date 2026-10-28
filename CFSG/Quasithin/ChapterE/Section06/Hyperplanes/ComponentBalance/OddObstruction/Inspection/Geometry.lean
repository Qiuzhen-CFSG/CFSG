module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Detection
public import CFSG.Quasithin.ChapterE.Section03.Parameters.AutomizerFF
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupAction.SylowFixedInvolution

/-!
# The actual component action used in E.6.19

The detected quotient component has nontrivial commutator with the image
of U. Thus U acts nontrivially on L. Since A centralizes L, the action image
has order dividing [U : A] = 2, and consequently has order exactly two.

Subnormal Sylow restriction identifies Q intersect L as a Sylow subgroup
of L, where Q is the genuine Sylow subgroup C_T(V) of C_G(A). The inclusion
V in Z(Q) makes the U-action fix this subgroup pointwise. We retain the
faithful embedding of Aut_{C_G(A)}(L) into Aut(L) and prove that its image
contains all inner automorphisms of L. The obstruction centralizer remains
exactly the centralizer defined in `Detection`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.19,
printed p.252 (PDF p.263), and E.6.8, printed pp.247–248.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction
variable {G : Type*} [Group G] {A U V L : Subgroup G}

/-- The relative component is quasisimple as a group in its own right. -/
theorem DetectedComponent.quasisimple (d : DetectedComponent A U V L) : IsQuasisimple L := by
  let := d.component.2.2
  exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe d.component.1)

/-- The quotient commutator detects a nontrivial action before taking the quotient. -/
theorem DetectedComponent.not_centralized_by_subspace (d : DetectedComponent A U V L) :
    ¬ U ≤ centralizer (L : Set G) := by
  intro hc
  have hq : ⁅quotientImage A L, quotientImage A U⁆ = ⊥ := by
    rw [quotientImage, quotientImage, ← map_commutator, Subgroup.map_eq_bot_iff]
    have hh : ⁅L.subgroupOf (centralizer (A : Set G)),
        U.subgroupOf (centralizer (A : Set G))⁆ = ⊥ := by
      apply commutator_eq_bot_iff_le_centralizer.mpr
      intro l hl u hu
      exact Subtype.ext ((hc hu) l hl).symm
    rw [hh]
    exact bot_le
  have he : quotientImage A L = ⊥ := d.commutator_subspace.symm.trans hq
  let := d.quotient_component.2
  let : IsSimpleGroup ((quotientImage A L) ⧸ center (quotientImage A L)) :=
    IsQuasisimple.simple
  let : Nontrivial (quotientImage A L) :=
    (QuotientGroup.mk'_surjective (center (quotientImage A L))).nontrivial
  exact (nontrivial_iff_ne_bot (quotientImage A L)).mp inferInstance he

/-- The action image has order exactly two, using the actual relative index. -/
theorem DetectedComponent.card_inducedAction [Finite G] (d : DetectedComponent A U V L)
    (hUV : U ≤ V) (hindex : A.relIndex U = 2) :
    Nat.card (inducedAutomizer L U) = 2 := by
  have hUN := hUV.trans d.normalized
  have hcard : Nat.card (inducedAutomizer L U) =
      (centralizer (L : Set G)).relIndex U := by
    unfold inducedAutomizer
    rw [← relIndex_ker, MonoidHom.ker_rangeRestrict,
      normalizerMonoidHom_ker, relIndex_subgroupOf hUN]
  have hAC : A ≤ centralizer (L : Set G) := le_centralizer_iff.mpr d.component.1
  have hd : Nat.card (inducedAutomizer L U) ∣ 2 := by
    rw [hcard, ← hindex]
    exact relIndex_dvd_of_le_left U hAC
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
  · exact (DetectedComponent.not_centralized_by_subspace d ((relIndex_eq_one).mp (hcard.symm.trans he))).elim
  · exact he

/-- The Sylow intersection is fixed pointwise by V; normality in G is not assumed. -/
theorem detected_sylow_fixed [Finite G] {K : GroupClass} {T : Sylow 2 G} {M : Subgroup G}
    (h : HypothesisE61 K T M V) (hA : A ∈ obstructionFamily M V)
    (d : DetectedComponent A U V L) :
    ∃ S : Sylow 2 L,
      (S : Subgroup L) = (sylowCentralizer (T : Subgroup G) V).subgroupOf L ∧
      ∀ v ∈ V, ∀ x : S, v * ((x : L) : G) * v⁻¹ = ((x : L) : G) := by
  obtain ⟨Q, hQ, _, _⟩ := sylow_geometry h hA
  obtain ⟨S, hS⟩ := Q.exists_subgroupOf_eq_of_subnormal
    (L.subgroupOf (centralizer (A : Set G))) d.component.2.1
  let e := subgroupOfEquivOfLe d.component.1
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have he : (S' : Subgroup L) =
      (sylowCentralizer (T : Subgroup G) V).subgroupOf L := by
    change (S : Subgroup _).map e.toMonoidHom = _
    rw [hS]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hQ ▸ mem_map_of_mem _ hy
    · intro hx
      have hx' : (x : G) ∈ (Q : Subgroup (centralizer (A : Set G))).map
          (centralizer (A : Set G)).subtype := hQ.symm ▸ hx
      obtain ⟨q, hq, heq⟩ := hx'
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      change (e.symm x : centralizer (A : Set G)) ∈ (Q : Subgroup _)
      exact (show q = (e.symm x : centralizer (A : Set G)) from Subtype.ext heq) ▸ hq
  refine ⟨S', he, ?_⟩
  intro v hv x
  have hx : ((x : L) : G) ∈ sylowCentralizer (T : Subgroup G) V := by
    have hx' := x.property
    change (x : L) ∈ (S' : Subgroup L) at hx'
    rwa [he] at hx'
  exact mul_inv_eq_iff_eq_mul.mpr (hx.2 v hv)

/-- The faithful inclusion of the actual induced automorphism group into Aut(L). -/
def actionEmbedding (A L : Subgroup G) :
    inducedAutomizer L (centralizer (A : Set G)) →* MulAut L :=
  (Automizer L).subtype.comp (inducedAutomizer L (centralizer (A : Set G))).subtype

/-- The action embedding is a composition of subgroup inclusions. -/
theorem actionEmbedding_injective (A L : Subgroup G) :
    Function.Injective (actionEmbedding A L) :=
  (Automizer L).subtype_injective.comp
    (inducedAutomizer L (centralizer (A : Set G))).subtype_injective

/-- Every inner automorphism occurs, because L lies in C_G(A). -/
theorem inner_le_actionEmbedding_range (hL : L ≤ centralizer (A : Set G)) :
    (MulAut.conj : L →* MulAut L).range ≤ (actionEmbedding A L).range := by
  rintro _ ⟨l, rfl⟩
  let n : normalizer (L : Set G) := ⟨l, L.le_normalizer l.property⟩
  let a : Automizer L := L.normalizerMonoidHom.rangeRestrict n
  have ha : a ∈ inducedAutomizer L (centralizer (A : Set G)) :=
    mem_map_of_mem _ (hL l.property)
  refine ⟨⟨a, ha⟩, ?_⟩
  ext x
  rfl

private theorem detected_action_card_and_fixes [Finite G] {K : GroupClass} {T : Sylow 2 G} {M : Subgroup G}
    (h : HypothesisE61 K T M V) (hA : A ∈ obstructionFamily M V)
    (hUV : U ≤ V) (hindex : A.relIndex U = 2)
    (d : DetectedComponent A U V L) :
    let E := (inducedAutomizer L U).subgroupOf
      (inducedAutomizer L (centralizer (A : Set G)))
    Nat.card E = 2 ∧ ∃ S : Sylow 2 L,
      ∀ a ∈ E, ∀ x ∈ (S : Subgroup L), actionEmbedding A L a x = x := by
  let := h.elementary
  dsimp only
  have hUH := subspace_le_centralizer hA.1 hUV
  have hcard : Nat.card ((inducedAutomizer L U).subgroupOf
      (inducedAutomizer L (centralizer (A : Set G)))) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (inducedAction_le hUH)).toEquiv]
    exact DetectedComponent.card_inducedAction d hUV hindex
  obtain ⟨S, _, hfix⟩ := detected_sylow_fixed h hA d
  refine ⟨hcard, S, ?_⟩
  intro a ha x hx
  obtain ⟨u, hu, heu⟩ := ha
  apply Subtype.ext
  change ((a : Automizer L).val x : G) = x
  have he := congrArg (fun b : Automizer L => (b.val x : G)) heu
  exact he.symm.trans (hfix u (hUV hu) ⟨x, hx⟩)

/-- The source configuration supplies every intrinsic action hypothesis. The
centralizer of E in this acting group is definitionally `actionCentralizer A U L`. -/
theorem detected_sylowFixedInvolution [Finite G]
    {K : GroupClass} {T : Sylow 2 G} {M : Subgroup G}
    (h : HypothesisE61 K T M V) (hA : A ∈ obstructionFamily M V)
    (hUV : U ≤ V) (hindex : A.relIndex U = 2)
    (d : DetectedComponent A U V L) :
    Theory.GroupAction.SylowFixedInvolution (actionEmbedding A L)
      ((inducedAutomizer L U).subgroupOf
        (inducedAutomizer L (centralizer (A : Set G)))) := by
  obtain ⟨hcard, hfix⟩ := detected_action_card_and_fixes h hA hUV hindex d
  exact ⟨actionEmbedding_injective A L, inner_le_actionEmbedding_range d.component.1,
    hcard, hfix⟩

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction
