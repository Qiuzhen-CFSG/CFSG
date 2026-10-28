module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.PlaneApplication
public import Theory.GroupTheory.CentralizerInjectiveImage
public import Theory.SpecificGroups.SymmetricFive.OuterFourIntersection
public import Theory.ElementaryAbelian.EightQuotientRank
public import Theory.Representation.BinaryPermutation.FiveQuadraticActors

/-!
# Cross-actions of two original natural A₅ modules

Both modules lie in the same Sylow subgroup and are normalized by it. A
cross-action with image of order two would have an invariant kernel of order
eight. The original hyperplane-centralizer theorem makes that action trivial.
The elementary rank bound in S₅ therefore makes every nontrivial cross-image
a four-group.

The modules normalize each other, so their mutual commutators lie in their
intersection and are centralized by both. Thus each cross-action is quadratic.
The even four-group acts nonquadratically on the five-point core, so every
nontrivial cross-image is an outer four-group. In particular, these natural
modules cannot directly supply an elementary residual lift of an even four.
The original outside application is in SourceAssembly/NonsolvableCrossModule.

Source inputs: Aschbacher--Smith 13.2.3(1), printed pp.878--879, and the
five-point module calculation used in 12.6.23, p.830. The comparison supports
the unresolved nonsolvable step of 13.2.8(1), p.880; it does not assert it.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ W : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

/-- An invariant centralizer in the original module cannot be a hyperplane. -/
theorem centralizer_intersection_ne_eight
    (hWT : W ≤ (T : Subgroup G))
    (hTW : (T : Subgroup G) ≤ normalizer (W : Set G)) :
    Nat.card (V ⊓ centralizer (W : Set G) : Subgroup G) ≠ 8 := by
  intro hc
  let C := V ⊓ centralizer (W : Set G)
  have hn : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf d.flag.T_normalizes
      (hTW.trans (normalizer_le_normalizer_centralizer W))).trans
        inf_normalizer_le_normalizer_inf
  have hWV : W ≤ centralizer (V : Set G) := by
    apply (le_inf (hWT.trans d.flag.T_normalizes)
      (le_centralizer_iff.mp (show C ≤ centralizer (W : Set G) from inf_le_right))).trans
    exact (centralizer_third d.flag C inf_le_left hc hn).le
  have he : C = V := inf_eq_left.mpr (le_centralizer_iff.mp hWV)
  change Nat.card C = 8 at hc
  rw [he,d.module_card] at hc
  omega

/-- Every nontrivial cross-action in S₅ has image of order four. -/
theorem cross_action_card
    {J : Subgroup G} (hVJ : V ≤ J) (hWJ : W ≤ J)
    (hWT : W ≤ (T : Subgroup G))
    (hTW : (T : Subgroup G) ≤ normalizer (W : Set G))
    (q : J →* Equiv.Perm (Fin 5))
    (hk : q.ker = centralizer (W.subgroupOf J : Set J))
    (hm : ¬ V ≤ centralizer (W : Set G)) :
    Nat.card ((V.subgroupOf J).map q) = 4 := by
  let A := V.subgroupOf J
  let := d.elementary
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hVJ
  let : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
  obtain ⟨P,hP⟩ := (IsElementaryAbelian.isPGroup 2 (A.map q)).exists_le_sylow
  have hb := Theory.SpecificGroups.SymmetricFive.OuterFourIntersection.elementary_card_le_four
    P (A.map q) hP
  have hmapped : (A ⊓ q.ker).map J.subtype = V ⊓ centralizer (W : Set G) := by
    rw [hk,← map_inf_centralizer_of_injective J.subtype J.subtype_injective,
      map_subgroupOf_eq_of_le hWJ,map_subgroupOf_eq_of_le hVJ]
  have hC : Nat.card (A ⊓ q.ker : Subgroup J) =
      Nat.card (V ⊓ centralizer (W : Set G) : Subgroup G) :=
    (card_map_of_injective J.subtype_injective).symm.trans (congrArg (fun X : Subgroup G => Nat.card X) hmapped)
  have hprod := IsElementaryAbelian.card_inf_ker_mul_card_map A q
  rw [hC, Nat.card_congr (subgroupOfEquivOfLe hVJ).toEquiv,d.module_card] at hprod
  have hnot8 := d.centralizer_intersection_ne_eight hWT hTW
  have hnot16 : Nat.card (V ⊓ centralizer (W : Set G) : Subgroup G) ≠ 16 := by
    intro hc
    have he : V ⊓ centralizer (W : Set G) = V :=
      eq_of_le_of_card_ge inf_le_left (by rw [hc,d.module_card])
    exact hm (he.symm.le.trans inf_le_right)
  generalize Nat.card (A.map q) = n at hb hprod ⊢
  interval_cases n <;> omega

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context

namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
open Representation Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ K W W₁ W₂ W₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
include d e

/-- Mutual normalization and elementary abelianness make the actual cross-action quadratic. -/
theorem cross_action_quadratic
    {J : Subgroup G} (q : J →* Equiv.Perm (Fin 5))
    (he : ∀ j : J, ∀ w : BinaryPermutation.core (Fin 5),
      j.val * e.flag.module.map (Multiplicative.ofAdd w) * j.val⁻¹ =
        e.flag.module.map (Multiplicative.ofAdd
          (BinaryPermutation.coreRepresentation (Fin 5) (q j) w))) :
    IsQuadratic (BinaryPermutation.coreRepresentation (Fin 5)) ((V.subgroupOf J).map q) := by
  rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ w
  let := d.elementary
  let x := e.flag.module.map (Multiplicative.ofAdd w)
  have hx : x ∈ W := e.flag.module.range_eq.le ⟨Multiplicative.ofAdd w,rfl⟩
  have hc : ⁅b.val,x⁆ ∈ V :=
    (le_normalizer_iff_commutator_le_left.mp
      (e.chosen.le_sylow.trans d.flag.T_normalizes)) (commutator_mem_commutator hb hx)
  have hd : e.flag.module.map (Multiplicative.ofAdd
      (BinaryPermutation.coreRepresentation (Fin 5) (q b) w - w)) = ⁅b.val,x⁆ := by
    change e.flag.module.map (Multiplicative.ofAdd
      (BinaryPermutation.coreRepresentation (Fin 5) (q b) w) / Multiplicative.ofAdd w) = _
    rw [map_div,←he b w]
    simp only [div_eq_mul_inv,commutatorElement_def,x]
  apply e.flag.module.injective
  change e.flag.module.map (Multiplicative.ofAdd
      (BinaryPermutation.coreRepresentation (Fin 5) (q a)
        (BinaryPermutation.coreRepresentation (Fin 5) (q b) w - w))) = _
  calc
    _ = a.val * e.flag.module.map (Multiplicative.ofAdd
        (BinaryPermutation.coreRepresentation (Fin 5) (q b) w - w)) * a.val⁻¹ := (he a _).symm
    _ = a.val * ⁅b.val,x⁆ * a.val⁻¹ := by rw [hd]
    _ = ⁅b.val,x⁆ := mul_inv_eq_iff_eq_mul.mpr
      ((mem_centralizer_iff.mp ((le_centralizer V) ha) _ hc).symm)
    _ = _ := hd.symm


/-- A nontrivial cross-action is an outer four-group, not the even Sylow four. -/
theorem cross_action_outer_four
    {J : Subgroup G} (hVJ : V ≤ J) (hWJ : W ≤ J)
    (q : J →* Equiv.Perm (Fin 5))
    (hk : q.ker = centralizer (W.subgroupOf J : Set J))
    (he : ∀ j : J, ∀ w : BinaryPermutation.core (Fin 5),
      j.val * e.flag.module.map (Multiplicative.ofAdd w) * j.val⁻¹ =
        e.flag.module.map (Multiplicative.ofAdd
          (BinaryPermutation.coreRepresentation (Fin 5) (q j) w)))
    (hm : ¬ V ≤ centralizer (W : Set G)) :
    Nat.card ((V.subgroupOf J).map q) = 4 ∧
      ¬ (V.subgroupOf J).map q ≤ alternatingGroup (Fin 5) := by
  have hc := d.cross_action_card hVJ hWJ e.chosen.le_sylow e.flag.T_normalizes q hk hm
  refine ⟨hc,?_⟩
  intro hA
  let A := (V.subgroupOf J).map q
  let B := A.subgroupOf (alternatingGroup (Fin 5))
  let := d.elementary
  let : IsElementaryAbelian 2 (V.subgroupOf J) := IsElementaryAbelian.subgroupOf hVJ
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map q
  have hquad := d.cross_action_quadratic e q he
  have hquadB : IsQuadratic (BinaryPermutation.alternatingCoreRepresentation (Fin 5)) B :=
    fun a ha b hb w => hquad a.val ha b.val hb w
  have hbound := BinaryPermutation.FiveQuadraticActors.card_le_two_of_quadratic B
    (IsElementaryAbelian.isPGroup 2 A).comap_subtype hquadB
  rw [Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv,hc] at hbound
  omega

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
