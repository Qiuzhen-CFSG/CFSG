module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.Basic

/-!
# The faithful action on the two-residual

The quotient H* = N_G(L)/C_G(L) uses relative normality. Ambient subgroups
and elements have specified images under its canonical homomorphism.
Restriction to L has kernel Z(L), so L* is canonically L/Z(L). A subgroup
centralizing D = O²(C_L(r)) maps into the actual C_H*(D*); disjointness
from C_G(L) makes that map injective.

These are the quotient transports used in all three cases of the order
argument. No centralizer classification is assumed or asserted here.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 16.4.1 and proof of 16.4.9(1), printed pp.1183 and 1189.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections.OrderTwo
open OuterResidual
variable {G : Type*} [Group G]

/-- The source quotient H*; its denominator is normal inside N_G(L). -/
abbrev ActionQuotient (L : Subgroup G) := componentActionQuotient L

/-- The canonical homomorphism H → H*. -/
def quotientMap (L : Subgroup G) : normalizer (L : Set G) →* ActionQuotient L :=
  QuotientGroup.mk' ((centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)))

/-- The image of an ambient subgroup in H*, after restricting to H. -/
def actionImage (L A : Subgroup G) : Subgroup (ActionQuotient L) :=
  (A.subgroupOf (normalizer (L : Set G))).map (quotientMap L)

/-- Containment of ambient subgroups preserves their images in H*. -/
theorem actionImage_mono (L : Subgroup G) {A B : Subgroup G} (hAB : A ≤ B) :
    actionImage L A ≤ actionImage L B :=
  map_mono (fun _ hx => hAB hx)

/-- The image of a specified element of N_G(L). -/
def actionElement (L : Subgroup G) (a : G) (ha : a ∈ normalizer (L : Set G)) :
    ActionQuotient L := quotientMap L ⟨a, ha⟩

/-- Restrict H → H* to a subgroup known to lie in H. -/
def actionMap {L A : Subgroup G} (hA : A ≤ normalizer (L : Set G)) :
    A →* ActionQuotient L := (quotientMap L).comp (inclusion hA)

/-- The full centralizer C_H*(D*) for D = O²(C_L(r)). -/
def residualCentralizer (L : Subgroup G) (r : G) : Subgroup (ActionQuotient L) :=
  centralizer (actionImage L (involutionResidual L r) : Set (ActionQuotient L))

/-- An element of A lying in H gives an element of A*. -/
theorem mem_actionImage {L A : Subgroup G} {a : G}
    (ha : a ∈ normalizer (L : Set G)) (haA : a ∈ A) :
    actionElement L a ha ∈ actionImage L A := ⟨⟨a, ha⟩, haA, rfl⟩

/-- Disjointness from K makes the action quotient faithful on A. -/
theorem actionMap_injective {L A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G)) (hfaith : Disjoint A (centralizer (L : Set G))) :
    Function.Injective (actionMap hA) := by
  apply (injective_iff_map_eq_one (actionMap hA)).mpr
  intro a ha
  have haK : (a : G) ∈ centralizer (L : Set G) :=
    (QuotientGroup.eq_one_iff (⟨a, hA a.property⟩ : normalizer (L : Set G))).mp ha
  exact Subtype.ext (Subgroup.disjoint_def.mp hfaith a.property haK)

/-- The restricted homomorphism has exactly the specified image A*. -/
theorem actionMap_range {L A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G)) :
    (actionMap hA).range = actionImage L A := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨inclusion hA a, a.property, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

/-- The kernel on L is its own center, not all of O₂(H). -/
theorem componentActionMap_ker (L : Subgroup G) :
    (actionMap (le_normalizer : L ≤ normalizer (L : Set G))).ker = center L := by
  ext x
  change quotientMap L ⟨x, le_normalizer x.property⟩ = 1 ↔ x ∈ center L
  rw [show quotientMap L ⟨x, le_normalizer x.property⟩ = 1 ↔
    (x : G) ∈ centralizer (L : Set G) from QuotientGroup.eq_one_iff _]
  simp only [mem_centralizer_iff, mem_center_iff]
  constructor
  · intro hx y
    exact Subtype.ext (hx y y.property)
  · intro hx y hy
    exact congrArg Subtype.val (hx ⟨y, hy⟩)

/-- Identify L/Z(L) with its actual image L* inside H*. -/
noncomputable def centerQuotientEquivActionImage (L : Subgroup G) :
    (L ⧸ center L) ≃* actionImage L L :=
  (QuotientGroup.quotientMulEquivOfEq (componentActionMap_ker L).symm).trans
    ((QuotientGroup.quotientKerEquivRange (actionMap (le_normalizer (H := L)))).trans
      (MulEquiv.subgroupCongr (actionMap_range _)))

/-- Centralizing D implies that the image centralizes D*. -/
theorem actionMap_mem_residualCentralizer {L A : Subgroup G} {r : G}
    (hA : A ≤ normalizer (L : Set G))
    (hc : A ≤ centralizer (involutionResidual L r : Set G)) (a : A) :
    actionMap hA a ∈ residualCentralizer L r := by
  apply mem_centralizer_iff.mpr
  rintro d ⟨x, hx, rfl⟩
  have he : x * inclusion hA a = inclusion hA a * x :=
    Subtype.ext (mem_centralizer_iff.mp (hc a.property) x hx)
  exact congrArg (quotientMap L) he

/-- The actual action homomorphism into the residual centralizer. -/
def residualCentralizerMap {L A : Subgroup G} {r : G}
    (hA : A ≤ normalizer (L : Set G))
    (hc : A ≤ centralizer (involutionResidual L r : Set G)) :
    A →* residualCentralizer L r :=
  (actionMap hA).codRestrict _ (actionMap_mem_residualCentralizer hA hc)

/-- The residual-centralizer homomorphism is faithful when A ∩ K = 1. -/
theorem residualCentralizerMap_injective {L A : Subgroup G} {r : G}
    (hA : A ≤ normalizer (L : Set G))
    (hc : A ≤ centralizer (involutionResidual L r : Set G))
    (hfaith : Disjoint A (centralizer (L : Set G))) :
    Function.Injective (residualCentralizerMap hA hc) := by
  intro a b hab
  exact actionMap_injective hA hfaith (congrArg Subtype.val hab)

/-- A nontrivial abelian odd residual image prevents a full centralizer of
order two. The graph-field E₉ row therefore calls for a bound on its two-part,
not the literal full-centralizer equality printed in case (I). -/
theorem residualCentralizer_card_ne_two_of_odd_image [Finite G]
    {L : Subgroup G} {r : G}
    (hcomm : IsMulCommutative (actionImage L (involutionResidual L r)))
    (hodd : Odd (Nat.card (actionImage L (involutionResidual L r))))
    (hne : actionImage L (involutionResidual L r) ≠ ⊥) :
    Nat.card (residualCentralizer L r) ≠ 2 := by
  intro hc
  have hd := card_dvd_of_le (le_centralizer_iff_isMulCommutative.mpr hcomm)
  change Nat.card (actionImage L (involutionResidual L r)) ∣
    Nat.card (residualCentralizer L r) at hd
  rw [hc] at hd
  rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with hcard | hcard
  · exact hne ((actionImage L (involutionResidual L r)).eq_bot_iff_card.mpr hcard)
  · rw [hcard] at hodd
    norm_num at hodd

end CFSG.Quasithin.Chapter16.Intersections.OrderTwo
