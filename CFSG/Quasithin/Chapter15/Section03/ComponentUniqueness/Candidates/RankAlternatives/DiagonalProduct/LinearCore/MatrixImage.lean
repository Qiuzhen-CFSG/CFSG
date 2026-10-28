module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.ActionLift
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.PRegularLift
public import Theory.GroupTheory.PrimeOrderLift

/-!
# From cubic Borel actions to the linear quotient-action image

The quotient map is the given L → L/O₂(L) → PSL₃(F). A supplied Sylow
subgroup of I restricts to the relatively subnormal component L and maps
to a Sylow subgroup in these same coordinates. Order-three elements lift
through the two-group kernel with unchanged order. Consequently, when the
preimage of a quotient Borel lies in M ∩ L, its order-three generators act
through A = O²(Y₊ ∩ L), using Y₊ = θ(M ∩ I).

The final conditional theorem reduces image generation to three separate
obligations: placement and invariance of the actual Sylow normalizer,
inner-diagonal coverage for the order-three generators of Y₊, and the
concrete cubic Borel calculation. The chosen y, field, equivalence and
compatible matrix are retained. No exponent assumption on Y₊ and no
containment of O₂(Y) in A is used.

These obligations are not asserted here. Their local assembly must use
CharacteristicTwo.LocalData, the actual Sylow subgroup from 15.3.11(1),
and RankTwo.RankTwoShadow with its O_{2,Φ} denominator. Both even-exponent
PSL₃ fields and the central-two-cover field of order four still require
that assembly. This module does not establish the source result alone.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), final
paragraph of 15.3.37, printed p.1135, with 15.3.11(6). The cubic Borel
calculation uses the concrete matrix groups, not a later containment
from 15.3.38--40.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore.MatrixImage
variable {G H : Type*} [Group G] [Group H]

/-- The quotient homomorphism in the fixed model coordinates. -/
def quotientMap {L : Subgroup G} (e : (L ⧸ pCore 2 L) ≃* H) : L →* H :=
  e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

theorem quotientMap_surjective {L : Subgroup G} (e : (L ⧸ pCore 2 L) ≃* H) :
    Function.Surjective (quotientMap e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem quotientMap_ker {L : Subgroup G} (e : (L ⧸ pCore 2 L) ≃* H) :
    (quotientMap e).ker = pCore 2 L := by
  ext x
  change e (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ x ∈ pCore 2 L
  rw [map_eq_one_iff e e.injective]
  exact QuotientGroup.eq_one_iff _

/-- The action of an element of the component is its literal inner action. -/
theorem quotientAction_on_component {Yplus L : Subgroup G}
    (hn : Yplus ≤ normalizer (L : Set G)) (e : (L ⧸ pCore 2 L) ≃* H)
    (x : Yplus) (hx : (x : G) ∈ L) :
    quotientAction hn e x = MulAut.conj (quotientMap e ⟨x, hx⟩) := by
  ext z
  obtain ⟨l, rfl⟩ := quotientMap_surjective e z
  change quotientAction hn e x (e (QuotientGroup.mk' (pCore 2 L) l)) =
    quotientMap e ⟨x, hx⟩ * quotientMap e l * (quotientMap e ⟨x, hx⟩)⁻¹
  rw [quotientAction_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

variable [Finite G]

/-- The supplied local Sylow, restricted to L and mapped through the fixed quotient. -/
theorem quotient_sylow {I L S : Subgroup G} (hLI : L ≤ I)
    (hL : (L.subgroupOf I).IsSubnormal) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = S)
    (e : (L ⧸ pCore 2 L) ≃* H) :
    ∃ T : Sylow 2 H, (T : Subgroup H) = (S.subgroupOf L).map (quotientMap e) := by
  obtain ⟨Q, hQ⟩ := P.exists_subgroupOf_eq_of_subnormal (L.subgroupOf I) hL
  let eL := subgroupOfEquivOfLe hLI
  let R := Q.mapSurjective (f := eL.toMonoidHom) eL.surjective
  have hR : (R : Subgroup L) = S.subgroupOf L := by
    change (Q : Subgroup (L.subgroupOf I)).map eL.toMonoidHom = _
    rw [hQ, ← hP]
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.val, ha, rfl⟩
    · rintro ⟨a, ha, he⟩
      refine ⟨⟨a, ?_⟩, ha, ?_⟩
      · change (a : G) ∈ L
        change (a : G) = (x : G) at he
        exact he.symm ▸ x.property
      · exact Subtype.ext he
  refine ⟨R.mapSurjective (quotientMap_surjective e), ?_⟩
  change (R : Subgroup L).map (quotientMap e) = _
  rw [hR]

/-- A two-group kernel preserves the order of an odd-order lift. -/
theorem order_three_lift {L : Subgroup G} (e : (L ⧸ pCore 2 L) ≃* H)
    (z : H) (hz : orderOf z = 3) :
    ∃ l : L, quotientMap e l = z ∧ orderOf l = 3 := by
  obtain ⟨l, hl, he⟩ := (quotientMap e).exists_pRegular_lift
    (quotientMap_surjective e) 2 Nat.prime_two z (by rw [hz]; decide)
  refine ⟨l, he, ?_⟩
  have ho := (quotientMap e).orderOf_map_eq_of_coprime_of_isPGroup_ker
    (quotientMap_ker e ▸ pCore_isPGroup) l (Nat.prime_two.coprime_iff_not_dvd.mpr hl)
  exact ho.symm.trans (he ▸ hz)

/-- Order-three elements of the intersection lie in its two-residual. -/
theorem order_three_mem_componentPart {Yplus L : Subgroup G} {x : G}
    (hxY : x ∈ Yplus) (hxL : x ∈ L) (hx : orderOf x = 3) :
    x ∈ componentPart Yplus L := by
  rw [componentPart, ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
  refine ⟨⟨x, hxY, hxL⟩, mem_pResidual_of_orderOf_coprime ?_, rfl⟩
  have ho : orderOf (⟨x, hxY, hxL⟩ : (Yplus ⊓ L : Subgroup G)) = 3 :=
    (orderOf_injective (Yplus ⊓ L).subtype (Yplus ⊓ L).subtype_injective _).symm.trans hx
  exact ho ▸ (show Nat.Coprime 2 3 by decide)

/-- Lift every order-three Borel generator into the actual component residual. -/
theorem inner_theta_le_component_image {Yplus M I L : Subgroup G}
    (hθ : theta (M ⊓ I) = Yplus) (hLI : L ≤ I)
    (hn : Yplus ≤ normalizer (L : Set G)) (e : (L ⧸ pCore 2 L) ≃* H)
    (B : Subgroup H) (hB : B.comap (quotientMap e) ≤ M.subgroupOf L) :
    (theta B).map MulAut.conj ≤
      ((componentPart Yplus L).subgroupOf Yplus).map (quotientAction hn e) := by
  rw [map_le_iff_le_comap]
  apply (closure_le _).mpr
  rintro z ⟨hzB, hz3⟩
  obtain ⟨l, hl, hl3⟩ := order_three_lift e z hz3
  have hlM : (l : G) ∈ M := hB (show quotientMap e l ∈ B from hl ▸ hzB)
  have hlG : orderOf (l : G) = 3 := (Subgroup.orderOf_coe l).trans hl3
  have hlY : (l : G) ∈ Yplus := hθ ▸ subset_closure ⟨⟨hlM, hLI l.property⟩, hlG⟩
  refine ⟨⟨l, hlY⟩, order_three_mem_componentPart hlY l.property hlG, ?_⟩
  rw [quotientAction_on_component hn e _ l.property]
  exact congrArg MulAut.conj hl

omit [Finite G] in
private theorem range_le_of_theta_generators {Yplus M : Subgroup G}
    (hθ : theta M = Yplus) (f : Yplus →* H) (D : Subgroup H)
    (hgen : ∀ x : Yplus, orderOf x = 3 → f x ∈ D) : f.range ≤ D := by
  have hY : Yplus ≤ (D.comap f).map Yplus.subtype := by
    calc
      Yplus = theta M := hθ.symm
      _ ≤ (D.comap f).map Yplus.subtype := ?_
    apply (closure_le _).mpr
    rintro x ⟨hxM, hx3⟩
    have hxY : x ∈ Yplus := hθ ▸ subset_closure ⟨hxM, hx3⟩
    refine ⟨⟨x, hxY⟩, hgen _ ?_, rfl⟩
    simpa only [Subgroup.orderOf_mk] using hx3
  rintro _ ⟨x, rfl⟩
  obtain ⟨a, ha, he⟩ := hY x.property
  have he' : a = x := Subtype.ext he
  exact he' ▸ ha

/-- The placement obligation in the supplied quotient coordinates. -/
structure BorelPlacement (Yplus S M L : Subgroup G)
    (hn : Yplus ≤ normalizer (L : Set G)) (e : (L ⧸ pCore 2 L) ≃* H) where
  sylow : Sylow 2 H
  sylow_eq : (sylow : Subgroup H) = (S.subgroupOf L).map (quotientMap e)
  preimage_le : (normalizer (sylow : Set H)).comap (quotientMap e) ≤ M.subgroupOf L
  invariant : ∀ x : Yplus,
    (sylow : Subgroup H).map (quotientAction hn e x).toMonoidHom = sylow

/-- Concrete cubic matrix assertion; it does not assume ambient generation. -/
def CubicBorelGeneration (F : Type*) [Field F] : Prop :=
  ∀ (T : Sylow 2 PSL(3,F)) (d₀ g : Matrix.GeneralLinearGroup (Fin 3) F),
    let δ := Matrix.PSL3.OuterSolvable.linearConj F d₀
    let β := Matrix.PSL3.OuterSolvable.linearConj F g
    δ ∉ MulAut.innerSubgroup PSL(3,F) →
    δ ^ 3 = 1 → (T : Subgroup PSL(3,F)).map δ.toMonoidHom = T →
    β ^ 3 = 1 → (T : Subgroup PSL(3,F)).map β.toMonoidHom = T →
    β ∈ (theta (normalizer (T : Set PSL(3,F)))).map MulAut.conj ⊔ zpowers δ

/-- Generation follows from placement and the concrete cubic matrix calculation.
All actions use the original equivalence and the original actor. -/
theorem image_le_of_borel {Yplus S M I L : Subgroup G}
    (hθ : theta (M ⊓ I) = Yplus) (hLI : L ≤ I)
    (hn : Yplus ≤ normalizer (L : Set G))
    {F : Type*} [Field F] (e : (L ⧸ pCore 2 L) ≃* PSL(3,F))
    (y : Yplus) (hy : orderOf y = 3)
    (α : MulAut L) (d₀ : Matrix.GeneralLinearGroup (Fin 3) F)
    (hc : ConjugationOn L y α)
    (ho : Matrix.PSL3.OuterSolvable.linearConj F d₀ ∉ MulAut.innerSubgroup PSL(3,F))
    (he : ∀ x : L, e (QuotientGroup.mk' (pCore 2 L) (α x)) =
      Matrix.PSL3.OuterSolvable.linearConj F d₀ (e (QuotientGroup.mk' (pCore 2 L) x)))
    (b : BorelPlacement Yplus S M L hn e)
    (hlinear : ∀ x : Yplus, orderOf x = 3 →
      quotientAction hn e x ∈ Matrix.PSL3.OuterSolvable.innerDiagonal F)
    (hmodel : CubicBorelGeneration F) :
    (quotientAction hn e).range ≤
      ((componentPart Yplus L).subgroupOf Yplus).map (quotientAction hn e) ⊔
        zpowers (quotientAction hn e y) := by
  have hay := quotientAction_eq_of_compatible hn e y α
    (Matrix.PSL3.OuterSolvable.linearConj F d₀) hc he
  have hycube : (Matrix.PSL3.OuterSolvable.linearConj F d₀) ^ 3 = 1 := by
    have hy3 : y ^ 3 = 1 := hy ▸ pow_orderOf_eq_one y
    rw [← hay, ← map_pow, hy3, map_one]
  apply range_le_of_theta_generators hθ
  intro x hx
  obtain ⟨g, hg⟩ := hlinear x hx
  have hgcube : (Matrix.PSL3.OuterSolvable.linearConj F g) ^ 3 = 1 := by
    have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
    rw [hg, ← map_pow, hx3, map_one]
  have hm := hmodel b.sylow d₀ g ho hycube (hay ▸ b.invariant y)
    hgcube (hg.symm ▸ b.invariant x)
  change Matrix.PSL3.OuterSolvable.linearConj F g ∈
    (theta (normalizer (b.sylow : Set PSL(3,F)))).map MulAut.conj ⊔
      zpowers (Matrix.PSL3.OuterSolvable.linearConj F d₀) at hm
  rw [hg, ← hay] at hm
  exact (sup_le_sup
    (inner_theta_le_component_image hθ hLI hn e _ b.preimage_le) le_rfl) hm

end CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore.MatrixImage
