module
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Contracts
public import CFSG.Quasithin.Chapter16.Section01To02.LiePreliminaries.Basic

/-!
# Central quotient transports for the residual comparison

The ambient residual O²(C_L(t)), restricted to L, is the fixed two-residual
of the actual normalizer action. For a quasisimple component with trivial
odd core, its central quotient image is isomorphic to the two-residual of
the induced fixed subgroup in any specified model. The proof uses the
surjective fixed-residual theorem for a central two-kernel; it does not
assert that the whole fixed subgroup lifts.

Solvability is unchanged by this central image, allowing comparisons of the
same subgroup through two different component quotients without identifying
their covering kernels. These transports support the table comparison in
Aschbacher–Smith 16.4.11(2), combined manuscript (1 March 2004), printed p.1193.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison
open Subgroup Theory.GroupTheory LiePreliminaries
variable {G : Type*} [Group G] {L : Subgroup G} {t : G}

/-- The actual normalizer action of an ambient element on the component. -/
abbrev action (ht : t ∈ normalizer (L : Set G)) : MulAut L :=
  L.normalizerMonoidHom ⟨t, ht⟩

/-- Fixed points of the normalizer action are exactly the ambient centralizer. -/
noncomputable def fixedCentralizerEquiv (ht : t ∈ normalizer (L : Set G)) :
    (action ht).fixedSubgroup ≃* (L ⊓ centralizer ({t} : Set G) : Subgroup G) where
  toFun x := ⟨x.val, x.val.property, mem_centralizer_singleton_iff.mpr (by
    have hx := congrArg Subtype.val ((MulAut.mem_fixedSubgroup _ _).mp x.property)
    change t * (x.val : G) * t⁻¹ = x.val at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm)⟩
  invFun x := ⟨⟨x, x.property.1⟩, (MulAut.mem_fixedSubgroup _ _).mpr (by
    apply Subtype.ext
    change t * (x : G) * t⁻¹ = x
    rw [← mem_centralizer_singleton_iff.mp x.property.2, mul_inv_cancel_right])⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Ambient and intrinsic two-residuals agree under the subgroup identification. -/
theorem residual_subgroupOf_eq (ht : t ∈ normalizer (L : Set G)) :
    (residual L t).subgroupOf L = fixedTwoResidual L (action ht) := by
  let e := fixedCentralizerEquiv ht
  have hm := map_pResidual 2 e.symm
  ext x
  constructor
  · rintro ⟨c, hc, he⟩
    refine ⟨e.symm c, hm ▸ (mem_map.mpr ⟨c, hc, rfl⟩), ?_⟩
    exact Subtype.ext he
  · rintro ⟨c, hc, he⟩
    refine ⟨e c, (map_pResidual 2 e) ▸ (mem_map.mpr ⟨c, hc, rfl⟩), ?_⟩
    exact congrArg Subtype.val he

/-- Restriction of the actual quotient map to a subgroup of the component. -/
def centralImageMap {X : Subgroup G} (hXL : X ≤ L) : X →* centralImage L X where
  toFun x := ⟨QuotientGroup.mk' (center L) ⟨x, hXL x.property⟩,
    ⟨⟨x, hXL x.property⟩, x.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (QuotientGroup.mk' (center L))
      (⟨x, hXL x.property⟩ : L) (⟨y, hXL y.property⟩ : L)

theorem centralImageMap_surjective {X : Subgroup G} (hXL : X ≤ L) :
    Function.Surjective (centralImageMap hXL) := by
  rintro ⟨q, x, hx, rfl⟩
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  change QuotientGroup.mk' (center L) ⟨x.val, _⟩ = QuotientGroup.mk' (center L) x
  congr

/-- A central kernel cannot hide nonsolvability. This also compares two
images of the same residual in different component quotients. -/
theorem centralImage_solvable_iff {X : Subgroup G} (hXL : X ≤ L) :
    Group.IsSolvable (centralImage L X) ↔ Group.IsSolvable X := by
  let f := centralImageMap hXL
  constructor
  · intro h
    let := h
    let : Group.IsSolvable f.ker := Group.isSolvable_of_comm (by
      intro x y
      have hx : (⟨x.val, hXL x.val.property⟩ : L) ∈ center L := by
        apply (QuotientGroup.eq_one_iff _).mp
        change QuotientGroup.mk' (center L) ⟨x.val, hXL x.val.property⟩ = 1
        have he := congrArg Subtype.val x.property
        simpa only [f, centralImageMap, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_one] using he
      apply Subtype.ext
      apply Subtype.ext
      change (x.val.val : G) * (y.val.val : G) = (y.val.val : G) * (x.val.val : G)
      exact congrArg Subtype.val
        (mem_center_iff.mp hx ⟨y.val, hXL y.val.property⟩).symm)
    exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by simp)
  · intro h
    let := h
    exact Group.isSolvable_of_surjective (centralImageMap_surjective hXL)

/-- Isomorphisms of components induce actual isomorphisms of their central quotients. -/
noncomputable def centralQuotientCongr {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) : (H ⧸ center H) ≃* (K ⧸ center K) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (centerCongr e ⟨x, hx⟩).property
    · intro x hx
      exact ⟨e.symm x, ((centerCongr e).symm ⟨x, hx⟩).property,
        e.apply_symm_apply x⟩)

variable [Finite G]

/-- The precise image equality in a specified central quotient model. -/
theorem centralImage_model_map [IsQuasisimple L] (hodd : pPrimeCore 2 L = ⊥)
    {S : Type*} [Group S] (e : (L ⧸ center L) ≃* S)
    (ht : t ∈ normalizer (L : Set G)) :
    (centralImage L (residual L t)).map e.toMonoidHom =
      fixedTwoResidual S (MulAut.centralQuotientAction e (action ht)) := by
  rw [centralImage, residual_subgroupOf_eq ht, map_map]
  exact map_fixedTwoResidual hodd e (action ht)

/-- Identify the actual central image with the model fixed two-residual. -/
noncomputable def centralImageModelEquiv [IsQuasisimple L]
    (hodd : pPrimeCore 2 L = ⊥) {S : Type*} [Group S]
    (e : (L ⧸ center L) ≃* S) (ht : t ∈ normalizer (L : Set G)) :
    centralImage L (residual L t) ≃*
      pResidual 2 (MulAut.centralQuotientAction e (action ht)).fixedSubgroup :=
  ((e.subgroupMap _).trans (MulEquiv.subgroupCongr
    (centralImage_model_map hodd e ht))).trans
    ((pResidual 2 (MulAut.centralQuotientAction e (action ht)).fixedSubgroup).equivMapOfInjective
      _ (Subgroup.subtype_injective _)).symm

variable {T : Sylow 2 G} {z g r : G} {R : Subgroup G}

/-- (E1) passes to the centralizer component by subnormality. -/
theorem component_oddCore (d : Contrary T z L g R r) : pPrimeCore 2 L = ⊥ := by
  have hcore := Subgroup.IsSubnormal.pPrimeCore_eq_bot (d.evenType.oddCore z d.setup.involution)
    (L.subgroupOf (involutionCentralizer z)) d.setup.component.2.1
  have hm := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe d.setup.component.1)
  simpa only [hcore, Subgroup.map_bot] using hm.symm

/-- The odd-core calculation also holds in the conjugate component. -/
theorem conjugate_oddCore (d : Contrary T z L g R r) :
    pPrimeCore 2 (L.conjBy g) = ⊥ := by
  let e : L ≃* L.conjBy g := (MulAut.conj g).subgroupMap L
  have hm := pPrimeCore_map_iso 2 e
  simpa only [component_oddCore d, Subgroup.map_bot] using hm.symm

omit [Finite G] in
/-- Relative normality passes to images in one fixed component quotient. -/
theorem centralImage_normal {L X Y : Subgroup G} (hXL : X ≤ L) (hYX : Y ≤ X)
    (hn : (Y.subgroupOf X).Normal) :
    ((centralImage L Y).subgroupOf (centralImage L X)).Normal := by
  have he : (Y.subgroupOf X).map (centralImageMap hXL) =
      (centralImage L Y).subgroupOf (centralImage L X) := by
    ext x
    constructor
    · rintro ⟨y, hy, he⟩
      refine ⟨⟨y, hXL y.property⟩, hy, ?_⟩
      exact congrArg Subtype.val he
    · rintro ⟨y, hy, he⟩
      refine ⟨⟨y, hYX hy⟩, hy, ?_⟩
      apply Subtype.ext
      exact he
  rw [← he]
  exact hn.map _ (centralImageMap_surjective hXL)

omit [Finite G] in
/-- Images through different central kernels have the same solvability. -/
theorem cross_centralImage_solvable_iff {L M X : Subgroup G}
    (hXL : X ≤ L) (hXM : X ≤ M) :
    Group.IsSolvable (centralImage L X) ↔ Group.IsSolvable (centralImage M X) :=
  (centralImage_solvable_iff hXL).trans (centralImage_solvable_iff hXM).symm

/-- The outer residual image is normal in the inner residual image when both
are formed in L/Z(L); this does not identify it with the image in L′/Z(L′). -/
theorem contrary_normal_image (d : Contrary T z L g R r) :
    ((centralImage L (residual (L.conjBy g) z)).subgroupOf
      (centralImage L (residual L r))).Normal :=
  centralImage_normal ((residual_le L r).trans inf_le_left)
    d.residual_normal.1 d.residual_normal.2.1

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison
