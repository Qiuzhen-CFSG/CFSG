module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreAction
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointPairCommutator

/-!
# Three actual involutory lifts of the binary plane shears

Coordinates on the original seed define its two independent plane shears.
The point-core displacement theorem produces involutions for these shears
and their product, in the three corresponding actual point cores. Their
full seed actions identify the two required kernel elements, while the
distinct-point calculation gives a square-one commutator.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.HigmanSims.BinaryPlane

abbrev Model := Multiplicative (Fin 3 → ZMod 2)
def e0 : Model := Multiplicative.ofAdd ![1, 0, 0]
def e1 : Model := Multiplicative.ofAdd ![0, 1, 0]
def e2 : Model := Multiplicative.ofAdd ![0, 0, 1]

def alphaFun (x : Model) : Model :=
  Multiplicative.ofAdd ![x.toAdd 0 + x.toAdd 2, x.toAdd 1, x.toAdd 2]
def betaFun (x : Model) : Model :=
  Multiplicative.ofAdd ![x.toAdd 0, x.toAdd 1 + x.toAdd 2, x.toAdd 2]

/-- The shear adding the third binary coordinate to the first. -/
def alpha : MulAut Model where
  toFun := alphaFun
  invFun := alphaFun
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

/-- The shear adding the third binary coordinate to the second. -/
def beta : MulAut Model where
  toFun := betaFun
  invFun := betaFun
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

def plane : Subgroup Model where
  carrier := {x | x.toAdd 2 = 0}
  one_mem' := rfl
  mul_mem' := by intro a b ha hb; change a.toAdd 2 + b.toAdd 2 = 0; rw [ha, hb, add_zero]
  inv_mem' := by intro a ha; change -(a.toAdd 2) = 0; rw [ha, neg_zero]

variable {G : Type*} [Group G] {V : Subgroup G}

/-- The first shear transported through the given coordinates on the actual seed. -/
def alphaAt (c : V ≃* Model) : MulAut V := (MulAut.congr c).symm alpha
/-- The second shear transported through the same actual seed coordinates. -/
def betaAt (c : V ≃* Model) : MulAut V := (MulAut.congr c).symm beta
/-- The literal plane of the original seed cut out by the third coordinate. -/
def planeAt (c : V ≃* Model) : Subgroup G :=
  (plane.comap c.toMonoidHom).map V.subtype

theorem alphaAt_apply (c : V ≃* Model) (x : V) :
    c (alphaAt c x) = alpha (c x) := c.apply_symm_apply _
theorem betaAt_apply (c : V ≃* Model) (x : V) :
    c (betaAt c x) = beta (c x) := c.apply_symm_apply _

/-- All lift data refer to the same full normalizer, seed, point cores and plane. -/
structure LiftData (c : V ≃* Model) where
  a : normalizer (V : Set G)
  b : normalizer (V : Set G)
  t : normalizer (V : Set G)
  a_core : (a : G) ∈ (involutionCentralizer ((c.symm e0 : V) : G)).pCoreIn 2
  b_core : (b : G) ∈ (involutionCentralizer ((c.symm e1 : V) : G)).pCoreIn 2
  t_core : (t : G) ∈ (involutionCentralizer ((c.symm (e0 * e1) : V) : G)).pCoreIn 2
  a_square : a ^ 2 = 1
  b_square : b ^ 2 = 1
  t_square : t ^ 2 = 1
  a_action : V.normalizerMonoidHom a = alphaAt c
  b_action : V.normalizerMonoidHom b = betaAt c
  t_action : V.normalizerMonoidHom t = alphaAt c * betaAt c
  a_plane : (a : G) ∈ centralizer (planeAt c : Set G)
  b_plane : (b : G) ∈ centralizer (planeAt c : Set G)
  t_plane : (t : G) ∈ centralizer (planeAt c : Set G)
  commutator_square : ⁅a, b⁆ ^ 2 = 1
  commutator_core : ⁅a, b⁆ ∈ pCore 2 (normalizer (V : Set G))
  product_core : t * (a * b)⁻¹ ∈ pCore 2 (normalizer (V : Set G))

private theorem model_orders : orderOf alpha = 2 ∧ orderOf beta = 2 ∧
    orderOf (alpha * beta) = 2 := by
  have order (a : MulAut Model) (ha : a ^ 2 = 1) (hne : a e2 ≠ e2) : orderOf a = 2 := by
    apply orderOf_eq_prime_iff.mpr
    exact ⟨ha, fun he => hne (by rw [he]; rfl)⟩
  refine ⟨order alpha ?_ ?_, order beta ?_ ?_, order (alpha * beta) ?_ ?_⟩
  · apply MulEquiv.ext; intro x
    exact (by decide +kernel : ∀ x : Model, alpha (alpha x) = x) x
  · decide +kernel
  · apply MulEquiv.ext; intro x
    exact (by decide +kernel : ∀ x : Model, beta (beta x) = x) x
  · decide +kernel
  · apply MulEquiv.ext; intro x
    exact (by decide +kernel : ∀ x : Model, alpha (beta (alpha (beta x))) = x) x
  · decide +kernel

private theorem model_commute : Commute alpha beta := by
  apply MulEquiv.ext
  exact (by decide +kernel : ∀ x : Model, alpha (beta x) = beta (alpha x))

private theorem model_displacements : alpha e2 * e2⁻¹ = e0 ∧ beta e2 * e2⁻¹ = e1 ∧
    (alpha * beta) e2 * e2⁻¹ = e0 * e1 := by decide +kernel

private theorem model_fixed : ∀ x : Model, x.toAdd 2 = 0 → alpha x = x ∧ beta x = x := by
  decide +kernel

theorem alpha_ne_one : alpha ≠ 1 := by
  intro he
  exact (by decide +kernel : alpha e2 ≠ e2) (DFunLike.congr_fun he e2)

theorem beta_ne_one : beta ≠ 1 := by
  intro he
  exact (by decide +kernel : beta e2 ≠ e2) (DFunLike.congr_fun he e2)

theorem alpha_ne_beta : alpha ≠ beta := by
  intro he
  exact (by decide +kernel : alpha e2 ≠ beta e2) (DFunLike.congr_fun he e2)

theorem alphaAt_ne_one (c : V ≃* Model) : alphaAt c ≠ 1 := by
  intro he
  apply alpha_ne_one
  exact (MulAut.congr c).symm.injective (he.trans (MulAut.congr c).symm.map_one.symm)

theorem betaAt_ne_one (c : V ≃* Model) : betaAt c ≠ 1 := by
  intro he
  apply beta_ne_one
  exact (MulAut.congr c).symm.injective (he.trans (MulAut.congr c).symm.map_one.symm)

theorem alphaAt_ne_betaAt (c : V ≃* Model) : alphaAt c ≠ betaAt c := by
  intro he
  exact alpha_ne_beta ((MulAut.congr c).symm.injective he)

theorem plane_card : Nat.card plane = 4 := by
  let : DecidablePred (· ∈ plane) := fun x => inferInstanceAs (Decidable (x.toAdd 2 = 0))
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem plane_elementary : IsElementaryAbelian 2 plane where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
    Subtype.ext ((by decide +kernel : ∀ y : Model, y ^ 2 = 1) x))

theorem alpha_fixes_plane (x : Model) (hx : x ∈ plane) : alpha x = x := (model_fixed x hx).1
theorem beta_fixes_plane (x : Model) (hx : x ∈ plane) : beta x = x := (model_fixed x hx).2

theorem planeAt_le (c : V ≃* Model) : planeAt c ≤ V := map_subtype_le _

theorem planeAt_card (c : V ≃* Model) : Nat.card (planeAt c) = 4 := by
  rw [planeAt, card_map_of_injective V.subtype_injective, comap_equiv_eq_map_symm',
    card_map_of_injective c.symm.injective, plane_card]

theorem planeAt_elementary (c : V ≃* Model) : IsElementaryAbelian 2 (planeAt c) := by
  let : IsElementaryAbelian 2 plane := plane_elementary
  rw [planeAt, comap_equiv_eq_map_symm']
  let : IsElementaryAbelian 2 (plane.map c.symm.toMonoidHom) := IsElementaryAbelian.map _
  exact IsElementaryAbelian.map_subtype

private theorem plane_centralized (c : V ≃* Model) (g : normalizer (V : Set G))
    (hg : V.normalizerMonoidHom g = alphaAt c ∨
      V.normalizerMonoidHom g = betaAt c ∨
      V.normalizerMonoidHom g = alphaAt c * betaAt c) :
    (g : G) ∈ centralizer (planeAt c : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  have ha : alphaAt c x = x := c.injective ((alphaAt_apply c x).trans (model_fixed (c x) hx).1)
  have hb : betaAt c x = x := c.injective ((betaAt_apply c x).trans (model_fixed (c x) hx).2)
  have he : V.normalizerMonoidHom g x = x := by
    rcases hg with hg | hg | hg
    · rw [hg]; exact ha
    · rw [hg]; exact hb
    · rw [hg, MulAut.mul_apply, hb, ha]
  exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)).symm

end CFSG.Quasithin.HigmanSims.BinaryPlane

namespace CFSG.Quasithin.HigmanSims
open BinaryPlane
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The exact original HS hypotheses produce all three canonical involutory
plane lifts with their point-core and full seed-action markings. -/
theorem TypeAt.exists_binary_plane_lifts (h : TypeAt z V) (c : V ≃* BinaryPlane.Model) :
    Nonempty (BinaryPlane.LiftData c) := by
  let u := c.symm e0
  let v := c.symm e1
  let w := c.symm e2
  let uv := c.symm (e0 * e1)
  have hu1 : (u : G) ≠ 1 := by
    intro he
    have hh := congrArg c (show u = 1 from Subtype.ext he)
    simp only [u, c.apply_symm_apply, map_one] at hh
    exact (by decide +kernel : e0 ≠ 1) hh
  have hv1 : (v : G) ≠ 1 := by
    intro he
    have hh := congrArg c (show v = 1 from Subtype.ext he)
    simp only [v, c.apply_symm_apply, map_one] at hh
    exact (by decide +kernel : e1 ≠ 1) hh
  have huv1 : (uv : G) ≠ 1 := by
    intro he
    have hh := congrArg c (show uv = 1 from Subtype.ext he)
    simp only [uv, c.apply_symm_apply, map_one] at hh
    exact (by decide +kernel : e0 * e1 ≠ 1) hh
  have huv : (u : G) ≠ v := by
    intro he
    have hh := congrArg c (show u = v from Subtype.ext he)
    simp only [u, v, c.apply_symm_apply] at hh
    exact (by decide +kernel : e0 ≠ e1) hh
  let hu := h.at_seed_point u u.property hu1
  let hv := h.at_seed_point v v.property hv1
  let huvtype := h.at_seed_point uv uv.property huv1
  have hao : orderOf (alphaAt c) = 2 :=
    ((MulAut.congr c).symm.orderOf_eq alpha).trans model_orders.1
  have hbo : orderOf (betaAt c) = 2 :=
    ((MulAut.congr c).symm.orderOf_eq beta).trans model_orders.2.1
  have hto : orderOf (alphaAt c * betaAt c) = 2 := by
    change orderOf ((MulAut.congr c).symm alpha * (MulAut.congr c).symm beta) = 2
    rw [← map_mul, MulEquiv.orderOf_eq]
    exact model_orders.2.2
  have had : alphaAt c w * w⁻¹ = (⟨(u : G), hu.involution_mem_seed⟩ : V) := by
    apply c.injective
    rw [map_mul, map_inv, alphaAt_apply]
    change alpha (c (c.symm e2)) * (c (c.symm e2))⁻¹ = c (c.symm e0)
    rw [c.apply_symm_apply, c.apply_symm_apply]
    exact model_displacements.1
  have hbd : betaAt c w * w⁻¹ = (⟨(v : G), hv.involution_mem_seed⟩ : V) := by
    apply c.injective
    rw [map_mul, map_inv, betaAt_apply]
    change beta (c (c.symm e2)) * (c (c.symm e2))⁻¹ = c (c.symm e1)
    rw [c.apply_symm_apply, c.apply_symm_apply]
    exact model_displacements.2.1
  have htd : (alphaAt c * betaAt c) w * w⁻¹ =
      (⟨(uv : G), huvtype.involution_mem_seed⟩ : V) := by
    apply c.injective
    rw [map_mul, map_inv, MulAut.mul_apply, alphaAt_apply, betaAt_apply]
    change alpha (beta (c (c.symm e2))) * (c (c.symm e2))⁻¹ = c (c.symm (e0 * e1))
    rw [c.apply_symm_apply, c.apply_symm_apply]
    exact model_displacements.2.2
  obtain ⟨a, haQ, ha2, haf⟩ := hu.exists_point_core_involution_of_displacement c _ hao w had
  obtain ⟨b, hbQ, hb2, hbf⟩ := hv.exists_point_core_involution_of_displacement c _ hbo w hbd
  obtain ⟨t, htQ, ht2, htf⟩ := huvtype.exists_point_core_involution_of_displacement c _ hto w htd
  have haC := plane_centralized c a (Or.inl haf)
  have hbC := plane_centralized c b (Or.inr (Or.inl hbf))
  have htC := plane_centralized c t (Or.inr (Or.inr htf))
  have huW : (u : G) ∈ planeAt c := ⟨u, by change (c u).toAdd 2 = 0; rw [c.apply_symm_apply]; rfl, rfl⟩
  have hvW : (v : G) ∈ planeAt c := ⟨v, by change (c v).toAdd 2 = 0; rw [c.apply_symm_apply]; rfl, rfl⟩
  have hab2 : ⁅(a : G), (b : G)⁆ ^ 2 = 1 :=
    h.point_core_pair_commutator_square u v u.property v.property hu1 hv1 huv a b haQ hbQ
      (mem_centralizer_singleton_iff.mpr (haC v hvW).symm)
      (mem_centralizer_singleton_iff.mpr (hbC u huW).symm)
  have hker : V.normalizerMonoidHom.ker = pCore 2 (normalizer (V : Set G)) := by
    rw [normalizerMonoidHom_ker, h.seed_centralizer]
    exact comap_map_eq_self_of_injective (normalizer (V : Set G)).subtype_injective _
  have habc : Commute (alphaAt c) (betaAt c) :=
    model_commute.map (MulAut.congr c).symm.toMonoidHom
  have habP : ⁅a, b⁆ ∈ pCore 2 (normalizer (V : Set G)) := by
    rw [← hker]
    change V.normalizerMonoidHom ⁅a, b⁆ = 1
    simp only [commutatorElement_def, map_mul, map_inv, haf, hbf]
    exact commutatorElement_eq_one_iff_commute.mpr habc
  have htP : t * (a * b)⁻¹ ∈ pCore 2 (normalizer (V : Set G)) := by
    rw [← hker]
    change V.normalizerMonoidHom (t * (a * b)⁻¹) = 1
    rw [map_mul, map_inv, map_mul, haf, hbf, htf, mul_inv_cancel]
  exact ⟨⟨a, b, t, haQ, hbQ, htQ, ha2, hb2, ht2, haf, hbf, htf,
    haC, hbC, htC, Subtype.ext hab2, habP, htP⟩⟩

end CFSG.Quasithin.HigmanSims
