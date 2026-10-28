module

public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.Arms.Restrictions

/-!
# Displacement squares and the full arms Levi projection

The arms radical has central derived subgroup of exponent two. Multiplying
an actor by any radical element therefore changes a displacement only by
central factors whose squares are one. Its square is unchanged. Applying
this to the actual full Levi projection retains the pointwise square
restriction for every image element, with no restriction on radical factors.

A generic complement-factor calculation avoids expanding the concrete
quotient construction while checking the projection identity.

Sources: the special radical in Aschbacher--Smith F.1.11--12
(`refs/quasithin.pdf`, pp.262--264) and the actual multiplication formulas
from GLS3 §§2.4 and 2.6 (`refs/KGroup/GLS3/chapter2.tex`).
-/

public section

open Subgroup
open scoped commutatorElement
noncomputable section
namespace Triality.Standard.Parabolics
open RadicalCoordinates RadicalCoordinates.Centers

private theorem arms_derived_eq_highest (P : Parameters) (hp : P.prime = 2) :
    ⁅radical P .arms, radical P .arms⁆ = highestRoot P := by
  rw [← embedded_center_radical_arms P hp, center_radical_arms_eq_commutator P hp,
    map_subtype_commutator]

private theorem arms_commutator_central (P : Parameters) (hp : P.prime = 2)
    (a : Carrier P) (ha : a ∈ radical P .arms)
    (b : Carrier P) (hb : b ∈ radical P .arms)
    (z : Carrier P) (hz : z ∈ radical P .arms) : Commute ⁅a, b⁆ z := by
  have hm := commutator_mem_commutator ha hb
  rw [arms_derived_eq_highest P hp, ← embedded_center_radical_arms P hp] at hm
  obtain ⟨c, hc, he⟩ := hm
  rw [← he]
  exact (congrArg Subtype.val (mem_center_iff.mp hc ⟨z, hz⟩)).symm

private theorem highest_square (P : Parameters) (hp : P.prime = 2)
    (z : Carrier P) (hz : z ∈ highestRoot P) : z ^ 2 = 1 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  rw [← highestHom_range P hp] at hz
  obtain ⟨a, rfl⟩ := hz
  have ha : a ^ 2 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [pow_two]
    change a.toAdd + a.toAdd = 0
    exact CharTwo.add_self_eq_zero _
  rw [← map_pow, ha, map_one]

private theorem arms_commutator_square (P : Parameters) (hp : P.prime = 2)
    (a : Carrier P) (ha : a ∈ radical P .arms)
    (b : Carrier P) (hb : b ∈ radical P .arms) : ⁅a, b⁆ ^ 2 = 1 := by
  apply highest_square P hp
  rw [← arms_derived_eq_highest P hp]
  exact commutator_mem_commutator ha hb

private theorem mul_inv_mem_kernel {G K : Type*} [Group G] [Group K]
    (f : G →* K) (x y : G) (h : f x = f y) : x * y⁻¹ ∈ f.ker := by
  change f (x * y⁻¹) = 1
  rw [map_mul, map_inv, h, mul_inv_cancel]

private theorem relative_projection_factor {G : Type*} [Group G]
    {H R C : Subgroup G} (hR : R ≤ H) (hC : C ≤ H)
    (hgen : R ⊔ C = H) (hd : Disjoint R C) [(R.subgroupOf H).Normal]
    (x : H) :
    x.val * (relativeComplementProjection hR hC hgen hd x).val⁻¹ ∈ R := by
  let f := relativeComplementProjection hR hC hgen hd
  let c := f x
  have hi : f (Subgroup.inclusion hC c) = c :=
    relativeComplementProjection_inclusion hR hC hgen hd c
  exact (relativeComplementProjection_ker hR hC hgen hd).le
    (mul_inv_mem_kernel f x (Subgroup.inclusion hC c) hi.symm)

/-- Arbitrary radical factors do not change the squares of commutators with
radical elements. In particular they cannot hide a torus square obstruction. -/
theorem arms_commutator_square_eq_fullLeviProjection
    (P : Parameters) (hp : P.prime = 2) (x : parabolic P .arms)
    (r : Carrier P) (hr : r ∈ radical P .arms) :
    ⁅r, x.val⁆ ^ 2 = ⁅r, (fullLeviProjection P hp .arms x).val⁆ ^ 2 := by
  let g := fullLeviProjection P hp .arms x
  have hu : x.val * g.val⁻¹ ∈ radical P .arms :=
    relative_projection_factor (radical_le_parabolic P .arms)
      (fullLevi_le_parabolic P .arms) (parabolic_eq_radical_sup_fullLevi P hp .arms).symm
      (disjoint_radical_fullLevi P hp .arms) x
  have hv : ⁅r, g.val⁆ ∈ radical P .arms := by
    apply le_normalizer_iff_commutator_le_left.mp
      (fullLevi_le_normalizer_radical P .arms)
    exact commutator_mem_commutator hr g.property
  have he := commutator_square_mul_actor (radical P .arms)
    (arms_commutator_central P hp) (arms_commutator_square P hp)
    r (x.val * g.val⁻¹) g.val hr hu hv
  simpa only [inv_mul_cancel_right] using he

/-- Every full-Levi image element retains the pointwise square restriction,
with no choice or removal of radical components in the original actor. -/
theorem arms_fullLeviImage_commutator_squares
    (P : Parameters) (hp : P.prime = 2)
    (X : Subgroup (parabolic P .arms))
    (hsq : ∀ z ∈ ⁅(radical P .arms).subgroupOf (parabolic P .arms), X⁆,
      (z : parabolic P .arms) ^ 2 = 1)
    (g : fullLevi P .arms) (hg : g ∈ X.map (fullLeviProjection P hp .arms))
    (r : Carrier P) (hr : r ∈ radical P .arms) : ⁅r, g.val⁆ ^ 2 = 1 := by
  obtain ⟨x, hx, rfl⟩ := hg
  rw [← arms_commutator_square_eq_fullLeviProjection P hp x r hr]
  let rd : parabolic P .arms := ⟨r, radical_le_parabolic P .arms hr⟩
  have he := congrArg (parabolic P .arms).subtype
    (hsq ⁅rd, x⁆ (commutator_mem_commutator hr hx))
  simpa only [map_pow, map_commutatorElement, map_one, Subgroup.subtype_apply, rd] using he

end Triality.Standard.Parabolics
