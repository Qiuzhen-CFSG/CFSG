module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Configuration
public import Theory.GroupTheory.SpecificGroups.KleinFourFixedAut

/-!
# The normal four-group in the component quotient

The point stabilizer in the automorphism group of a four-group is a
 two-group. Thus an order-three-generated actor with a nonidentity fixed
point acts trivially. Applied to `V₂ = [V₂,Y₊]`, this proves that
`C_{V₂}(Y₊) = 1`. Since `Y₊ ≤ L`, the quotient by `C_I(L)` is faithful
on `V₂`. Its normality and commutator action then pass to the quotient.

These are the transport facts needed in all the model exclusions in
Aschbacher--Smith 15.3.43, combined manuscript (1 March 2004), printed
p.1140. They use the shared reduction output; they do not replace the
required construction of that output or any model calculation.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne
variable {G : Type*} [Group G]

/-- A four-group equal to its commutator with an order-three-generated
actor has no nonidentity fixed point. A fixed point would put the action
in a two-group, annihilating every order-three generator. -/
theorem fourGroup_centralizer_eq_bot {V Y : Subgroup G} [IsKleinFour V]
    (hgen : theta Y = Y) (hnorm : Y ≤ normalizer (V : Set G))
    (hcomm : ⁅V, Y⁆ = V) : V ⊓ centralizer (Y : Set G) = ⊥ := by
  apply bot_unique
  intro x hx
  by_contra hne
  have hxne : x ≠ 1 := hne
  let v : V := ⟨x, hx.1⟩
  have hv : v ≠ 1 := fun h => hxne (congrArg Subtype.val h)
  let ρ : Y →* MulAut V := V.normalizerMonoidHom.comp (Subgroup.inclusion hnorm)
  have hfix : ∀ a ∈ ρ.range, a v = v := by
    rintro a ⟨y, rfl⟩
    apply Subtype.ext
    change (y : G) * x * (y : G)⁻¹ = x
    rw [hx.2 y y.property, mul_assoc, mul_inv_cancel, mul_one]
  have hp := IsKleinFour.isPGroup_aut_subgroup_of_fixed_ne_one ρ.range hv hfix
  have hcentral : Y ≤ centralizer (V : Set G) := by
    rw [← hgen, theta, closure_le]
    rintro y ⟨hy, ho⟩
    let a : ρ.range := ⟨ρ ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩⟩
    have ha : a ^ 3 = 1 := by
      apply Subtype.ext
      change (ρ ⟨y, hy⟩) ^ 3 = 1
      rw [← map_pow]
      have hy3 : (⟨y, hy⟩ : Y) ^ 3 = 1 := Subtype.ext (ho ▸ pow_orderOf_eq_one y)
      rw [hy3, map_one]
    have ha1 : a = 1 := (hp.powEquiv (by decide : Nat.Coprime 2 3)).injective
      (by simpa only [IsPGroup.powEquiv_apply, one_pow] using ha)
    have hrho : ρ ⟨y, hy⟩ = 1 := congrArg Subtype.val ha1
    have hk : (Subgroup.inclusion hnorm ⟨y, hy⟩) ∈ V.normalizerMonoidHom.ker := hrho
    rw [normalizerMonoidHom_ker] at hk
    exact hk
  have hz : ⁅V, Y⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hcentral)
  have hVbot : V = ⊥ := hcomm.symm.trans hz
  have hc := IsKleinFour.card_four (G := V)
  have hc1 : Nat.card V = 1 := Subgroup.card_eq_one.mpr hVbot
  omega

/-- The four-group embeds faithfully in the quotient by `C_I(L)` when
its actor lies in `L`. This retains the actual group, not just a rank bound. -/
noncomputable def fourGroupImageEquiv {I L V Y : Subgroup G}
    (d : ComponentAction I L) [IsKleinFour V]
    (hVI : V ≤ I) (hYL : Y ≤ L) (hgen : theta Y = Y)
    (hnorm : Y ≤ normalizer (V : Set G)) (hcomm : ⁅V, Y⁆ = V) :
    V ≃* d.image V := by
  let f : V →* d.image V := (d.quotientMap.subgroupMap (V.subgroupOf I)).comp
    (subgroupOfEquivOfLe hVI).symm.toMonoidHom
  have hsurj : Function.Surjective f := (d.quotientMap.subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe hVI).symm.surjective
  have hinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    rw [MonoidHom.mem_ker, Subtype.ext_iff] at hx
    change d.quotientMap ⟨x, hVI x.property⟩ = 1 at hx
    have hk : (⟨(x : G), hVI x.property⟩ : I) ∈ d.kernel :=
      (QuotientGroup.eq_one_iff _).mp hx
    have hxc : (x : G) ∈ V ⊓ centralizer (Y : Set G) :=
      ⟨x.property, centralizer_le hYL hk⟩
    rw [fourGroup_centralizer_eq_bot hgen hnorm hcomm] at hxc
    exact Subtype.ext hxc
  exact MulEquiv.ofBijective f ⟨hinj, hsurj⟩

/-- Relative normality of the plane passes to the actual local image. -/
theorem image_normal_in_local {I L V M : Subgroup G}
    (d : ComponentAction I L) (hVI : V ≤ I) (hVM : V ≤ M)
    (hnorm : M ⊓ I ≤ normalizer (V : Set G)) :
    d.image V ≤ d.image M ∧ ((d.image V).subgroupOf (d.image M)).Normal := by
  have hVI' : V.subgroupOf I ≤ M.subgroupOf I := fun _ hx => hVM hx
  have hnI : M.subgroupOf I ≤ normalizer (V.subgroupOf I : Set I) := by
    rw [← subgroupOf_normalizer_eq hVI]
    exact fun x hx => hnorm ⟨hx, x.property⟩
  refine ⟨map_mono hVI', normal_subgroupOf_of_le_normalizer ?_⟩
  exact (map_mono hnI).trans ((V.subgroupOf I).le_normalizer_map d.quotientMap)

/-- Transport the full commutator action through the quotient. -/
theorem image_commutator_eq {I L V Y : Subgroup G}
    (d : ComponentAction I L) (hVI : V ≤ I) (hYI : Y ≤ I)
    (hcomm : ⁅V, Y⁆ = V) : ⁅d.image V, d.image Y⁆ = d.image V := by
  have hi : ⁅V.subgroupOf I, Y.subgroupOf I⁆ = V.subgroupOf I := by
    apply Subgroup.map_injective I.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hVI,
      map_subgroupOf_eq_of_le hYI, hcomm]
  have hm := congrArg (fun X : Subgroup I => X.map d.quotientMap) hi
  rwa [map_commutator] at hm
/-- The model calculations receive the original four-group, faithfully
embedded and normal in `M_I⁺`, with its full `Y₊⁺` commutator action.
This is a consequence of the reduction output; constructing that output
remains necessary for the source theorem. -/
theorem ReducedConfiguration.four_group_image
    {Yplus S M I L V₁ V₂ : Subgroup G}
    (c : ReducedConfiguration Yplus S M I L V₁ V₂) :
    Nonempty (V₂ ≃* c.toComponentAction.image V₂) ∧
      c.toComponentAction.image V₂ ≤ c.toComponentAction.image M ∧
      ((c.toComponentAction.image V₂).subgroupOf (c.toComponentAction.image M)).Normal ∧
      ⁅c.toComponentAction.image V₂, c.toComponentAction.image Yplus⁆ =
        c.toComponentAction.image V₂ := by
  let : IsElementaryAbelian 2 V₂ := c.plane_two_elementary
  let : Finite V₂ := Nat.finite_of_card_ne_zero (by rw [c.plane_two_card]; decide)
  let : Nontrivial V₂ := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [c.plane_two_card]
    decide)
  let : IsKleinFour V₂ := ⟨c.plane_two_card, IsElementaryAbelian.exponent_eq_prime⟩
  have hVI : V₂ ≤ I := c.plane_two_le.trans (le_sup_right.trans c.minimal.1.1.2)
  have hgen : theta Yplus = Yplus := by rw [← c.theta_eq, theta_idempotent]
  have hYMI : Yplus ≤ M ⊓ I := by
    rw [c.residual]
    exact map_subtype_le _
  have hnY := hYMI.trans c.plane_two_normalized
  obtain ⟨hle, hn⟩ := image_normal_in_local c.toComponentAction hVI
    (c.plane_two_le.trans c.sylow_le_M) c.plane_two_normalized
  exact ⟨⟨fourGroupImageEquiv c.toComponentAction hVI c.y_le_component hgen hnY
      c.plane_two_commutator⟩, hle, hn,
    image_commutator_eq c.toComponentAction hVI (c.y_le_component.trans c.component_le)
      c.plane_two_commutator⟩
end CFSG.Quasithin.Chapter15.Section03.RankOne
