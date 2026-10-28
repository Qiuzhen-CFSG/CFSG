module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.CubicImage
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport

/-!
# Cubic containment for the chosen natural seed

The subgroup N_G(L) ∩ N_G(V) acts on the literal fixed-space quotient of
V. Its marked component is full SL₃, with the original two-core as kernel.
The rank-two cubic theorem therefore places every cubic of this subgroup
in L. In particular this proves the whole cubic clause when V = V_M.

Source: the natural-constituent step in Aschbacher--Smith A.3.19, printed
pp.54--55, used in 11.0.4, printed p.760. For cubics moving the seed, the
preliminary assembly owner retains the invariant-constituent argument.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The order-three clause of 11.0.4 for an actor preserving the chosen natural
seed. The action and two-core quotient are the literal source maps. -/
theorem sl3_orderThree_mem_of_normalizes_seed
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) {x : G}
    (hxM : x ∈ normalizer (L : Set G)) (hxV : x ∈ normalizer (V : Set G))
    (hx : orderOf x = 3) : x ∈ L := by
  let M := normalizer (L : Set G)
  let H := M ⊓ normalizer (V : Set G)
  have hLH : L ≤ H := le_inf L.le_normalizer D.normalizes
  let K := L.subgroupOf H
  let : K.Normal := normal_subgroupOf_of_le_normalizer inf_le_left
  let a : K ≃* L := subgroupOfEquivOfLe hLH
  let η : K →* Matrix.SpecialLinearGroup (Fin 3) S.field.Carrier :=
    m.groupEquiv.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 L)).comp a.toMonoidHom)
  have hη : Function.Surjective η := m.groupEquiv.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp a.surjective)
  have hηker : Nat.Coprime 3 (Nat.card η.ker) := by
    have hk : η.ker = (pCore 2 L).comap a.toMonoidHom := by
      ext k
      change m.groupEquiv (QuotientGroup.mk' (pCore 2 L) (a k)) = 1 ↔ a k ∈ pCore 2 L
      rw [m.groupEquiv.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff (a k)
    have hp : IsPGroup 2 η.ker := hk ▸ pCore_isPGroup.comap_of_injective
      a.toMonoidHom a.injective
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  let c := Coordinates.sl3 m
  let ρ : Representation (ZMod 2) H (Fin 3 → S.field.Carrier) :=
    c.conjugationAction inf_le_left inf_le_right
  have hnat (k : K) (w : Fin 3 → S.field.Carrier) :
      ρ (k : H) w = (η k).val.mulVec w := by
    obtain ⟨v,hv⟩ := c.projection_surjective (Multiplicative.ofAdd w)
    have hw : (c.projection v).toAdd = w := congrArg Multiplicative.toAdd hv
    rw [← hw]
    change c.conjugationAction inf_le_left inf_le_right (k : H) _ = _
    rw [c.conjugationAction_projection]
    have he : V.normalizerMonoidHom (inclusion (show H ≤ normalizer (V : Set G) from inf_le_right) k.val) v =
        V.normalizerMonoidHom (inclusion D.normalizes (a k)) v := rfl
    rw [he,c.projection_component_conjugation]
    rfl
  have hd : 3 ∣ Nat.card S.field.Carrier - 1 := by
    rw [S.field.card_eq]
    exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff S.field.degree).mpr heven
  have hr : primeRank 3 H ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion (show H ≤ M from inf_le_left))
      (inclusion_injective inf_le_left)).trans
      ((normalizer_sqtk D S).stronglyQuasithin 3 Nat.prime_three (by decide))
  exact CubicNatural.cubic_mem_of_natural_quotient K η hη hηker ρ hnat hd hr
    ⟨x,hxM,hxV⟩ (Subtype.ext (hx ▸ pow_orderOf_eq_one x))

/-- The even-degree SL₃ order-three clause when the original seed is already
its full normalizer orbit. No faithful-image or split-extension premise remains. -/
theorem sl3_orderThree_mem_of_fullModule_eq
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree)
    (hfull : componentOrbit V (normalizer (L : Set G)) = V) {x : G}
    (hxM : x ∈ normalizer (L : Set G)) (hx : orderOf x = 3) : x ∈ L := by
  have hn := le_normalizer_componentOrbit V (normalizer (L : Set G))
  rw [hfull] at hn
  exact sl3_orderThree_mem_of_normalizes_seed D S m heven hxM (hn hxM) hx

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
