module
public import Theory.GroupTheory.LocalNormalizerLift
public import Theory.Mathieu.M22.Properties.HexadExtension
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.TwoLocalOrders

/-!
# The Mathieu hexad local excludes Ree F₄ sections

The actual M₂₂ hexad stabilizer has a normal elementary sixteen and order
5760. Frattini lifting through any finite covering kernel gives a nontrivial
two-subgroup whose normalizer has order divisible by fifteen. This conflicts
with the native Ree parabolic normalizer cover: the linear parabolic is
five-free and the Suzuki parabolic is three-free. Thus no finite group
surjecting onto M₂₂ embeds in a positive-parameter Ree F₄ model.

The original residual-image consumer is
`Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.OddLocalRee`.
No central kernel is discarded and no componenthood in a selected element's
fixed group is needed. Source: Aschbacher--Smith 2.3.9(7)(f), p.525;
4.4.3, p.623; F.1.12, pp.263--264; GLS3 Theorem 3.1.3 and §§2.3, 2.6.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.M22LocalSections
/-- A full finite cover of M22 carries a nontrivial two-subgroup whose
normalizer has order divisible by fifteen. The kernel is unrestricted. -/
theorem exists_two_local_fifteen_dvd {E : Type*} [Group E] [Finite E]
    (f : E →* M22) (hf : Function.Surjective f) :
    ∃ U : Subgroup E, U ≠ ⊥ ∧ IsPGroup 2 U ∧
      15 ∣ Nat.card (normalizer (U : Set E)) := by
  let H := m22HexadStabilizer
  let R : Subgroup H := (m22SetAction m22Hexad123).ker
  let : R.Normal := inferInstanceAs ((m22SetAction m22Hexad123).ker.Normal)
  have hR : IsPGroup 2 R :=
    @IsElementaryAbelian.isPGroup 2 _ _ (m22HexadKernel_elementaryAbelian m22Hexad123_mem)
  have hne : R ≠ ⊥ := by
    intro he
    have hc := m22HexadKernel_card m22Hexad123_mem
    change Nat.card R = 16 at hc
    rw [he,card_bot] at hc
    contradiction
  let q := f.subgroupComap H
  obtain ⟨U,hU,hUp,hUn⟩ := exists_pSubgroup_normalizer_surjective_of_normal_pSubgroup
    q (f.subgroupComap_surjective_of_surjective H hf) R hR hne
  let j := (H.comap f).subtype
  let W := U.map j
  have hW : W ≠ ⊥ := fun he => hU ((map_eq_bot_iff_of_injective _ (H.comap f).subtype_injective).mp he)
  refine ⟨W,hW,hUp.map j,?_⟩
  have hd : 15 ∣ Nat.card (normalizer (U : Set (H.comap f))) :=
    dvd_trans (by change 15 ∣ Nat.card m22HexadStabilizer; rw [m22HexadStabilizer_card]; decide)
      (card_dvd_of_surjective _ hUn)
  have hn := card_dvd_of_le (U.le_normalizer_map j)
  rw [card_map_of_injective (H.comap f).subtype_injective] at hn
  exact hd.trans hn

/-- The Ree two-local order obstruction excludes every full M22 cover,
without suppressing its central kernel or requiring a fixed-group promotion. -/
theorem no_embedding_ree {E : Type*} [Group E] [Finite E]
    (f : E →* M22) (hf : Function.Surjective f)
    {m : ℕ} (hm : 1 ≤ m) (j : E →* ReeF4.Model m) (hj : Function.Injective j) : False := by
  obtain ⟨U,hU,hp,hd⟩ := exists_two_local_fifteen_dvd f hf
  have hne : U.map j ≠ ⊥ := fun he => hU ((map_eq_bot_iff_of_injective _ hj).mp he)
  apply ReeF4.ConverseParabolics.normalizer_fifteen_free hm (U.map j) hne (hp.map j)
  have hn := card_dvd_of_le (U.le_normalizer_map j)
  rw [card_map_of_injective hj] at hn
  exact hd.trans hn
end Sporadic.Mathieu.M22LocalSections
