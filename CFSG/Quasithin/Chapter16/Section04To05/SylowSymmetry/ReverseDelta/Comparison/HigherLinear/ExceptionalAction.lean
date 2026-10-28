module

public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.HigherLinear.ExceptionalAction.Transport
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.HigherLinear.Reduction
public import CFSG.Quasithin.Chapter16.Section04To05.IntersectionStructure.SylowTransport

public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Contracts
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.Transport

/-!
# Excluding the exceptional equal-A₄ pair by its action

Reduction leaves the inner j₂ row and exceptional outer row in PSL₄(2).
Their marked actors have cycle types 2²1⁴ and 2³1² in the actual A₈
component models. These precise earlier table clauses remain explicit;
no residual-comparison conclusion is assumed.

The center of C_{L′}(z) has a unique involution v. The actual action of
C_L(r) on L′ fixes v. Conversely v normalizes L and fixes C_L(r), so its
action on L is identity or the action of r. Thus either v or vr⁻¹ is a
two-element of C_G(L) commuting with z. Its relative Sylow subgroup is
⟨z⟩, forcing that element to be 1 or z. These alternatives put v in
Z(L′), make v trivial, or make z inner on L′, each a contradiction.

The stronger action theorem needs neither the abstract A₄ equivalences
nor equality of the residuals. Consequently it applies to the remaining
branch without identifying the images in L/Z(L) and L′/Z(L′). Final
higher-linear assembly, including provision of the marked earlier rows,
remains outside this module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
16.1.4(3),(9), printed p.1171, and the proof of 16.4.11(2), printed p.1193.
-/

@[expose] public section

open Subgroup Equiv
open Theory.SpecificGroups.SymmetricEight.Involutions
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.HigherLinear.ExceptionalAction
open Transport
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- Conjugation by the actual inner centralizer on the opposite component. -/
def innerCentralizerAction (d : Contrary T z L g R r) :
    (L ⊓ centralizer ({r} : Set G) : Subgroup G) →* MulAut (L.conjBy g) :=
  (L.conjBy g).normalizerMonoidHom.comp
    (inclusion ((inner_centralizer_le d.setup d.mem d.involution).trans inf_le_left))

/-- The induced action retains ambient conjugation on every element. -/
theorem innerCentralizerAction_apply (d : Contrary T z L g R r)
    (x : (L ⊓ centralizer ({r} : Set G) : Subgroup G)) (y : L.conjBy g) :
    (innerCentralizerAction d x y : G) = (x : G) * y * (x : G)⁻¹ := rfl

omit [Finite G] in
private theorem centralizer_le_normalizer_zpowers (s : G) :
    centralizer ({s} : Set G) ≤ normalizer (zpowers s : Set G) := by
  apply le_trans _ (centralizer_le_normalizer _)
  intro x hx y hy
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
  exact (show Commute s x from (mem_centralizer_singleton_iff.mp hx).symm).zpow_left n

/-- The central involution z is the only involution of C_G(L) commuting with z.
The Sylow condition is relative to C_G(L), not to the ambient group. -/
private theorem centralizing_two_element (d : Contrary T z L g R r) {k : G}
    (hk : k ∈ centralizer (L : Set G)) (hkz : k ∈ centralizer ({z} : Set G))
    (hk2 : k ^ 2 = 1) : k = 1 ∨ k = z := by
  classical
  have hz : zpowers z = commutingSylow T L :=
    eq_of_le_of_card_ge (zpowers_le.mpr (z_mem_commutingSylow d.setup))
      (by rw [Nat.card_zpowers, d.setup.involution, d.small])
  have hp : IsPGroup 2 (zpowers k) := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one hk2)
  have hzp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, d.setup.involution, pow_one])
  have hQp : IsPGroup 2 (zpowers k ⊔ zpowers z : Subgroup G) :=
    hp.to_sup_of_normal_right' hzp
      (zpowers_le.mpr (centralizer_le_normalizer_zpowers z hkz))
  have he := d.setup.toStandardSetup.commutingSylow_sylow.maximal hQp
    (sup_le (zpowers_le.mpr hk) (zpowers_le.mpr (z_mem_commutingSylow d.setup).2))
    (hz ▸ (le_sup_right : zpowers z ≤ zpowers k ⊔ zpowers z))
  have hkm : k ∈ zpowers z := hz.symm ▸ he ▸ mem_sup_left (mem_zpowers k)
  rw [mem_zpowers_iff_mem_range_orderOf, d.setup.involution] at hkm
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hkm
  have hi2 := Finset.mem_range.mp hi
  interval_cases i
  · exact Or.inl (by simpa using he.symm)
  · exact Or.inr (by simpa using he.symm)

private theorem centralizer_z_normalizes (d : Contrary T z L g R r) :
    centralizer ({z} : Set G) ≤ normalizer (L : Set G) := by
  have hp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, d.setup.involution, pow_one])
  have hn := d.setup.tight.normalizer_le hp
    (zpowers_ne_bot.mpr (fun he => by simpa [he] using d.setup.involution))
    (zpowers_le.mpr (z_mem_commutingSylow d.setup).2)
  rw [d.setup.normalizers_eq] at hn
  exact (centralizer_le_normalizer_zpowers z).trans hn

omit [Finite G] in
private theorem conjugate_center_eq_bot (hZ : center L = ⊥) :
    center (L.conjBy g) = ⊥ := by
  let e : L ≃* L.conjBy g := (MulAut.conj g).subgroupMap L
  apply eq_bot_iff.mpr
  intro x hx
  have h := ((centerCongr e).symm ⟨x, hx⟩).property
  change e.symm x ∈ center L at h
  rw [hZ, mem_bot] at h
  exact e.symm.injective (h.trans e.symm.map_one.symm)

/-- The actual inner and outer marked actions are incompatible. The proof uses
the characteristic central involution of the outer fixed group, not the orders
or abstract isomorphism types of the two A₄ residuals. -/
theorem excluded_of_marked_actions (d : Contrary T z L g R r) (hZ : center L = ⊥)
    (ei : L ≃* A) (eo : L.conjBy g ≃* A)
    (hi : automorphismPermutationEquiv ei
      (action (d.setup.sylow_normalizes (d.setup.le_sylow d.mem))) = twoPairs)
    (ho : automorphismPermutationEquiv eo (action d.z_normalizes) = threePairs) : False := by
  obtain ⟨v, hv, hv1, hv2, hvfix⟩ := outer_characteristic_involution eo d.z_normalizes ho
  have haction : ∀ x : (L ⊓ centralizer ({r} : Set G) : Subgroup G),
      innerCentralizerAction d x ⟨v, hv.1⟩ = ⟨v, hv.1⟩ := by
    intro x
    apply Subtype.ext
    rw [innerCentralizerAction_apply]
    rw [hvfix x ((inner_centralizer_le d.setup d.mem d.involution) x.property),
      mul_inv_cancel_right]
  have hvN := centralizer_z_normalizes d hv.2
  let b : MulAut L := action hvN
  have hb : ∀ x : L, (x : G) ∈ centralizer ({r} : Set G) → b x = x := by
    intro x hx
    apply Subtype.ext
    change v * (x : G) * v⁻¹ = x
    have h := congrArg Subtype.val (haction ⟨x, x.property, hx⟩)
    rw [innerCentralizerAction_apply] at h
    have hc := mul_inv_eq_iff_eq_mul.mp h
    rw [← hc, mul_inv_cancel_right]
  have hrM : r ∈ centralizer (L.conjBy g : Set G) := by
    rw [centralizer_conjugate]
    exact d.sylow.le d.mem
  have hrN := d.setup.sylow_normalizes (d.setup.le_sylow d.mem)
  have hr2 : r ^ 2 = 1 := d.involution ▸ pow_orderOf_eq_one r
  have hvK_or : v ∈ centralizer (L : Set G) ∨ v * r⁻¹ ∈ centralizer (L : Set G) := by
    rcases fixing_inner ei hrN hi b hb with hb1 | hbr
    · left
      have hk : (⟨v, hvN⟩ : normalizer (L : Set G)) ∈ L.normalizerMonoidHom.ker := hb1
      rw [normalizerMonoidHom_ker] at hk
      exact hk
    · right
      have hk : (⟨v, hvN⟩ : normalizer (L : Set G)) * ⟨r, hrN⟩⁻¹ ∈
          L.normalizerMonoidHom.ker := by
        change L.normalizerMonoidHom _ = 1
        rw [map_mul, map_inv, show L.normalizerMonoidHom ⟨v, hvN⟩ =
          L.normalizerMonoidHom ⟨r, hrN⟩ from hbr, mul_inv_cancel]
      rw [normalizerMonoidHom_ker] at hk
      exact hk
  rcases hvK_or with hvK | hk
  · rcases centralizing_two_element d hvK hv.2 hv2 with he | he
    · exact hv1 he
    · exact d.outer (mem_sup_right (he ▸ hv.1))
  · have hkr : Commute v r := mem_centralizer_iff.mp hrM v hv.1
    have hk2 : (v * r⁻¹) ^ 2 = 1 := by
      rw [hkr.inv_right.mul_pow, hv2, inv_pow, hr2, inv_one, one_mul]
    have hkz : v * r⁻¹ ∈ centralizer ({z} : Set G) :=
      (centralizer ({z} : Set G)).mul_mem hv.2
        ((centralizer ({z} : Set G)).inv_mem
          (d.setup.sylow_centralizes (d.setup.le_sylow d.mem)))
    rcases centralizing_two_element d hk hkz hk2 with he | he
    · have hvr : v = r := mul_inv_eq_one.mp he
      have hvMC : v ∈ centralizer (L.conjBy g : Set G) := hvr.symm ▸ hrM
      have hc : (⟨v, hv.1⟩ : L.conjBy g) ∈ center (L.conjBy g) := by
        apply mem_center_iff.mpr
        intro x
        apply Subtype.ext
        exact mem_centralizer_iff.mp hvMC x x.property
      rw [conjugate_center_eq_bot hZ, mem_bot] at hc
      exact hv1 (congrArg Subtype.val hc)
    · apply d.outer
      rw [← he]
      exact mul_mem (mem_sup_right hv.1) (mem_sup_left
        ((centralizer (L.conjBy g : Set G)).inv_mem hrM))

/-- Cycle markings suffice: actual permutation conjugators normalize both
actors before applying the ambient action contradiction. -/
theorem excluded_of_cycle_types (d : Contrary T z L g R r) (hZ : center L = ⊥)
    (ei : L ≃* A) (eo : L.conjBy g ≃* A)
    (hi : (automorphismPermutationEquiv ei
      (action (d.setup.sylow_normalizes (d.setup.le_sylow d.mem)))).cycleType = {2, 2})
    (ho : (automorphismPermutationEquiv eo (action d.z_normalizes)).cycleType = {2, 2, 2}) :
    False := by
  obtain ⟨fi, hfi⟩ := mark_of_cycleType ei
    (action (d.setup.sylow_normalizes (d.setup.le_sylow d.mem))) twoPairs
    (hi.trans twoPairs_cycleType.symm)
  obtain ⟨fo, hfo⟩ := mark_of_cycleType eo (action d.z_normalizes) threePairs
    (ho.trans threePairs_cycleType.symm)
  exact excluded_of_marked_actions d hZ fi fo hfi hfo

/-- The genuine conjugate component model, transported from the PSL₄(2) model. -/
noncomputable def conjugateAlternatingEquiv (d : Contrary T z L g R r)
    (hZ : center L = ⊥) (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 4 2) :
    L.conjBy g ≃* A :=
  ((MulAut.conj g).subgroupMap L).symm.trans (componentAlternatingEquiv d hZ hmodel)

/-- The remaining equal-A₄ branch of the higher-linear comparison, under the
exact earlier marked j₂ and exceptional outer table clauses. Residual equality
and the two A₄ equivalences are unnecessary once these actions are specified.
The source-theorem owner still has to supply both marked table clauses. -/
theorem equal_a4_excluded (d : Contrary T z L g R r) (hZ : center L = ⊥)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 4 2)
    (hi : (automorphismPermutationEquiv (componentAlternatingEquiv d hZ hmodel)
      (action (d.setup.sylow_normalizes (d.setup.le_sylow d.mem)))).cycleType = {2, 2})
    (ho : (automorphismPermutationEquiv (conjugateAlternatingEquiv d hZ hmodel)
      (action d.z_normalizes)).cycleType = {2, 2, 2}) : False :=
  excluded_of_cycle_types d hZ (componentAlternatingEquiv d hZ hmodel)
    (conjugateAlternatingEquiv d hZ hmodel) hi ho

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.HigherLinear.ExceptionalAction
