module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.Contracts

/-!
# Actor normality in the covered Bender geometry

Let P and Y be the images on V of T_L and the odd cyclic actor X. Since X
normalizes T_L, Y normalizes P. The actor-normality field of `Geometry`
gives the reverse normalization: T_L fixes U_C. Their coprime orders imply
that P and Y commute. This commutation preserves the actual moved subgroup
[V,X]. A two-group acting on this subgroup has a nonidentity fixed point;
transitivity of X then makes T_L fix every element of [V,X]. It already
fixes U_C, so it fixes V and hence U_L.

Consequently Z(T_L)=Z(L) makes U_L lie in C_G(L), killing [V,X] and
contradicting its required order. This verifies that removing the stronger
`LocalAction.image_eq` field cannot repair the existing geometry interface.
It does not eliminate the covered ambient configuration: no existence of
`Geometry` under the genuine ambient hypotheses has been proved here.

Source: Aschbacher–Smith, Proposition 16.5.1, printed p.1194, and I.2.2(4),
printed p.409, combined manuscript of 1 March 2004.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction.CoveredCase
open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem image_normalizes {V A X : Subgroup G}
    (h : X ≤ normalizer (A : Set G)) :
    inducedActor V X ≤ normalizer (inducedActor V A : Set (ActionImage V)) := by
  exact (map_mono ((comap_mono h).trans (le_normalizer_comap
    (normalizer (V : Set G)).subtype))).trans
      (le_normalizer_map V.normalizerMonoidHom.rangeRestrict)

omit [Finite G] in
private theorem coprime_actor {T : Sylow 2 G} {L R : Subgroup G} {n : ℕ}
    (d : Geometry T L R n) : Nat.Coprime 2 (Nat.card d.actor) := by
  rw [d.actor_card, Nat.coprime_two_left]
  have he : Even (2 ^ n) := even_two.pow_of_ne_zero (by have := d.degree; omega)
  exact (Nat.odd_sub' (Nat.one_le_pow n 2 (by decide))).mpr (by simpa using he)

/-- Mutual normalization and coprime orders make the two actual action images commute. -/
theorem component_image_commutes_of_geometry {T : Sylow 2 G} {L R : Subgroup G} {n : ℕ}
    (d : Geometry T L R n) :
    inducedActor (benderSpace T L) (componentSylow T L) ≤
      centralizer (inducedActor (benderSpace T L) d.actor : Set (ActionImage (benderSpace T L))) := by
  let V := benderSpace T L
  let A := componentSylow T L
  let P := inducedActor V A
  let Y := inducedActor V d.actor
  have hAN : A ≤ normalizer (V : Set G) := inf_le_left.trans d.sylow_normalizes
  have hPN : P ≤ normalizer (Y : Set (ActionImage V)) := by
    rintro a ⟨aN, ha, rfl⟩
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact d.actor_normal_in_stabilizer aN (d.sylow_fixes ha.1)
  have hYN : Y ≤ normalizer (P : Set (ActionImage V)) :=
    image_normalizes (d.actor_le.trans inf_le_right)
  have hA : IsPGroup 2 A := T.isPGroup'.of_injective
    (inclusion inf_le_left) (inclusion_injective _)
  have hP : IsPGroup 2 P :=
    (hA.of_equiv (subgroupOfEquivOfLe hAN).symm).map _
  have hYcard : Nat.card Y ∣ Nat.card d.actor := by
    have hh := card_map_dvd (d.actor.subgroupOf (normalizer (V : Set G)))
      V.normalizerMonoidHom.rangeRestrict
    rwa [Nat.card_congr (subgroupOfEquivOfLe d.actor_normalizes).toEquiv] at hh
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdis : Disjoint P Y := disjoint_of_coprime_natCard (by
    rw [hk]
    exact ((coprime_actor d).pow_left k).coprime_dvd_right hYcard)
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply le_bot_iff.mp
  exact (le_inf (le_normalizer_iff_commutator_le_left.mp hYN)
    (le_normalizer_iff_commutator_le_right.mp hPN)).trans hdis.le_bot

private theorem geometry_actions_commute {T : Sylow 2 G} {L R : Subgroup G} {n : ℕ}
    (d : Geometry T L R n) {a x v : G}
    (ha : a ∈ componentSylow T L) (hx : x ∈ d.actor) (hv : v ∈ benderSpace T L) :
    MulAut.conj a (MulAut.conj x v) = MulAut.conj x (MulAut.conj a v) := by
  let aN : normalizer (benderSpace T L : Set G) := ⟨a, d.sylow_normalizes ha.1⟩
  let xN : normalizer (benderSpace T L : Set G) := ⟨x, d.actor_normalizes hx⟩
  let f := (benderSpace T L).normalizerMonoidHom.rangeRestrict
  have he : f xN * f aN = f aN * f xN :=
    component_image_commutes_of_geometry d ⟨aN, ha, rfl⟩ (f xN) ⟨xN, hx, rfl⟩
  have hh := congrArg (fun b : ActionImage (benderSpace T L) =>
    (b : MulAut (benderSpace T L)) ⟨v, hv⟩) he
  exact (congrArg Subtype.val hh).symm

private theorem geometry_component_normalizes_moved
    {T : Sylow 2 G} {L R : Subgroup G} {n : ℕ} (d : Geometry T L R n) :
    componentSylow T L ≤ normalizer ((⁅benderSpace T L, d.actor⁆ : Subgroup G) : Set G) := by
  intro a ha
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hle : (⁅benderSpace T L, d.actor⁆).map (MulAut.conj a).toMonoidHom ≤
      ⁅benderSpace T L, d.actor⁆ := by
    apply map_le_iff_le_comap.mpr
    apply commutator_le.mpr
    intro v hv x hx
    have hev := geometry_actions_commute d ha hx ((benderSpace T L).inv_mem hv)
    have he : MulAut.conj a ⁅v, x⁆ = ⁅MulAut.conj a v, x⁆ := by
      have he1 : ⁅v, x⁆ = v * MulAut.conj x v⁻¹ := by
        simp only [commutatorElement_def, MulAut.conj_apply, mul_assoc]
      have he2 : ⁅MulAut.conj a v, x⁆ =
          MulAut.conj a v * MulAut.conj x (MulAut.conj a v⁻¹) := by
        rw [map_inv]
        simp only [commutatorElement_def, MulAut.conj_apply, mul_assoc]
      rw [he1, map_mul, hev, he2]
    change MulAut.conj a ⁅v, x⁆ ∈ ⁅benderSpace T L, d.actor⁆
    rw [he]
    exact commutator_mem_commutator
      ((mem_normalizer_iff.mp (d.sylow_normalizes ha.1) v).mp hv) hx
  exact eq_of_le_of_card_ge hle (card_map_of_injective (MulAut.conj a).injective).ge

/-- Actor normality and transitivity force the component Sylow to fix its omega subgroup.
The proof uses the actual moved subgroup and its conjugation action. -/
theorem component_omega_centralizes_sylow_of_geometry
    {T : Sylow 2 G} {L R : Subgroup G} {n : ℕ} (d : Geometry T L R n) :
    omegaOneAmbient (componentSylow T L) ≤ centralizer (componentSylow T L : Set G) := by
  let A := componentSylow T L
  let W := ⁅benderSpace T L, d.actor⁆
  have hA : IsPGroup 2 A := T.isPGroup'.of_injective
    (inclusion inf_le_left) (inclusion_injective _)
  let f : A →* MulAut W := W.normalizerMonoidHom.comp
    (inclusion (geometry_component_normalizes_moved d))
  let : MulAction A W := MulAction.compHom W f
  have hcard : 2 ∣ Nat.card W := by
    rw [d.moved_card]
    exact dvd_pow_self _ (by have := d.degree; omega)
  obtain ⟨w, hw, hw1⟩ := hA.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    W hcard (a := 1) (by intro a; exact map_one (f a))
  have hwV : (w : G) ∈ benderSpace T L := (le_sup_right.trans_eq d.span) w.property
  have hwne : (w : G) ≠ 1 := by
    intro hh
    exact hw1 (Subtype.ext hh).symm
  have hWA : W ≤ centralizer (A : Set G) := by
    intro v hv a ha
    by_cases hv1 : v = 1
    · simp [hv1]
    obtain ⟨x, hx, _⟩ := d.regular w w.property hwne v hv hv1
    have hwfix : MulAut.conj a (w : G) = w :=
      congrArg Subtype.val (hw ⟨a, ha⟩)
    have he : MulAut.conj a v = v := by
      rw [← hx, geometry_actions_commute d ha x.property hwV, hwfix]
    exact mul_inv_eq_iff_eq_mul.mp he
  have hCA : omegaOneAmbient (commutingSylow T L) ≤ centralizer (A : Set G) :=
    ((omegaOneAmbient_le _).trans inf_le_right).trans (centralizer_le inf_le_right)
  have hVA : benderSpace T L ≤ centralizer (A : Set G) := by
    rw [← d.span]
    exact sup_le hCA hWA
  exact le_sup_right.trans hVA

/-- Even without the full action-image equality, the published geometry is impossible
when the component Sylow center equals the component center. This is a diagnostic,
not an exclusion under the ambient hypotheses of Proposition 16.5.1. -/
theorem no_geometry_of_sylow_center
    {T : Sylow 2 G} {L R : Subgroup G} {n : ℕ}
    (hcenter : (center (componentSylow T L)).map (componentSylow T L).subtype =
      (center L).map L.subtype) : ¬ Nonempty (Geometry T L R n) := by
  rintro ⟨d⟩
  have hUC := component_omega_centralizes_sylow_of_geometry d
  have hUK : omegaOneAmbient (componentSylow T L) ≤ centralizer (L : Set G) := by
    intro u hu
    have huZ : u ∈ (center (componentSylow T L)).map (componentSylow T L).subtype := by
      refine ⟨⟨u, omegaOneAmbient_le _ hu⟩, ?_, rfl⟩
      exact mem_center_iff.mpr fun a => Subtype.ext (hUC hu a a.property)
    rw [hcenter] at huZ
    obtain ⟨uL, huL, rfl⟩ := huZ
    intro a ha
    exact congrArg L.subtype (mem_center_iff.mp huL ⟨a, ha⟩)
  have hVK : benderSpace T L ≤ centralizer (L : Set G) :=
    sup_le ((omegaOneAmbient_le _).trans inf_le_right) hUK
  have hz : ⁅benderSpace T L, d.actor⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (hVK.trans (centralizer_le (d.actor_le.trans inf_le_left)))
  have hc := d.moved_card
  rw [hz, card_bot] at hc
  have hp : 1 < 2 ^ n := one_lt_pow₀ (by decide) (by have := d.degree; omega)
  omega


end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction.CoveredCase
