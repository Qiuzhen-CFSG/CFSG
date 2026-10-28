module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.FiveDisplacement
public import Theory.Representation.IrreducibleFivePlaneInverter.Embedded

/-!
# Original five-core centralization and component selection

Assume the original V-star moves O₅(H-star). The actual supercritical
subgroup is elementary of order 25 or extraspecial of order 125. Its marked
Sylow-three action is irreducible on the Frattini quotient and V-star
inverts that quotient. In the elementary case, the original faithful binary
section has V-star displacement at least six; in the extraspecial case the
lower bound is eight. Both contradict the original rank-four commutator
section U_H/V₁. Thus the whole five-core is centralized, and the earlier
odd-core argument now selects the actual moved component without any
additional odd-core hypothesis.

The earlier fixed-space, point invariance, intersection and nonsingular
centralizer hypotheses remain explicit. Component analysis, the abelian
point-span theorem and the universal natural reduction remain subsequent
source obligations.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.832.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06

private theorem frattini_inverter_ne_one {Y : Type*} [Group Y] [Finite Y]
    (hcard : Nat.card (Y ⧸ frattini Y) = 25) (a : MulAut Y)
    (hinv : ∀ x : Y ⧸ frattini Y, quotientAut (frattini Y) a x = x⁻¹) : a ≠ 1 := by
  intro ha
  have hb : quotientAut (frattini Y) a = 1 := by rw [ha,map_one]
  let : Nontrivial (Y ⧸ frattini Y) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; decide)
  obtain ⟨x,hx⟩ := exists_ne (1 : Y ⧸ frattini Y)
  have hi : x = x⁻¹ := (DFunLike.congr_fun hb x).symm.trans (hinv x)
  have htwo : x ^ 2 = 1 := by rw [pow_two]; exact eq_inv_iff_mul_eq_one.mp hi
  have hd := orderOf_dvd_natCard x
  rw [hcard] at hd
  have ho := Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 25)
    (orderOf_dvd_of_pow_eq_one htwo) hd
  exact hx (orderOf_eq_one_iff.mp ho)

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- V-star centralizes the entire original five-core: both possible moved
supercritical models contradict the original rank-four commutator section. -/
theorem SourceHypothesis.original_star_five_core_centralized
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H)) :
    Nonabelian.Setup.star H V ≤
      centralizer (pCore 5 (H ⧸ pCore 2 H) : Set (H ⧸ pCore 2 H)) := by
  by_contra hm
  let E := D.fullSetup hZ T z
  let R := pCore 5 (H ⧸ pCore 2 H)
  let U := Nonabelian.Setup.star H V
  let P : Sylow 3 E.L₁ := Classical.choice inferInstance
  let P₀ := (P : Subgroup E.L₁).map E.L₁.subtype
  let A := Nonabelian.Setup.star H P₀
  obtain ⟨Y,hY,hmodels,hcard,hP,hirr,hinv⟩ :=
    S.original_five_supercritical_frattini D hZ z hz hTV hTz hbound hns hH hn hm P
  let : Y.Characteristic := hY.characteristic
  let a := (MulAut.characteristic Y).comp
    (MulAut.conjNormal : (H ⧸ pCore 2 H) →* MulAut R)
  have hU : Nat.card U = 2 :=
    (S.original_nonabelian_geometry D hZ z hz hTV hTz hbound hH hn).2.1
  let : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by rw [hU]; decide)
  obtain ⟨v,hv⟩ := exists_ne (1 : U)
  have ham : a v.val ≠ 1 := frattini_inverter_ne_one hcard (a v.val) (hinv v hv)
  rcases hmodels with ⟨hc,⟨e⟩⟩ | ⟨hc,hs,⟨e⟩⟩
  · let : IsElementaryAbelian 5 (Multiplicative (ZMod 5) × Multiplicative (ZMod 5)) :=
      { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide +kernel) }
    let : IsElementaryAbelian 5 Y := IsElementaryAbelian.of_injective e.toMonoidHom e.injective
    have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
    let := h.point_normal_in_UH
    let := h.point_quotient_elementary
    obtain ⟨σ,c,hσ,_⟩ := h.faithful_point_quotient
    have hr := S.original_binary_displacement_bound D hZ z hz hTV hTz hbound hH hn σ c
    let j : Y →* (H ⧸ pCore 2 H) := R.subtype.comp Y.subtype
    have hj : Function.Injective j := R.subtype_injective.comp Y.subtype_injective
    have hA : IsPGroup 3 A := by
      let : IsElementaryAbelian 3 A := (S.original_point_sylow_star D hZ z hz hTz hH P).1
      exact IsElementaryAbelian.isPGroup 3 A
    have hv2 : v.val ^ 2 = 1 := by
      have hh := pow_card_eq_one' (x := v)
      rw [hU] at hh
      exact congrArg Subtype.val hh
    have hvn : v.val ≠ 1 := fun he => hv (Subtype.ext he)
    have hl := IrreducibleFivePlaneInverter.six_le_displacement_of_embedded_frattini
      σ hσ j hj hc a (fun g y => rfl) A hA hirr v.val
      ⟨hvn,hv2⟩ (hinv v hv)
    have hu := hr v.val v.property
    omega
  · let : IsExtraspecial 5 Y := hs
    have hzero := S.original_extraspecial_five_action_trivial D hZ z hz hTV hTz hbound hH hn Y hc e
    exact ham (hzero.le (mem_map_of_mem a v.property))

/-- The original moved component is selected with the five-core premise
now discharged; only the retained earlier-source geometry remains explicit. -/
theorem SourceHypothesis.original_selectedComponent
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H)) :
    Nonempty ((D.fullSetup hZ T z).SelectedComponent H) :=
  S.original_selectedComponent_of_five_core D hZ z hz hTV hTz hbound hns hH hn
    (S.original_star_five_core_centralized D hZ z hz hTV hTz hbound hns hH hn)
end CFSG.Quasithin.Chapter12.Section06
