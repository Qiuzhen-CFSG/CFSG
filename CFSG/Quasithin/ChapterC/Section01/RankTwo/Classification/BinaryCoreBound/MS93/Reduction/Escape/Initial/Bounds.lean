module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Basic

/-!
# Numerical reductions for the initial contrary configuration

The radius commutator R₀ lies in the natural eight-group at the far endpoint
and in Q at the starting vertex. Faithfulness of the natural action excludes
order eight. Thus its order is two or four; order two makes it the critical
commutator R. The quotient image modulo the starting Z has order at most two.

If R₀ has order four, critical-index reciprocity and the actual natural
action force the critical image to have order two. Finally, transport of H
shows that the radius/moving lower bound already implies the H lower bound.
All orders concern finite local subgroups of the infinite free amalgam.
The strict growth R₀ ≠ R remains a separate proof obligation.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.5), (4.3.1)(i)--(iii),(vi), printed pp.869--870, 882--883.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

namespace Initial

theorem Z_commutator_stabilizer (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) :
    ⁅Z R a, stabilizer R a⁆ = U R a := by
  have h := commutator_eq_of_centralizing_sup
    ((sup_comm _ _).trans (source.local_generation a ha))
    (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a ha)))
    ((Ltilde_le_stabilizer a).trans (Z_normalized R a))
  exact h.symm

theorem radius_le_natural (p : Counterexample geometry) (source : LocalSource L R) :
    radiusCommutator p.a p.a' ≤ U R p.a' := by
  have hV : V R p.a ≤ stabilizer R p.a' :=
    p.trapped.trans (Q_le_stabilizer_of_dist_two R p.c p.a' p.before_color p.before.1)
  rw [radiusCommutator, commutator_comm]
  exact (commutator_mono le_rfl hV).trans
    (Z_commutator_stabilizer source p.a' p.end_color).le

theorem radius_le_start_kernel (p : Counterexample geometry) (hb : 2 < geometry.b R) :
    radiusCommutator p.a p.a' ≤ Q R p.a :=
  p.radius_le_start.trans (geometry.V_le_Q hb p.a p.color_a)

theorem radius_card_le_four (p : Counterexample geometry) (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry) :
    Nat.card (radiusCommutator p.a p.a') ≤ 4 := by
  have hDU := radius_le_natural p source
  let : Finite (U R p.a') := Nat.finite_of_card_ne_zero
    (by rw [modules.natural.card_at p.a' p.end_color]; decide)
  have hdvd := card_dvd_of_le hDU
  rw [modules.natural.card_at p.a' p.end_color] at hdvd
  have hne : Nat.card (radiusCommutator p.a p.a') ≠ 8 := by
    intro hcard
    have heq : radiusCommutator p.a p.a' = U R p.a' :=
      eq_of_le_of_card_ge hDU (by rw [modules.natural.card_at p.a' p.end_color, hcard])
    have hUQ : U R p.a' ≤ Q R p.a := heq ▸ radius_le_start_kernel p hb
    apply p.critical.2
    rw [← modules.natural.centralizer p.a' p.end_color]
    exact le_inf (source.critical_Z_le_stabilizer geometry p.a p.color_a p.a' p.critical).1
      ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R p.a p.color_a)).trans
        (centralizer_le hUQ))
  have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  omega

theorem radius_card_two_or_four (p : Counterexample geometry) (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry) :
    Nat.card (radiusCommutator p.a p.a') = 2 ∨
      Nat.card (radiusCommutator p.a p.a') = 4 := by
  let := p.radius_finite
  let : Finite (U R p.a') := Nat.finite_of_card_ne_zero
    (by rw [modules.natural.card_at p.a' p.end_color]; decide)
  have hlarge := (one_lt_card_iff_ne_bot _).mpr (p.radius_ne_bot source)
  have hsmall := radius_card_le_four p source hb modules
  have hdvd := card_dvd_of_le (radius_le_natural p source)
  rw [modules.natural.card_at p.a' p.end_color] at hdvd
  have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  omega

theorem radius_eq_critical_of_card_two (p : Counterexample geometry)
    (source : LocalSource L R) (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (hcard : Nat.card (radiusCommutator p.a p.a') = 2) :
    radiusCommutator p.a p.a' = criticalCommutator p.a p.a' := by
  let := p.radius_finite
  exact (eq_of_le_of_card_ge (p.critical_le_radius_inf_start.trans inf_le_left)
    (by rw [p.critical_card source hb modules, hcard])).symm

theorem radius_card_four_iff_ne_critical (p : Counterexample geometry)
    (source : LocalSource L R) (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry) :
    Nat.card (radiusCommutator p.a p.a') = 4 ↔
      radiusCommutator p.a p.a' ≠ criticalCommutator p.a p.a' := by
  constructor
  · intro hcard heq
    rw [heq, p.critical_card source hb modules] at hcard
    omega
  · intro hne
    rcases radius_card_two_or_four p source hb modules with htwo | hfour
    · exact False.elim (hne (radius_eq_critical_of_card_two p source hb modules htwo))
    · exact hfour

theorem radius_quotient_image_le_two (p : Counterexample geometry)
    (source : LocalSource L R) (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry) :
    (Z R p.a).relIndex (radiusCommutator p.a p.a') ≤ 2 := by
  let := p.radius_finite
  let D := radiusCommutator p.a p.a'
  let C := (Z R p.a).subgroupOf D
  let : Finite ↥(Z R p.a ⊓ D) := Finite.of_injective
    (inclusion (show Z R p.a ⊓ D ≤ D from inf_le_right)) (inclusion_injective _)
  have hC : 2 ≤ Nat.card C := by
    have hh := card_le_of_le
      (show criticalCommutator p.a p.a' ≤ Z R p.a ⊓ D from
        p.critical_le_radius_inf_start.trans (by rw [inf_comm]))
    rw [p.critical_card source hb modules] at hh
    rwa [← Nat.card_congr (subgroupOfEquivOfLe
      (show Z R p.a ⊓ D ≤ D from inf_le_right)).toEquiv, inf_subgroupOf_right] at hh
  have hprod := C.index_mul_card
  have hsmall := radius_card_le_four p source hb modules
  change C.index ≤ 2
  change Nat.card D ≤ 4 at hsmall
  nlinarith

theorem critical_index_of_radius_card_four (p : Counterexample geometry)
    (source : LocalSource L R) (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (hcard : Nat.card (radiusCommutator p.a p.a') = 4) :
    (Q R p.a').relIndex (Z R p.a) = 2 := by
  let s : BinaryNaturalStructure source :=
    ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
  rw [s.critical_Z_index_eq_U geometry p.a p.color_a p.a' p.critical,
    modules.critical_U_index p.a p.color_a p.a' p.critical]
  let : Finite (U R p.a') := Nat.finite_of_card_ne_zero
    (by rw [modules.natural.card_at p.a' p.end_color]; decide)
  let C := (Q R p.a).subgroupOf (U R p.a')
  have hRC : radiusCommutator p.a p.a' ≤ Q R p.a ⊓ U R p.a' :=
    le_inf (radius_le_start_kernel p hb) (radius_le_natural p source)
  let : Finite ↥(Q R p.a ⊓ U R p.a') := Finite.of_injective
    (inclusion (show Q R p.a ⊓ U R p.a' ≤ U R p.a' from inf_le_right))
    (inclusion_injective _)
  have hC : 4 ≤ Nat.card C := by
    have hh := card_le_of_le hRC
    rw [hcard] at hh
    rwa [← Nat.card_congr (subgroupOfEquivOfLe
      (show Q R p.a ⊓ U R p.a' ≤ U R p.a' from inf_le_right)).toEquiv,
      inf_subgroupOf_right] at hh
  have hprod := C.index_mul_card
  rw [modules.natural.card_at p.a' p.end_color] at hprod
  have hne : C.index ≠ 1 := by
    intro hi
    have hle : U R p.a' ≤ Q R p.a := relIndex_eq_one.mp hi
    have hreversed := source.critical_reverse geometry p.a p.color_a p.a' p.end_color p.critical
    have hindex : (Q R p.a).relIndex (Z R p.a') = 1 := by
      rw [s.critical_Z_index_eq_U geometry p.a' p.end_color p.a hreversed]
      exact relIndex_eq_one.mpr hle
    exact hreversed.2 (relIndex_eq_one.mp hindex)
  change C.index = 2
  have hpositive : 0 < C.index := by nlinarith
  have hlower : 2 ≤ C.index := by omega
  nlinarith

omit [Finite M] in
theorem H_card_eq_base (a : Vertex R) (ha : color R a = false) :
    Nat.card (H R a) = Nat.card (H R (alpha R)) := by
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  have hh := H_act R g (alpha R)
  simp only [alpha, act_mVertex, one_mul] at hh
  change H R (mVertex R g) = (H R (alpha R)).map (MulAut.conj g⁻¹).toMonoidHom at hh
  rw [hh, ← Nat.card_congr ((H R (alpha R)).equivMapOfInjective
    (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).toEquiv]

theorem H_card_of_radius_moving (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (hcard : 4 ≤ Nat.card (⁅V R p.a, Vcirc R p.c⁆ : Subgroup (FreeAmalgam R))) :
    4 ≤ Nat.card (H R p.a) := by
  have hVc : Vcirc R p.c ≤ V R p.c := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer p.c).trans (V_normalized p.c))
  have hHQ : H R p.c ≤ Q R p.c := (Subgroup.commutator_le_sup _ _).trans
    (sup_le (hVc.trans (geometry.V_le_Q hb p.c p.before_color)) le_rfl)
  let := finite_stabilizer R p.c
  let : Finite (H R p.c) := Finite.of_injective
    (inclusion (hHQ.trans (show Q R p.c ≤ stabilizer R p.c from fun _ hx => hx.1)))
    (inclusion_injective _)
  have hle : ⁅V R p.a, Vcirc R p.c⁆ ≤ H R p.c := by
    rw [commutator_comm]
    exact commutator_mono le_rfl p.trapped
  calc
    4 ≤ Nat.card (⁅V R p.a, Vcirc R p.c⁆ : Subgroup (FreeAmalgam R)) := hcard
    _ ≤ Nat.card (H R p.c) := card_le_of_le hle
    _ = Nat.card (H R p.a) :=
      (H_card_eq_base p.c p.before_color).trans (H_card_eq_base p.a p.color_a).symm

end Initial
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape
