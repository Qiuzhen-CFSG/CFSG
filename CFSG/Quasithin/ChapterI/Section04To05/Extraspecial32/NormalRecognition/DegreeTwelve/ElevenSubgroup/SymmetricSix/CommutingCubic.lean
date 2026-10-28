module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.SymmetricSix.CommutingCubic.Reduction
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.SymmetricSix.CommutingCubic.OddComplement
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Census.Orbits
public import Theory.GroupAction.KleinFourCardinality
public import Mathlib.GroupTheory.FixedPointFree

/-!
# The final four-group argument for the commuting cubic

The odd subgroup supplied by the transfer step is acted on by the commuting
involutions `u` and `z`. Its common fixed subgroup is trivial, since `u`
inverts the fixed cubic of `z`. Brauer--Wielandt therefore gives
`|P| = 3 |C_P(u)| |C_P(uz)|`. Fusion with `z` bounds each odd fixed subgroup
by order three; the additional three-part forces `|P|` to be nine or 27
and at least one of the two fixed subgroups to have order three.

On either fixed subgroup, conjugation by `z` is an actual fixed-point-free
involution. Thus it acts by inversion on the chosen subgroup itself. This
avoids mistaking inversion of a quotient for inversion of its chosen lifts.

The final theorem `commutingCubicData` discharges the transfer input using
the actual odd complement and obtains fusion of `uz` from the local
outside-core orbit. It constructs all fields of `CommutingCubicData` from
the source hypotheses and the explicit earlier `SourceGeometry`, without
choosing between its two ambient orders.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemma 4.5 and its final observation, p.40.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.CommutingCubic
open Subgroup
variable {G : Type*} [Group G] [Finite G] {z : G}

private theorem centralizer_card_of_fused (h : Hypotheses z) {v : G}
    (hv : IsConj z v) : Nat.card (Centralizer v) = 192 := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hv
  have hc : Nat.card (Centralizer z) = Nat.card (Centralizer (g * z * g⁻¹)) := by
    apply Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj g).toEquiv ?_)
    intro x
    change x ∈ Centralizer z ↔ MulAut.conj g x ∈ Centralizer (MulAut.conj g z)
    simp only [mem_centralizer_singleton_iff]
    constructor
    · intro he
      simpa only [map_mul] using congrArg (MulAut.conj g) he
    · intro he
      apply (MulAut.conj g).injective
      simpa only [map_mul] using he
  exact hc.symm.trans h.centralizer_card

private theorem fixed_card_cases {h : Hypotheses z} {a : SourceGeometry h}
    (o : OddCentralizerData h a) {v : G} (hv : IsConj z v) :
    Nat.card (o.P ⊓ Centralizer v : Subgroup G) = 1 ∨
      Nat.card (o.P ⊓ Centralizer v : Subgroup G) = 3 := by
  have hd := card_dvd_of_le (show o.P ⊓ Centralizer v ≤ Centralizer v from inf_le_right)
  rw [centralizer_card_of_fused h hv] at hd
  have ho := Odd.of_dvd_nat o.odd
    (card_dvd_of_le (show o.P ⊓ Centralizer v ≤ o.P from inf_le_left))
  have hcop := ho.coprime_two_right.pow_right 6
  have hthree : Nat.card (o.P ⊓ Centralizer v : Subgroup G) ∣ 3 :=
    hcop.dvd_of_dvd_mul_left (by convert hd using 1)
  exact Nat.prime_three.eq_one_or_self_of_dvd _ hthree

private theorem common_fixed_eq_one {h : Hypotheses z} {a : SourceGeometry h}
    (o : OddCentralizerData h a) {v : G} (hv : v = a.u ∨ v = a.u * z)
    {x : G} (hxP : x ∈ o.P) (hxz : x ∈ Centralizer z) (hxv : x ∈ Centralizer v) :
    x = 1 := by
  have hx : x ∈ cubicInG h := o.fixed_z ▸ (show x ∈ o.P ⊓ Centralizer z from ⟨hxP, hxz⟩)
  have hi := choice_inverts_X a hv x hx
  have hc : v * x * v⁻¹ = x :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hxv).symm
  have hx2 : x ^ 2 = 1 := by
    rw [hc] at hi
    calc
      x ^ 2 = x * x := pow_two x
      _ = x⁻¹ * x := congrArg (· * x) hi
      _ = 1 := inv_mul_cancel x
  have hx3 : orderOf x ∣ 3 := by
    have hd := orderOf_dvd_natCard (⟨x, hx⟩ : cubicInG h)
    rw [cubicInG_card, ← Subgroup.orderOf_coe] at hd
    exact hd
  apply orderOf_eq_one_iff.mp
  exact Nat.dvd_one.mp (Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hx2) hx3)

private noncomputable def conjOn (P : Subgroup G) (v : G)
    (hv : v ∈ normalizer (P : Set G)) : MulAut P := P.normalizerMonoidHom ⟨v, hv⟩

omit [Finite G] in
private theorem conjOn_involutive (P : Subgroup G) (v : G)
    (hv : v ∈ normalizer (P : Set G)) (hv2 : v ^ 2 = 1) :
    Function.Involutive (conjOn P v hv) := by
  intro x
  apply Subtype.ext
  change v * (v * (x : G) * v⁻¹) * v⁻¹ = x
  calc
    _ = v ^ 2 * x * (v ^ 2)⁻¹ := by rw [pow_two]; group
    _ = x := by rw [hv2]; simp

omit [Finite G] in
private theorem conjOn_fixed_card (P : Subgroup G) (v : G)
    (hv : v ∈ normalizer (P : Set G)) :
    Nat.card (conjOn P v hv).fixedSubgroup = Nat.card (P ⊓ Centralizer v : Subgroup G) := by
  let e : (conjOn P v hv).fixedSubgroup ≃ (P ⊓ Centralizer v : Subgroup G) := {
    toFun x := ⟨x.val, x.val.property, by
      apply mem_centralizer_singleton_iff.mpr
      have hh := congrArg Subtype.val ((MulAut.mem_fixedSubgroup _ _).mp x.property)
      change v * (x.val : G) * v⁻¹ = x.val at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm⟩
    invFun x := ⟨⟨x.val, x.property.1⟩, by
      apply (MulAut.mem_fixedSubgroup _ _).mpr
      apply Subtype.ext
      change v * x.val * v⁻¹ = x.val
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp x.property.2).symm⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact Nat.card_congr e

private theorem inverts_fixed {h : Hypotheses z} {a : SourceGeometry h}
    (o : OddCentralizerData h a) {v : G} (hv : v = a.u ∨ v = a.u * z)
    (x : G) (hx : x ∈ o.P ⊓ Centralizer v) : z * x * z⁻¹ = x⁻¹ := by
  have hcv : Commute z v := by
    rcases hv with rfl | rfl
    · exact (u_commutes_z a).symm
    · exact (u_commutes_z a).symm.mul_right (Commute.refl z)
  have hn : z ∈ normalizer ((o.P ⊓ Centralizer v : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨o.z_normalizes,
      (Centralizer v).le_normalizer (mem_centralizer_singleton_iff.mpr hcv)⟩
  let f := conjOn (o.P ⊓ Centralizer v) z hn
  have hfp : MonoidHom.FixedPointFree f := by
    intro y hy
    apply Subtype.ext
    have he := congrArg Subtype.val hy
    change z * (y : G) * z⁻¹ = y at he
    exact common_fixed_eq_one o hv y.property.1
      (mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he).symm) y.property.2
  have hfi : Function.Involutive f :=
    conjOn_involutive _ z hn (h.involution ▸ pow_orderOf_eq_one z)
  exact congrArg Subtype.val (congrFun (hfp.coe_eq_inv_of_involutive hfi) ⟨x, hx⟩)


/-- The source four-group formula, with literal ambient fixed subgroups. -/
public theorem OddCentralizerData.fixed_card_product {h : Hypotheses z} {a : SourceGeometry h}
    (o : OddCentralizerData h a) :
    Nat.card o.P = Nat.card (o.P ⊓ Centralizer a.u : Subgroup G) * 3 *
      Nat.card (o.P ⊓ Centralizer (a.u * z) : Subgroup G) := by
  let A := conjOn o.P a.u o.u_normalizes
  let B := conjOn o.P z o.z_normalizes
  have hA : Function.Involutive A :=
    conjOn_involutive _ _ _ (a.u_order ▸ pow_orderOf_eq_one a.u)
  have hB : Function.Involutive B :=
    conjOn_involutive _ _ _ (h.involution ▸ pow_orderOf_eq_one z)
  have hcomm : Commute A B := by
    have hc : Commute (⟨a.u, o.u_normalizes⟩ : normalizer (o.P : Set G))
        ⟨z, o.z_normalizes⟩ := Subtype.ext (u_commutes_z a).eq
    exact hc.map o.P.normalizerMonoidHom
  have hbot : A.fixedSubgroup ⊓ B.fixedSubgroup = ⊥ := by
    apply (eq_bot_iff_forall _).mpr
    intro x hx
    apply Subtype.ext
    have hu := congrArg Subtype.val ((MulAut.mem_fixedSubgroup _ _).mp hx.1)
    have hz := congrArg Subtype.val ((MulAut.mem_fixedSubgroup _ _).mp hx.2)
    change a.u * (x : G) * a.u⁻¹ = x at hu
    change z * (x : G) * z⁻¹ = x at hz
    exact common_fixed_eq_one o (Or.inl rfl) x.property
      (mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hz).symm)
      (mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hu).symm)
  have hcard := Theory.GroupAction.brauerWielandt_fixedSubgroup_card o.odd A B hA hB hcomm
  have hone : Nat.card (A.fixedSubgroup ⊓ B.fixedSubgroup : Subgroup o.P) = 1 :=
    card_eq_one.mpr hbot
  rw [hone, one_pow, mul_one] at hcard
  have hprod : A * B = conjOn o.P (a.u * z)
      ((normalizer (o.P : Set G)).mul_mem o.u_normalizes o.z_normalizes) :=
    (map_mul o.P.normalizerMonoidHom
      (⟨a.u, o.u_normalizes⟩ : normalizer (o.P : Set G)) ⟨z, o.z_normalizes⟩).symm
  rw [hprod] at hcard
  dsimp only [A, B] at hcard
  rw [conjOn_fixed_card, conjOn_fixed_card, conjOn_fixed_card,
    o.fixed_z, cubicInG_card] at hcard
  exact hcard

/-- Fusion and the four-group formula give precisely the two odd orders. -/
public theorem OddCentralizerData.card_cases {h : Hypotheses z} {a : SourceGeometry h}
    (o : OddCentralizerData h a) (huz : IsConj z (a.u * z)) :
    Nat.card o.P = 9 ∨ Nat.card o.P = 27 := by
  have hc := o.fixed_card_product
  have hdiv := o.nine_dvd
  rcases fixed_card_cases o a.u_fused with hu | hu <;>
    rcases fixed_card_cases o huz with huz | huz <;>
    rw [hu, huz] at hc <;> norm_num at hc
  · rw [hc] at hdiv
    norm_num at hdiv
  · exact Or.inl hc
  · exact Or.inl hc
  · exact Or.inr hc

/-- The nontrivial fixed subgroup already has the required order three. -/
private theorem exists_fixed_cubic {h : Hypotheses z} {a : SourceGeometry h}
    (o : OddCentralizerData h a) (huz : IsConj z (a.u * z)) :
    ∃ v : G, (v = a.u ∨ v = a.u * z) ∧ orderOf v = 2 ∧ IsConj z v ∧
      Nat.card (o.P ⊓ Centralizer v : Subgroup G) = 3 := by
  rcases fixed_card_cases o a.u_fused with hu | hu
  · have hzu : Nat.card (o.P ⊓ Centralizer (a.u * z) : Subgroup G) = 3 := by
      rcases fixed_card_cases o huz with hc | hc
      · have hh := o.fixed_card_product
        rw [hu, hc] at hh
        have hd := o.nine_dvd
        rw [hh] at hd
        norm_num at hd
      · exact hc
    exact ⟨a.u * z, Or.inr rfl, uz_order a, huz, hzu⟩
  · exact ⟨a.u, Or.inl rfl, a.u_order, a.u_fused, hu⟩

end CommutingCubic

open CommutingCubic Subgroup
variable {G : Type*} [Group G] [Finite G] {z : G}
/-- The concluding construction in 4.5, conditional on its transfer
input and the fusion of the second allowed involution. -/
public theorem commutingCubicData_of_oddCentralizer {h : Hypotheses z} {a : SourceGeometry h}
    (o : OddCentralizerData h a) (huz : IsConj z (a.u * z)) :
    Nonempty (CommutingCubicData h a) := by
  obtain ⟨v, hv, hv2, hvf, hvc⟩ := exists_fixed_cubic o huz
  refine ⟨{
    u := v
    u_choice := hv
    u_order := hv2
    u_fused := hvf
    X1 := o.P ⊓ Centralizer v
    card_X1 := hvc
    X1_centralizes_X := inf_le_left.trans o.le_centralizer
    z_inverts_X1 := inverts_fixed o hv
    u_centralizes_X1 := ?_
    centralizer_X_card := ?_ }⟩
  · intro x hx
    exact (mem_centralizer_singleton_iff.mp hx.2).symm
  · rw [o.centralizer_card]
    rcases o.card_cases huz with hc | hc
    · exact Or.inl (by rw [hc])
    · exact Or.inr (by rw [hc])

/-- Aschbacher 4.5, including its final centralizer-order observation.
The source geometry is supplied by the earlier local analysis; both the odd
complement and fusion of the alternate involution are constructed here. -/
public theorem commutingCubicData (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) (d : FusionEightData z)
    (a : SourceGeometry h) : Nonempty (CommutingCubicData h a) := by
  let selected : SelectedFusionData h := {
    g := a.g
    fused_mem := a.fused_mem
    fused_ne := a.fused_ne
    intersection_elementary := a.intersection_elementary
    intersection_card := a.intersection_card
    intersection_ne_fusion := a.intersection_ne_fusion
    u := a.u
    u_order := a.u_order
    u_centralizes := a.u_centralizes
    u_conjugate_core := a.u_conjugate_core
    u_not_core := a.u_not_core
    u_fused := a.u_fused
    u_inverts_X := a.u_inverts_X }
  have orbits := Census.orbitData_of_quaternion_normal h hn d selected
  have huz : IsConj z (a.u * z) :=
    uz_fused_of_outside_transitive a orbits.outside_transitive
  obtain ⟨o⟩ := oddCentralizerData h a
  exact commutingCubicData_of_oddCentralizer o huz

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup
