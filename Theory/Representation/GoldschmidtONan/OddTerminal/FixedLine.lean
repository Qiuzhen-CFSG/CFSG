module

public import Theory.Representation.GoldschmidtONan.OrbitGeometry.Transport
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The fixed line in the odd transitive O'Nan case

The stabilizer of the fixed space preserves the moved space. The supplied
suborbit geometry therefore identifies its orbits with the actual Y-orbits.
For an orbit member contained in the moved space, its Y-stabilizer has order
`|fixedSpace ρ Y| - 1`; for a mixed orbit member that stabilizer is trivial.
If the fixed dimension exceeds one, the former suborbit is strictly shorter.

Reversing an ordered pair preserves its suborbit size: the two corresponding
two-point stabilizers are conjugate, so orbit–stabilizer gives equal lengths.
Consequently a reversed moved-space pair lies in the same suborbit and some
group element exchanges its two distinct members. An element of odd order
cannot do this. Transitivity on nonzero vectors supplies a moved-space orbit
member, completing the fixed-line reduction without a solvability theorem.

Source: GLS, Number 2, Chapter C, Proposition 14.2, Step 4,
`refs/KGroup/GLS2/ChapterC.tex`. The proof uses only the nonzero-transitivity
clause of `TransitiveGeometry`; its other two clauses are unnecessary here.
-/

namespace Representation.GoldschmidtONan
variable {G A : Type*} [Group G] [MulAction G A]

private def pairedStabilizerEquiv (a : A) (g : G) :
    MulAction.stabilizer (MulAction.stabilizer G a) (g • a) ≃
      MulAction.stabilizer (MulAction.stabilizer G a) (g⁻¹ • a) where
  toFun x := ⟨⟨g⁻¹ * x.val.val * g, by
    change (g⁻¹ * x.val.val * g) • a = a
    have hx : x.val.val • (g • a) = g • a := x.property
    simp only [mul_smul, hx, inv_smul_smul]⟩, by
    change (g⁻¹ * x.val.val * g) • (g⁻¹ • a) = g⁻¹ • a
    have hx : x.val.val • a = a := x.val.property
    simp only [mul_smul, smul_inv_smul, hx]⟩
  invFun x := ⟨⟨g * x.val.val * g⁻¹, by
    change (g * x.val.val * g⁻¹) • a = a
    have hx : x.val.val • (g⁻¹ • a) = g⁻¹ • a := x.property
    simp only [mul_smul, hx, smul_inv_smul]⟩, by
    change (g * x.val.val * g⁻¹) • (g • a) = g • a
    have hx : x.val.val • a = a := x.val.property
    simp only [mul_smul, inv_smul_smul, hx]⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv x := by ext; simp [mul_assoc]

private theorem paired_suborbit_card [Finite G] (a : A) (g : G) :
    Nat.card (MulAction.orbit (MulAction.stabilizer G a) (g • a)) =
      Nat.card (MulAction.orbit (MulAction.stabilizer G a) (g⁻¹ • a)) := by
  have hc := Nat.card_congr (pairedStabilizerEquiv a g)
  have hp (b : A) := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup (MulAction.stabilizer G a) b)
  simp only [Nat.card_prod] at hp
  have hpos : 0 < Nat.card (MulAction.stabilizer (MulAction.stabilizer G a) (g⁻¹ • a)) :=
    Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [← hc]
  exact (hp (g • a)).trans (hc ▸ (hp (g⁻¹ • a)).symm)

private theorem no_swap_of_odd [Finite G] (ho : Odd (Nat.card G)) {a b : A} (hab : a ≠ b)
    {g : G} (ha : g • a = b) (hb : g • b = a) : False := by
  have hgodd : Odd (orderOf g) := ho.of_dvd_nat (orderOf_dvd_natCard g)
  obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime hgodd.coprime_two_left
  have hs : g ^ 2 ∈ MulAction.stabilizer G a := by
    change (g ^ 2) • a = a
    rw [pow_two, mul_smul, ha, hb]
  have hg : g ∈ MulAction.stabilizer G a := hn ▸ (MulAction.stabilizer G a).pow_mem hs n
  exact hab (hg.symm.trans ha)
end Representation.GoldschmidtONan

namespace Representation.GoldschmidtONan
open BinaryOffender RegularCyclicNormalClosure
variable {X V : Type*} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) X V} {Y : Subgroup X}

local instance orbitAction : MulAction X (fixedOrbit ρ Y) where
  smul x W := ⟨W.val.map (ρ x), map_mem_fixedOrbit W.property x⟩
  one_smul W := Subtype.ext (orbit_map_one W.val)
  mul_smul x y W := Subtype.ext (orbit_map_mul W.val x y)

private noncomputable def basePoint (ρ : Representation (ZMod 2) X V) (Y : Subgroup X) :
    fixedOrbit ρ Y := ⟨fixedSpace ρ Y, fixed_mem_fixedOrbit⟩

private theorem actor_fixes_base (y : Y) : (y : X) • basePoint ρ Y = basePoint ρ Y :=
  Subtype.ext (fixed_map_actor y)

private theorem suborbit_same_type (h : Input ρ Y) (hs : SuborbitGeometry ρ Y)
    (W U : fixedOrbit ρ Y) (hW : W ≠ basePoint ρ Y) (hU : U ≠ basePoint ρ Y)
    (ht : (W.val ≤ displacementSpan ρ Y ⊤) ↔ (U.val ≤ displacementSpan ρ Y ⊤)) :
    U ∈ MulAction.orbit Y W := by
  have hW' : W.val ≠ fixedSpace ρ Y := fun he => hW (Subtype.ext he)
  have hU' : U.val ≠ fixedSpace ρ Y := fun he => hU (Subtype.ext he)
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (h.orbit_ne_bot U.property)
  have huF : u ∉ fixedSpace ρ Y := fun hf => hu0
    (Submodule.disjoint_def.mp (h.orbit_disjoint_fixed U.property hU') u hu hf)
  have hun : u ∈ nonzeroSuborbitUnion ρ Y W.val := by
    rcases hs W.val W.property hW' with hm | hm
    · rw [hm.2.1]
      exact ⟨ht.mp hm.1 hu, hu0⟩
    · rw [hm.2.2]
      refine ⟨huF, ?_⟩
      have hn : ¬ W.val ≤ displacementSpan ρ Y ⊤ := by
        intro hle
        exact h.orbit_ne_bot W.property
          (eq_bot_iff.mpr fun v hv => Submodule.disjoint_def.mp hm.1 v hv (hle hv))
      rcases hs U.val U.property hU' with hle | hdis
      · exact False.elim (hn (ht.mpr hle.1))
      · exact fun huD => hu0 (Submodule.disjoint_def.mp hdis.1 u hu huD)
  obtain ⟨_, y, hy⟩ := hun
  refine MulAction.mem_orbit_iff.mpr ⟨y, Subtype.ext ?_⟩
  exact h.orbit_eq_of_common_nonzero (map_mem_fixedOrbit W.property y) U.property hy hu hu0

private theorem stabilizer_orbit_eq_actor (h : Input ρ Y) (hs : SuborbitGeometry ρ Y)
    (W : fixedOrbit ρ Y) :
    MulAction.orbit (MulAction.stabilizer X (basePoint ρ Y)) W = MulAction.orbit Y W := by
  ext U
  constructor
  · rintro ⟨x, rfl⟩
    change x • W ∈ MulAction.orbit Y W
    by_cases hW : W = basePoint ρ Y
    · have he : x • W = W := hW ▸ x.property
      rw [he]
      exact MulAction.mem_orbit_self W
    have hU : x • W ≠ basePoint ρ Y := by
      intro he
      apply hW
      exact (MulAction.injective (x : X)) (he.trans x.property.symm)
    apply suborbit_same_type h hs W (x • W) hW hU
    have hx : (fixedSpace ρ Y).map (ρ x) = fixedSpace ρ Y :=
      congrArg Subtype.val x.property
    change W.val ≤ displacementSpan ρ Y ⊤ ↔ W.val.map (ρ x) ≤ displacementSpan ρ Y ⊤
    conv_rhs => rw [← h.moved_map_of_fixed_map x hx]
    exact (Submodule.map_le_map_iff_of_injective (action_injective (ρ := ρ) (x : X)) _ _).symm
  · rintro ⟨y, rfl⟩
    exact MulAction.mem_orbit_iff.mpr ⟨⟨y, actor_fixes_base y⟩, rfl⟩


private theorem moved_stabilizer_card [Finite X] [Finite V]
    (h : Input ρ Y) (hs : SuborbitGeometry ρ Y)
    (W : fixedOrbit ρ Y) (hle : W.val ≤ displacementSpan ρ Y ⊤) :
    Nat.card (MulAction.stabilizer Y W) = Nat.card (fixedSpace ρ Y) - 1 := by
  classical
  have hne : W.val ≠ fixedSpace ρ Y := by
    intro he
    have hb : fixedSpace ρ Y ≤ displacementSpan ρ Y ⊤ := he ▸ hle
    exact h.fixed_nontrivial (eq_bot_iff.mpr fun v hv =>
      Submodule.disjoint_def.mp h.split.disjoint v hv (hb hv))
  have ht : ∀ v ∈ W.val, v ≠ 0 → ∀ w ∈ W.val, w ≠ 0 →
      ∃ y : Y, W.val.map (ρ y) = W.val ∧ ρ y v = w := by
    rcases hs W.val W.property hne with hm | hm
    · exact hm.2.2
    · exact False.elim (h.orbit_ne_bot W.property
        (eq_bot_iff.mpr fun v hv => Submodule.disjoint_def.mp hm.1 v hv (hle hv)))
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (h.orbit_ne_bot W.property)
  let f : MulAction.stabilizer Y W → {w : W.val // w ≠ 0} := fun y =>
    ⟨⟨ρ y.val v, by
      have hy : W.val.map (ρ y.val) = W.val := congrArg Subtype.val y.property
      exact hy ▸ (Submodule.mem_map_of_mem hv)⟩, by
      intro he
      apply hv0
      apply action_injective (ρ := ρ) (y.val : X)
      simpa using congrArg (fun w : W.val => (w : V)) he⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b he
      have he' : ρ a.val v = ρ b.val v :=
        congrArg (fun w : {w : W.val // w ≠ 0} => (w.val : V)) he
      obtain ⟨c, hc, hu⟩ := h.regular v (hle hv) hv0 (ρ b.val v)
        (moved_mem_action b.val (hle hv))
        (fun hz => hv0 (action_injective (ρ := ρ) (b.val : X) (by simpa using hz)))
      exact Subtype.ext ((hu a.val he').trans (hu b.val rfl).symm)
    · intro w
      obtain ⟨y, hy, hyv⟩ := ht v hv hv0 w.val w.val.property
        (fun he => w.property (Subtype.ext he))
      exact ⟨⟨y, Subtype.ext hy⟩, Subtype.ext (Subtype.ext hyv)⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf)]
  let := Fintype.ofFinite W.val
  let := Fintype.ofFinite {w : W.val // w ≠ 0}
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
    ← Nat.card_eq_fintype_card, card_eq_fixed_of_mem_fixedOrbit W.property]

private theorem mixed_orbit_card [Finite X]
    (hs : SuborbitGeometry ρ Y) (W : fixedOrbit ρ Y)
    (hne : W ≠ basePoint ρ Y) (hle : ¬ W.val ≤ displacementSpan ρ Y ⊤) :
    Nat.card (MulAction.orbit Y W) = Nat.card Y := by
  have hfree : ∀ y : Y, W.val.map (ρ y) = W.val → y = 1 := by
    rcases hs W.val W.property (fun he => hne (Subtype.ext he)) with hm | hm
    · exact False.elim (hle hm.1)
    · exact hm.2.1
  have hstab : MulAction.stabilizer Y W = ⊥ := by
    apply eq_bot_iff.mpr
    intro y hy
    exact Subgroup.mem_bot.mpr (hfree y (congrArg Subtype.val hy))
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Y W)
  simpa [Nat.card_prod, hstab] using hc


private theorem exists_moved_orbit [Finite X] (h : Input ρ Y)
    (hs : SuborbitGeometry ρ Y) (ht : NonzeroTransitive ρ) :
    ∃ W : fixedOrbit ρ Y, W.val ≤ displacementSpan ρ Y ⊤ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h.fixed_nontrivial
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h.moved_ne_bot
  obtain ⟨x, hx⟩ := ht v hv0 d hd0
  let W : fixedOrbit ρ Y := ⟨(fixedSpace ρ Y).map (ρ x), ⟨x, rfl⟩⟩
  have hdW : d ∈ W.val := ⟨v, hv, hx⟩
  have hne : W.val ≠ fixedSpace ρ Y := by
    intro he
    exact hd0 (Submodule.disjoint_def.mp h.split.disjoint d (he ▸ hdW) hd)
  refine ⟨W, ?_⟩
  rcases hs W.val W.property hne with hm | hm
  · exact hm.1
  · exact False.elim (hd0 (Submodule.disjoint_def.mp hm.1 d hdW hd))

/-- The odd-order, transitive branch of O'Nan's argument has a fixed line
(GLS, Number 2, Chapter C, Proposition 14.2, Step 4). -/
public theorem Input.fixed_finrank_one_of_odd_transitiveGeometry [Finite X] [Finite V]
    (h : Input ρ Y) (hs : SuborbitGeometry ρ Y) (ht : TransitiveGeometry ρ Y)
    (ho : Odd (Nat.card X)) : Module.finrank (ZMod 2) (fixedSpace ρ Y) = 1 := by
  classical
  let : Nontrivial (fixedSpace ρ Y) := Submodule.nontrivial_iff_ne_bot.mpr h.fixed_nontrivial
  have hkpos := Module.finrank_pos (R := ZMod 2) (M := fixedSpace ρ Y)
  by_contra hk
  have hk2 : 2 ≤ Module.finrank (ZMod 2) (fixedSpace ρ Y) := by omega
  have hFcard : 2 < Nat.card (fixedSpace ρ Y) := by
    let := Fintype.ofFinite (fixedSpace ρ Y)
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hk2
    norm_num at hp ⊢
    omega
  obtain ⟨W, hW⟩ := exists_moved_orbit h hs ht.1
  have hWne : W ≠ basePoint ρ Y := by
    intro he
    have hle : fixedSpace ρ Y ≤ displacementSpan ρ Y ⊤ := by
      simpa only [he, basePoint] using hW
    exact h.fixed_nontrivial (eq_bot_iff.mpr fun v hv =>
      Submodule.disjoint_def.mp h.split.disjoint v hv (hle hv))
  have hstab : 1 < Nat.card (MulAction.stabilizer Y W) := by
    rw [moved_stabilizer_card h hs W hW]
    omega
  have horbit : Nat.card (MulAction.orbit Y W) < Nat.card Y := by
    have hp := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Y W)
    rw [Nat.card_prod] at hp
    have : Nonempty (MulAction.orbit Y W) := ⟨⟨W, MulAction.mem_orbit_self W⟩⟩
    have hn : 0 < Nat.card (MulAction.orbit Y W) := Nat.card_pos
    nlinarith
  obtain ⟨x, hx⟩ : ∃ x : X, x • basePoint ρ Y = W := by
    obtain ⟨x, hx⟩ := W.property
    exact ⟨x, Subtype.ext hx⟩
  let U : fixedOrbit ρ Y := x⁻¹ • basePoint ρ Y
  have hUne : U ≠ basePoint ρ Y := by
    intro he
    have hh := congrArg (fun P : fixedOrbit ρ Y => x • P) he
    simp only [U, smul_inv_smul, hx] at hh
    exact hWne hh.symm
  have hpair : Nat.card (MulAction.orbit Y W) = Nat.card (MulAction.orbit Y U) := by
    have hp := paired_suborbit_card (basePoint ρ Y) x
    rw [hx, stabilizer_orbit_eq_actor h hs W, stabilizer_orbit_eq_actor h hs U] at hp
    exact hp
  have hU : U.val ≤ displacementSpan ρ Y ⊤ := by
    by_contra hU
    rw [mixed_orbit_card hs U hUne hU] at hpair
    omega
  obtain ⟨y, hy⟩ := (MulAction.mem_orbit_iff).mp
    (suborbit_same_type h hs W U hWne hUne (iff_of_true hW hU))
  apply no_swap_of_odd ho hWne.symm (g := x * (y : X))
  · rw [mul_smul, actor_fixes_base y, hx]
  · rw [mul_smul]
    change x • ((y : Y) • W) = basePoint ρ Y
    rw [hy]
    exact smul_inv_smul x (basePoint ρ Y)

end Representation.GoldschmidtONan
