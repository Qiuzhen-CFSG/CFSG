/-
Two structural steps towards the converse of the Suzuki classification:

* `hypothesisA_transport` moves Hypothesis (A) along an equivariant isomorphism
  of group actions;
* `hypothesisA_lift` lifts Hypothesis (A) from a normal subgroup of odd index to
  the whole group.
-/

module

public import BenderSuzuki.PFchapter1section1.Basic
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise

namespace BenderSuzuki
namespace Converse

open PFchapter1section1 PFAppendixIII
open scoped Pointwise

universe u v

/-! ### Orbit–stabilizer in a doubly transitive action -/

/-- Orbit–stabilizer, in `Nat.card` form. -/
public theorem card_stabilizer_mul_card_orbit {G X : Type*} [Group G] [MulAction G X]
    [Finite G] (b : X) :
    Nat.card (MulAction.stabilizer G b) * Nat.card (MulAction.orbit G b) = Nat.card G := by
  rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G b)]
  exact Subgroup.card_mul_index _

/-- In a doubly transitive action of a finite group, a one-point stabilizer has
order `|Ω| - 1` times the order of a two-point stabilizer: the stabilizer of `a`
is transitive on the remaining points. -/
public theorem card_stabilizer_eq_twoPoint_mul
    {K Ω : Type*} [Group K] [Finite K] [MulAction K Ω] [Finite Ω]
    (h2 : MulAction.IsMultiplyPretransitive K Ω 2) {a b : Ω} (hba : b ≠ a) :
    Nat.card (MulAction.stabilizer K a) =
      Nat.card ((MulAction.stabilizer K a ⊓ MulAction.stabilizer K b : Subgroup K)) *
        (Nat.card Ω - 1) := by
  classical
  haveI : Fintype Ω := Fintype.ofFinite _
  have h2' : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : K, g • x = z ∧ g • y = w :=
    MulAction.is_two_pretransitive_iff.1 h2
  have horb : MulAction.orbit (MulAction.stabilizer K a) b = {z : Ω | z ≠ a} := by
    ext z
    constructor
    · rintro ⟨h, rfl⟩
      intro hcon
      apply hba
      have hfix : (h : K) • a = a := h.2
      have hcon' : (h : K) • b = a := hcon
      have hinvfix : ((h : K))⁻¹ • a = a := inv_smul_eq_iff.2 hfix.symm
      have h1 : ((h : K))⁻¹ • ((h : K) • b) = ((h : K))⁻¹ • a := by rw [hcon']
      rw [inv_smul_smul] at h1
      rw [h1]
      exact hinvfix
    · intro hz
      obtain ⟨g, hg1, hg2⟩ := @h2' a b a z (Ne.symm hba) (Ne.symm hz)
      exact ⟨⟨g, hg1⟩, hg2⟩
  have hstabeq : MulAction.stabilizer (MulAction.stabilizer K a) b =
      (MulAction.stabilizer K a ⊓ MulAction.stabilizer K b).subgroupOf
        (MulAction.stabilizer K a) := by
    ext x
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have h := card_stabilizer_mul_card_orbit (G := MulAction.stabilizer K a) b
  rw [hstabeq, horb,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : MulAction.stabilizer K a ⊓ MulAction.stabilizer K b ≤
        MulAction.stabilizer K a)).toEquiv] at h
  have hcompl : Nat.card {z : Ω | z ≠ a} = Nat.card Ω - 1 := by
    show Nat.card {z : Ω // ¬ (z = a)} = Nat.card Ω - 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card]
  rw [hcompl] at h
  exact h.symm

/-! ### Transport along an equivariant isomorphism -/

section Transport

variable {G₁ G₂ Ω₁ Ω₂ : Type*}
  [Group G₁] [Finite G₁] [MulAction G₁ Ω₁] [Finite Ω₁]
  [Group G₂] [Finite G₂] [MulAction G₂ Ω₂] [Finite Ω₂]

omit [Finite G₁] [Finite G₂] [Finite Ω₁] [Finite Ω₂] in
/-- Membership in the image of a subgroup under an isomorphism. -/
public theorem mem_map_mulEquiv (e : G₁ ≃* G₂) (K : Subgroup G₁) (x : G₂) :
    x ∈ K.map (e : G₁ →* G₂) ↔ e.symm x ∈ K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨e.symm x, h, by simp⟩

omit [Finite G₁] [Finite G₂] [Finite Ω₁] [Finite Ω₂] in
/-- Right conjugation commutes with pushing a subgroup forward along an
isomorphism. -/
public theorem map_rightConjugate (e : G₁ ≃* G₂) (H : Subgroup G₁) (g : G₁) :
    (rightConjugate H g).map (e : G₁ →* G₂)
      = rightConjugate (H.map (e : G₁ →* G₂)) (e g) := by
  rw [rightConjugate, rightConjugate, Subgroup.conjBy, Subgroup.conjBy,
    Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj, mul_assoc]

omit [Finite G₁] [Finite G₂] [Finite Ω₁] [Finite Ω₂] in
/-- Point stabilizers correspond under an equivariant isomorphism. -/
public theorem map_stabilizer (e : G₁ ≃* G₂) (f : Ω₁ ≃ Ω₂)
    (hef : ∀ (g : G₁) (ω : Ω₁), f (g • ω) = e g • f ω) (ω : Ω₁) :
    (MulAction.stabilizer G₁ ω).map (e : G₁ →* G₂) = MulAction.stabilizer G₂ (f ω) := by
  ext x
  rw [mem_map_mulEquiv, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  have hx := hef (e.symm x) ω
  rw [MulEquiv.apply_symm_apply] at hx
  constructor
  · intro h
    rw [h] at hx
    exact hx.symm
  · intro h
    rw [h] at hx
    exact f.injective hx

omit [Finite G₁] [Finite G₂] [Finite Ω₁] [Finite Ω₂] in
/-- Double transitivity transports along an equivariant isomorphism. -/
public theorem transport_two_pretransitive (e : G₁ ≃* G₂) (f : Ω₁ ≃ Ω₂)
    (hef : ∀ (g : G₁) (ω : Ω₁), f (g • ω) = e g • f ω)
    (h2 : MulAction.IsMultiplyPretransitive G₁ Ω₁ 2) :
    MulAction.IsMultiplyPretransitive G₂ Ω₂ 2 := by
  have h2' : ∀ {x y z w : Ω₁}, x ≠ y → z ≠ w → ∃ g : G₁, g • x = z ∧ g • y = w :=
    MulAction.is_two_pretransitive_iff.1 h2
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  obtain ⟨g, hg1, hg2⟩ := @h2' (f.symm a) (f.symm b) (f.symm c) (f.symm d)
    (fun h => hab (by simpa using congrArg f h)) (fun h => hcd (by simpa using congrArg f h))
  refine ⟨e g, ?_, ?_⟩
  · have := hef g (f.symm a)
    rw [hg1, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    exact this.symm
  · have := hef g (f.symm b)
    rw [hg2, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    exact this.symm

/-- **Hypothesis (A) transports along an equivariant isomorphism of actions.** -/
public theorem hypothesisA_transport (e : G₁ ≃* G₂) (f : Ω₁ ≃ Ω₂)
    (hef : ∀ (g : G₁) (ω : Ω₁), f (g • ω) = e g • f ω)
    {H D Q : Subgroup G₁} {t : G₁} (hA : HypothesisA G₁ Ω₁ H D Q t) :
    HypothesisA G₂ Ω₂ (H.map (e : G₁ →* G₂)) (D.map (e : G₁ →* G₂))
      (Q.map (e : G₁ →* G₂)) (e t) := by
  have hinj : Function.Injective (e : G₁ →* G₂) := e.injective
  have hcard : ∀ K : Subgroup G₁, Nat.card (K.map (e : G₁ →* G₂)) = Nat.card K :=
    fun K => Subgroup.card_map_of_injective hinj
  refine { A1 := ?_, A2 := ?_, A3 := ?_ }
  · obtain ⟨point, hpoint⟩ := hA.A1.point_stabilizer
    refine
      { two_transitive := transport_two_pretransitive e f hef hA.A1.two_transitive
        point_stabilizer := ⟨f point, by rw [hpoint, map_stabilizer e f hef]⟩
        involution_t := ⟨fun h => hA.A1.involution_t.1 (by
            have h2 := congrArg e.symm h
            rwa [MulEquiv.symm_apply_apply, map_one] at h2),
          by rw [← map_pow, hA.A1.involution_t.2, map_one]⟩
        t_not_mem_H := ?_
        D_eq := ?_
        Q_le_H := Subgroup.map_mono hA.A1.Q_le_H
        D_le_H := Subgroup.map_mono hA.A1.D_le_H
        Q_normal_in_H := ?_
        Q_disjoint_D := ?_
        Q_sup_D := ?_
        Q_even := by rw [hcard]; exact hA.A1.Q_even
        D_odd := by rw [hcard]; exact hA.A1.D_odd }
    · rw [mem_map_mulEquiv, MulEquiv.symm_apply_apply]
      exact hA.A1.t_not_mem_H
    · rw [hA.A1.D_eq, Subgroup.map_inf_eq _ _ _ hinj, map_rightConjugate]
    · rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hA.A1.Q_le_H)]
      intro q h hq hh
      rw [mem_map_mulEquiv] at hq hh ⊢
      have := (Subgroup.normal_subgroupOf_iff hA.A1.Q_le_H).1 hA.A1.Q_normal_in_H
        (e.symm q) (e.symm h) hq hh
      simpa using this
    · rw [Subgroup.disjoint_def]
      intro x hx1 hx2
      rw [mem_map_mulEquiv] at hx1 hx2
      have h1 := (Subgroup.disjoint_def.1 hA.A1.Q_disjoint_D) hx1 hx2
      have h2 := congrArg e h1
      rwa [MulEquiv.apply_symm_apply, map_one] at h2
    · rw [← Subgroup.map_sup, hA.A1.Q_sup_D]
  · refine ⟨fun {g₁ g₂} h => ?_⟩
    have h1 : (e.symm g₁ : G₁) = e.symm g₂ := by
      refine hA.A2.eq_of_smul_eq_smul (fun ω => ?_)
      apply f.injective
      rw [hef, hef, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, h]
    have h2 := congrArg e h1
    rwa [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h2
  · obtain ⟨E, hE4, hEsq⟩ := hA.A3
    refine ⟨E.map (e : G₁ →* G₂), by rw [hcard]; exact hE4, ?_⟩
    rintro ⟨_, x, hx, rfl⟩
    apply Subtype.ext
    have hx2 : (x : G₁) ^ 2 = 1 := by
      have h1 := hEsq ⟨x, hx⟩
      have h2 := congrArg (Subtype.val : E → G₁) h1
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
    rw [Subgroup.coe_pow]
    show (e x) ^ 2 = 1
    rw [← map_pow, hx2, map_one]

end Transport

/-! ### Lifting across a normal subgroup of odd index -/

section Lift

variable {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]

/-- **Hypothesis (A) lifts from a normal subgroup of odd index.**

If `L` is a normal subgroup of odd index in `G`, the action of `G` on `Ω` is
faithful, and the restricted action of `L` on `Ω` satisfies Hypothesis (A) with a
`2`-group in the role of `Q`, then `G` itself satisfies Hypothesis (A) on `Ω`.

The point stabilizer, the involution and the two-point stabilizer are read off
from the ones for `L`; the subgroup `Q` is unchanged, and stays normal in the
larger stabilizer because it absorbs every `2`-element of `H ⊓ L`. -/
public theorem hypothesisA_lift
    (L : Subgroup G) [hLnormal : L.Normal] (hodd : Odd (Nat.card (G ⧸ L)))
    (hfaith : FaithfulSMul G Ω)
    {H₀ D₀ Q₀ : Subgroup L} {t₀ : L}
    (hA : HypothesisA (↥L) Ω H₀ D₀ Q₀ t₀)
    (hQ2 : ∃ N : ℕ, Nat.card Q₀ = 2 ^ N) :
    ∃ (H D Q : Subgroup G) (t : G), HypothesisA G Ω H D Q t := by
  classical
  obtain ⟨N, hQN⟩ := hQ2
  have hQ2' : ∀ x : L, x ∈ Q₀ → (x : G) ^ (2 ^ N) = 1 := by
    intro x hx
    have h1 : (⟨x, hx⟩ : Q₀) ^ Nat.card Q₀ = 1 := pow_card_eq_one'
    rw [hQN] at h1
    have h2 := congrArg (Subtype.val : Q₀ → L) h1
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h2
    have h3 := congrArg (Subtype.val : L → G) h2
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h3
  obtain ⟨ω₀, hH₀⟩ := hA.A1.point_stabilizer
  set H : Subgroup G := MulAction.stabilizer G ω₀ with hHdef
  set t : G := (t₀ : G) with htdef
  set Q : Subgroup G := Q₀.map L.subtype with hQdef
  set D : Subgroup G := H ⊓ rightConjugate H t with hDdef
  -- double transitivity of the bigger group
  have h2L : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : L, g • x = z ∧ g • y = w :=
    MulAction.is_two_pretransitive_iff.1 hA.A1.two_transitive
  have h2G : MulAction.IsMultiplyPretransitive G Ω 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    obtain ⟨g, hg1, hg2⟩ := @h2L a b c d hab hcd
    exact ⟨(g : G), hg1, hg2⟩
  -- the two stabilizers
  have hH₀eq : H₀ = H.subgroupOf L := by
    rw [hH₀]; ext x
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, hHdef,
      MulAction.mem_stabilizer_iff]
    exact Iff.rfl
  have hKeq : H₀.map L.subtype = H ⊓ L := by
    rw [hH₀eq, Subgroup.subgroupOf_map_subtype]
  -- the involution
  have htne : t ≠ 1 := fun h => hA.A1.involution_t.1 (Subtype.ext h)
  have htsq : t ^ 2 = 1 := by
    have h := congrArg (Subtype.val : L → G) hA.A1.involution_t.2
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h
  have htnotH : t ∉ H := by
    intro hc
    exact hA.A1.t_not_mem_H (by rw [hH₀eq, Subgroup.mem_subgroupOf]; exact hc)
  -- the second base point
  set b : Ω := t⁻¹ • ω₀ with hbdef
  have hbne : b ≠ ω₀ := by
    intro hc
    apply htnotH
    rw [hHdef, MulAction.mem_stabilizer_iff]
    rw [hbdef] at hc
    have h : t • (t⁻¹ • ω₀) = t • ω₀ := by rw [hc]
    rwa [smul_inv_smul, eq_comm] at h
  have hDstab : D = H ⊓ MulAction.stabilizer G b := by
    rw [hDdef, hHdef, rightConjugate_stabilizer]
  have hD₀stab : D₀ = MulAction.stabilizer (↥L) ω₀ ⊓ MulAction.stabilizer (↥L) b := by
    have hpt : (t₀⁻¹ : ↥L) • ω₀ = b := by
      show ((t₀⁻¹ : ↥L) : G) • ω₀ = b
      rw [Subgroup.coe_inv, ← htdef, ← hbdef]
    rw [hA.A1.D_eq, hH₀, rightConjugate_stabilizer, hpt]
  -- the two orbit counts
  have hHcard : Nat.card H = Nat.card D * (Nat.card Ω - 1) := by
    rw [hDstab, hHdef]
    exact card_stabilizer_eq_twoPoint_mul h2G hbne
  have hH₀card : Nat.card H₀ = Nat.card D₀ * (Nat.card Ω - 1) := by
    rw [hD₀stab, hH₀]
    exact card_stabilizer_eq_twoPoint_mul hA.A1.two_transitive hbne
  have hΩpos : 0 < Nat.card Ω - 1 := by
    haveI : Nonempty Ω := ⟨b⟩
    have hne : Nat.card Ω ≠ 1 := by
      intro h
      obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.1 h
      exact hbne (hsub.allEq b ω₀)
    have hpos : 0 < Nat.card Ω := Nat.card_pos
    omega
  -- the semidirect decomposition inside `L`
  have hQ₀le := hA.A1.Q_le_H
  have hD₀le := hA.A1.D_le_H
  have hH₀prod : Nat.card Q₀ * Nat.card D₀ = Nat.card H₀ := by
    haveI : (Q₀.subgroupOf H₀).Normal := hA.A1.Q_normal_in_H
    have hdisj : Disjoint (Q₀.subgroupOf H₀) (D₀.subgroupOf H₀) := by
      rw [Subgroup.disjoint_def]
      intro x hx1 hx2
      rw [Subgroup.mem_subgroupOf] at hx1 hx2
      exact Subtype.ext ((Subgroup.disjoint_def.1 hA.A1.Q_disjoint_D) hx1 hx2)
    have hsup : Q₀.subgroupOf H₀ ⊔ D₀.subgroupOf H₀ = ⊤ := by
      apply Subgroup.map_injective H₀.subtype_injective
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.2 hQ₀le, inf_eq_left.2 hD₀le, hA.A1.Q_sup_D,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hmul : ((Q₀.subgroupOf H₀ : Set H₀)) * ((D₀.subgroupOf H₀ : Set H₀)) = Set.univ := by
      rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top]
    have hc := (Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul).card_mul
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ₀le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD₀le).toEquiv] at hc
  -- transferred cardinalities
  have hQcard : Nat.card Q = Nat.card Q₀ := Subgroup.card_subtype L Q₀
  have hKcard : Nat.card ((H ⊓ L : Subgroup G)) = Nat.card H₀ := by
    rw [← hKeq]; exact Subgroup.card_subtype L H₀
  have hD₀pos : 0 < Nat.card D₀ := Nat.card_pos
  have hQ₀pos : 0 < Nat.card Q₀ := Nat.card_pos
  have hQ₀len : Nat.card Q₀ = Nat.card Ω - 1 := by
    have h := hH₀prod
    rw [hH₀card] at h
    exact Nat.eq_of_mul_eq_mul_right hD₀pos (by rw [h]; ring)
  -- `Q` sits inside `H ⊓ L`
  have hQleK : Q ≤ H ⊓ L := by
    rw [hQdef, ← hKeq]
    exact Subgroup.map_mono hQ₀le
  have hQleH : Q ≤ H := le_trans hQleK inf_le_left
  -- `Q` is normal in `H ⊓ L`, with odd index there
  have hQnormK : (Q.subgroupOf (H ⊓ L)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hQleK]
    rintro q k ⟨y, hy, rfl⟩ hk
    have hkL : k ∈ L := hk.2
    have hkH₀ : (⟨k, hkL⟩ : L) ∈ H₀ := by
      rw [hH₀eq, Subgroup.mem_subgroupOf]; exact hk.1
    have hres := (Subgroup.normal_subgroupOf_iff hQ₀le).1 hA.A1.Q_normal_in_H
      y ⟨k, hkL⟩ hy hkH₀
    exact ⟨_, hres, rfl⟩
  have hindexodd : Odd (Nat.card ((H ⊓ L : Subgroup G) ⧸ Q.subgroupOf (H ⊓ L))) := by
    haveI := hQnormK
    have h1 : Nat.card (Q.subgroupOf (H ⊓ L)) *
        Nat.card ((H ⊓ L : Subgroup G) ⧸ Q.subgroupOf (H ⊓ L)) =
        Nat.card ((H ⊓ L : Subgroup G)) := Subgroup.card_mul_index _
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQleK).toEquiv, hQcard, hKcard,
      ← hH₀prod] at h1
    have h2 : Nat.card ((H ⊓ L : Subgroup G) ⧸ Q.subgroupOf (H ⊓ L)) = Nat.card D₀ :=
      Nat.eq_of_mul_eq_mul_left hQ₀pos h1
    rw [h2]
    exact hA.A1.D_odd
  -- every `2`-element of `H ⊓ L` lies in `Q`
  have hkey : ∀ x : G, x ∈ H ⊓ L → (∃ n : ℕ, x ^ (2 ^ n) = 1) → x ∈ Q := by
    rintro x hx ⟨n, hn⟩
    haveI := hQnormK
    set y : (H ⊓ L : Subgroup G) := ⟨x, hx⟩ with hy
    have hy2 : y ^ (2 ^ n) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hn
    have hd1 : orderOf (QuotientGroup.mk (s := Q.subgroupOf (H ⊓ L)) y) ∣ 2 ^ n := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← QuotientGroup.mk_pow, hy2, QuotientGroup.mk_one]
    have hd2 : orderOf (QuotientGroup.mk (s := Q.subgroupOf (H ⊓ L)) y) ∣
        Nat.card ((H ⊓ L : Subgroup G) ⧸ Q.subgroupOf (H ⊓ L)) := orderOf_dvd_natCard _
    have hcop : Nat.Coprime (2 ^ n)
        (Nat.card ((H ⊓ L : Subgroup G) ⧸ Q.subgroupOf (H ⊓ L))) := by
      refine Nat.Coprime.pow_left _ ?_
      refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 ?_
      intro hdvd
      rw [Nat.odd_iff] at hindexodd
      omega
    have hgcd : Nat.gcd (2 ^ n)
        (Nat.card ((H ⊓ L : Subgroup G) ⧸ Q.subgroupOf (H ⊓ L))) = 1 := hcop
    have hdd := Nat.dvd_gcd hd1 hd2
    rw [hgcd] at hdd
    have hq : (QuotientGroup.mk (s := Q.subgroupOf (H ⊓ L)) y) = 1 :=
      orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdd)
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq
    exact hq
  -- normality of `Q` in the bigger stabilizer
  have hQnormH : (Q.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hQleH]
    intro q h hq hh
    obtain ⟨y, hy, hyq⟩ := hq
    simp only [SetLike.mem_coe] at hy
    have hn := hQ2' y hy
    have hqpow : q ^ (2 ^ N) = 1 := by rw [← hyq]; exact hn
    refine hkey _ ⟨?_, ?_⟩ ⟨N, ?_⟩
    · exact H.mul_mem (H.mul_mem hh (hQleH ⟨y, hy, hyq⟩)) (H.inv_mem hh)
    · exact hLnormal.conj_mem _ (by rw [← hyq]; exact y.2) h
    · rw [conj_pow, hqpow, mul_one, mul_inv_cancel]
  -- the odd relative index of `L` in `H`
  have hrel : Nat.card ((H ⊓ L : Subgroup G)) * L.relIndex H = Nat.card H := by
    have h1 : Nat.card (L.subgroupOf H) * (L.subgroupOf H).index = Nat.card H :=
      Subgroup.card_mul_index _
    have h2 : Nat.card (L.subgroupOf H) = Nat.card ((H ⊓ L : Subgroup G)) := by
      have h3 := Subgroup.card_subtype H (L.subgroupOf H)
      rw [Subgroup.subgroupOf_map_subtype] at h3
      rw [← h3, inf_comm L H]
    rwa [h2] at h1
  have hreloddL : Odd (L.relIndex H) := by
    have hdvd : L.relIndex H ∣ Nat.card (G ⧸ L) :=
      Subgroup.relIndex_dvd_index_of_normal L H
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, Nat.odd_mul] at hodd
    exact hodd.1
  -- the order of the two-point stabilizer
  have hDodd : Odd (Nat.card D) := by
    have h1 : Nat.card D * (Nat.card Ω - 1) =
        Nat.card D₀ * L.relIndex H * (Nat.card Ω - 1) := by
      rw [← hHcard, ← hrel, hKcard, hH₀card]
      ring
    have h2 : Nat.card D = Nat.card D₀ * L.relIndex H :=
      Nat.eq_of_mul_eq_mul_right hΩpos h1
    rw [h2, Nat.odd_mul]
    exact ⟨hA.A1.D_odd, hreloddL⟩
  -- disjointness and the product decomposition of the bigger stabilizer
  have hQdisjD : Disjoint Q D := by
    rw [Subgroup.disjoint_def]
    rintro x ⟨y, hy, rfl⟩ hxD
    simp only [SetLike.mem_coe] at hy
    have hn := hQ2' y hy
    have h1 : orderOf ((y : G)) ∣ 2 ^ N := orderOf_dvd_of_pow_eq_one hn
    have h2 : orderOf ((y : G)) ∣ Nat.card D := by
      have h3 := orderOf_dvd_natCard (⟨(y : G), hxD⟩ : D)
      rwa [← Subgroup.orderOf_coe (⟨(y : G), hxD⟩ : D)] at h3
    have hcop : Nat.Coprime (2 ^ N) (Nat.card D) := by
      refine Nat.Coprime.pow_left _ ?_
      refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 ?_
      intro hdvd
      rw [Nat.odd_iff] at hDodd
      omega
    have hgcd : Nat.gcd (2 ^ N) (Nat.card D) = 1 := hcop
    have hdd := Nat.dvd_gcd h1 h2
    rw [hgcd] at hdd
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdd)
  have hQDcard : Nat.card Q * Nat.card D = Nat.card H := by
    rw [hQcard, hQ₀len, hHcard]
    ring
  have hQsupD : Q ⊔ D = H := by
    have hDleH : D ≤ H := inf_le_left
    have hdisj : Disjoint (Q.subgroupOf H) (D.subgroupOf H) := by
      rw [Subgroup.disjoint_def]
      intro x hx1 hx2
      rw [Subgroup.mem_subgroupOf] at hx1 hx2
      exact Subtype.ext ((Subgroup.disjoint_def.1 hQdisjD) hx1 hx2)
    have hcard : Nat.card (Q.subgroupOf H) * Nat.card (D.subgroupOf H) = Nat.card H := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQleH).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDleH).toEquiv]
      exact hQDcard
    have hcompl := Subgroup.isComplement'_of_card_mul_and_disjoint hcard hdisj
    have htop := hcompl.sup_eq_top
    have h := congrArg (fun S : Subgroup H => S.map H.subtype) htop
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 hQleH, inf_eq_left.2 hDleH] at h
    rw [h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine ⟨H, D, Q, t, ?_⟩
  refine { A1 := ?_, A2 := hfaith, A3 := ?_ }
  · exact
      { two_transitive := h2G
        point_stabilizer := ⟨ω₀, rfl⟩
        involution_t := ⟨htne, htsq⟩
        t_not_mem_H := htnotH
        D_eq := hDdef
        Q_le_H := hQleH
        D_le_H := inf_le_left
        Q_normal_in_H := hQnormH
        Q_disjoint_D := hQdisjD
        Q_sup_D := hQsupD
        Q_even := by rw [hQcard]; exact hA.A1.Q_even
        D_odd := hDodd }
  · obtain ⟨E, hE4, hEsq⟩ := hA.A3
    refine ⟨E.map L.subtype, by rw [Subgroup.card_subtype]; exact hE4, ?_⟩
    rintro ⟨_, x, hx, rfl⟩
    apply Subtype.ext
    have hx2 : (x : L) ^ 2 = 1 := by
      have h1 := hEsq ⟨x, hx⟩
      have h2 := congrArg (Subtype.val : E → L) h1
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
    rw [Subgroup.coe_pow]
    show ((x : L) : G) ^ 2 = 1
    have h3 := congrArg (Subtype.val : L → G) hx2
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h3

end Lift

end Converse
end BenderSuzuki
