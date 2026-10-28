module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.SL23Local.CoreClosure
public import Theory.SpecificGroups.MinusExtraspecial.CubicAction.NormalForm
public import Theory.SpecificGroups.SL2.BinaryTetrahedralHom

/-!
# Identifying the actual cubic core closure with SL₂(3)

An order-three generator of X acts nontrivially on the actual extraspecial
core: trivial action would put it in the kernel of the Frattini action,
which is Q, contradicting the coprime orders. A cubic normal form for
`MinusExtraspecial.Model` then gives compatible coordinates on this very Q.

The quaternion and cyclic maps define an injective map from Q₈ ⋊ C₃.
Its image is exactly the supremum of the Q-conjugates of X: the fixed
dihedral factor adds no conjugates, while products of two cubic
commutators generate the quaternion factor. The unique nonidentity
central element of the core model maps to the distinguished z. Thus the
existing binary tetrahedral equivalence constructs both fields of
`CoreModel`, with the literal ambient subgroup throughout.

The final theorem `nonempty_coreModel` supplies the proved cubic normal
form for automorphisms of the explicit 32-element model, completing this
local construction from `Seed` alone. It needs neither simplicity nor the
earlier-source local-normalizer order. The intrinsic cubic geometry and
numerical inputs to the subsequent Sylow-pair construction remain with
that construction's assembly owner.

Source: Aschbacher, *Sporadic Groups* (1994), final paragraph of 47.5,
printed p.263, and the quaternion--dihedral coordinates on p.265.
-/

@[expose] public section

open Subgroup GLS3.Chapter5.SchurPresentation
open MinusExtraspecial.CubicAction
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.SL23Local
variable {G : Type*} [Group G] [Finite G]

/-- Coordinates on the actual core, compatible with a generator of the fixed X.
This is intermediate construction data, not an assumption of the source theorem. -/
structure CubicCoordinates (D : Seed G) where
  t : D.X
  order_t : orderOf (t : G) = 3
  core : MinusExtraspecial.Model →* G
  injective : Function.Injective core
  range_core : core.range = ambientCore D.z
  action : ∀ q, core (cycle q) = (t : G) * core q * (t : G)⁻¹

namespace CubicCoordinates
variable {D : Seed G} (C : CubicCoordinates D)

def quaternion : QuaternionGroup 2 →* G := C.core.comp MinusExtraspecial.quaternion

theorem quaternion_injective : Function.Injective C.quaternion :=
  C.injective.comp MinusExtraspecial.quaternion_injective

theorem core_mem (q : MinusExtraspecial.Model) : C.core q ∈ ambientCore D.z :=
  C.range_core ▸ (show C.core q ∈ C.core.range from ⟨q, rfl⟩)

theorem quaternion_mem_core (q : QuaternionGroup 2) : C.quaternion q ∈ ambientCore D.z :=
  C.core_mem _

theorem zpowers_t : zpowers (C.t : G) = D.X := by
  apply eq_of_le_of_card_ge (zpowers_le.mpr C.t.property)
  rw [Nat.card_zpowers, C.order_t, D.card_X]

theorem cube_t : (C.t : G) ^ 3 = 1 := C.order_t ▸ pow_orderOf_eq_one (C.t : G)

def cubic : Multiplicative (ZMod 3) →* G :=
  QuaternionGroup.cyclicPowerHom 3 (C.t : G) C.cube_t

theorem cubic_one : C.cubic (Multiplicative.ofAdd 1) = (C.t : G) :=
  QuaternionGroup.cyclicPowerHom_one _ _ _

theorem cubic_mem_X (k : Multiplicative (ZMod 3)) : C.cubic k ∈ D.X := by
  have hk := QuaternionGroup.cyclicPowerHom_intCast 3 (C.t : G) C.cube_t
    ((Multiplicative.toAdd k).val : ℤ)
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at hk
  change C.cubic k = _ at hk
  rw [hk]
  exact D.X.zpow_mem C.t.property _

theorem cubic_injective : Function.Injective C.cubic := by
  apply (injective_iff_map_eq_one _).mpr
  intro k hk
  have hc : k = 1 ∨ k = Multiplicative.ofAdd 1 ∨ k = Multiplicative.ofAdd 2 :=
    (show ∀ k : Multiplicative (ZMod 3),
      k = 1 ∨ k = Multiplicative.ofAdd 1 ∨ k = Multiplicative.ofAdd 2 from by decide) k
  rcases hc with rfl | rfl | rfl
  · rfl
  · rw [C.cubic_one] at hk
    have := congrArg orderOf hk
    rw [C.order_t, orderOf_one] at this
    contradiction
  · have hk2 : C.cubic (Multiplicative.ofAdd 2) = (C.t : G) ^ 2 := by
      simpa [cubic] using
        QuaternionGroup.cyclicPowerHom_intCast 3 (C.t : G) C.cube_t 2
    rw [hk2] at hk
    have hd := orderOf_dvd_of_pow_eq_one hk
    rw [C.order_t] at hd
    norm_num at hd

theorem quaternion_action (q : QuaternionGroup 2) :
    C.quaternion (q8Cycle q) = (C.t : G) * C.quaternion q * (C.t : G)⁻¹ :=
  C.action (MinusExtraspecial.quaternion q)

theorem compatible (k : Multiplicative (ZMod 3)) (q : QuaternionGroup 2) :
    C.quaternion (q8C3Action k q) = C.cubic k * C.quaternion q * (C.cubic k)⁻¹ := by
  have hc : k = 1 ∨ k = Multiplicative.ofAdd 1 ∨ k = Multiplicative.ofAdd 2 :=
    (show ∀ k : Multiplicative (ZMod 3),
      k = 1 ∨ k = Multiplicative.ofAdd 1 ∨ k = Multiplicative.ofAdd 2 from by decide) k
  rcases hc with rfl | rfl | rfl
  · change C.quaternion ((q8Cycle ^ 0) q) = C.cubic 1 * C.quaternion q * (C.cubic 1)⁻¹
    simp
  · change C.quaternion ((q8Cycle ^ 1) q) = _
    simpa only [pow_one, C.cubic_one] using C.quaternion_action q
  · change C.quaternion (q8Cycle (q8Cycle q)) = _
    have hk2 : C.cubic (Multiplicative.ofAdd 2) = (C.t : G) ^ 2 := by
      simpa [cubic] using
        QuaternionGroup.cyclicPowerHom_intCast 3 (C.t : G) C.cube_t 2
    rw [hk2, C.quaternion_action, C.quaternion_action, pow_two]
    group

def lift : (QuaternionGroup 2 ⋊[q8C3Action] Multiplicative (ZMod 3)) →* G :=
  SemidirectProduct.lift C.quaternion C.cubic (fun k => MonoidHom.ext (C.compatible k))

theorem lift_injective : Function.Injective C.lift := by
  have hd : Disjoint (ambientCore D.z) D.X := disjoint_of_coprime_natCard (by
    rw [D.localType.ambientCore_card, D.card_X]
    decide)
  apply (injective_iff_map_eq_one _).mpr
  intro v hv
  change C.quaternion v.left * C.cubic v.right = 1 at hv
  obtain ⟨ha, hb⟩ := disjoint_iff_mul_eq_one.mp hd
    (C.quaternion_mem_core _) (C.cubic_mem_X _) hv
  have ha' : v.left = 1 := C.quaternion_injective (ha.trans (map_one _).symm)
  have hb' : v.right = 1 := C.cubic_injective (hb.trans (map_one _).symm)
  exact SemidirectProduct.ext ha' hb'

/-- Actual commutators put the entire moved quaternion factor in ⟨X^Q⟩. -/
theorem quaternion_mem_closure (q : QuaternionGroup 2) : C.quaternion q ∈ coreClosure D := by
  have hcomm (a : QuaternionGroup 2) : C.quaternion (a * q8Cycle a⁻¹) ∈ coreClosure D := by
    have hconj : C.quaternion a * (C.t : G) * (C.quaternion a)⁻¹ ∈ coreClosure D :=
      (le_iSup (fun r : ambientCore D.z =>
        D.X.map (MulAut.conj (r : G)).toMonoidHom)
        ⟨C.quaternion a, C.quaternion_mem_core a⟩)
        (mem_map.mpr ⟨C.t, C.t.property, rfl⟩)
    have hprod := (coreClosure D).mul_mem hconj
      ((coreClosure D).inv_mem (X_le_coreClosure D C.t.property))
    convert hprod using 1
    rw [map_mul, C.quaternion_action, map_inv]
    group
  obtain ⟨a, b, hab⟩ := quaternion_commutators q
  rw [← hab, map_mul]
  exact (coreClosure D).mul_mem (hcomm a) (hcomm b)

theorem lift_range_le_closure : C.lift.range ≤ coreClosure D := by
  rintro _ ⟨v, rfl⟩
  exact (coreClosure D).mul_mem (C.quaternion_mem_closure v.left)
    (X_le_coreClosure D (C.cubic_mem_X v.right))

theorem closure_le_lift_range : coreClosure D ≤ C.lift.range := by
  have hquat (a : QuaternionGroup 2) : C.quaternion a ∈ C.lift.range :=
    ⟨SemidirectProduct.inl a, SemidirectProduct.lift_inl _ _ _ a⟩
  have ht : (C.t : G) ∈ C.lift.range :=
    ⟨SemidirectProduct.inr (Multiplicative.ofAdd 1),
      (SemidirectProduct.lift_inr _ _ _ _).trans C.cubic_one⟩
  apply iSup_le
  intro q
  apply map_le_iff_le_comap.mpr
  rw [← C.zpowers_t]
  apply zpowers_le.mpr
  change (q : G) * (C.t : G) * (q : G)⁻¹ ∈ C.lift.range
  have hq : (q : G) ∈ C.core.range := by rw [C.range_core]; exact q.property
  obtain ⟨m, hm⟩ := hq
  obtain ⟨a, d, had⟩ := MinusExtraspecial.factors_generate m
  have hd : C.core (MinusExtraspecial.dihedral d) * (C.t : G) *
      (C.core (MinusExtraspecial.dihedral d))⁻¹ = C.t := by
    have h := C.action (MinusExtraspecial.dihedral d)
    rw [cycle_dihedral] at h
    have hc : C.core (MinusExtraspecial.dihedral d) * (C.t : G) =
        (C.t : G) * C.core (MinusExtraspecial.dihedral d) :=
      (mul_inv_eq_iff_eq_mul.mp h.symm).symm
    rw [hc]
    group
  rw [← hm, ← had, map_mul]
  have he : (C.quaternion a * C.core (MinusExtraspecial.dihedral d)) * (C.t : G) *
      (C.quaternion a * C.core (MinusExtraspecial.dihedral d))⁻¹ =
      C.quaternion a * (C.t : G) * (C.quaternion a)⁻¹ := by
    calc
      _ = C.quaternion a * (C.core (MinusExtraspecial.dihedral d) * (C.t : G) *
          (C.core (MinusExtraspecial.dihedral d))⁻¹) * (C.quaternion a)⁻¹ := by group
      _ = _ := by rw [hd]
  change (C.quaternion a * C.core (MinusExtraspecial.dihedral d)) * (C.t : G) *
    (C.quaternion a * C.core (MinusExtraspecial.dihedral d))⁻¹ ∈ C.lift.range
  rw [he]
  exact C.lift.range.mul_mem (C.lift.range.mul_mem (hquat a) ht)
    (C.lift.range.inv_mem (hquat a))

/-- Equality with the literal ambient supremum, not an abstract family label. -/
theorem lift_range : C.lift.range = coreClosure D :=
  le_antisymm C.lift_range_le_closure C.closure_le_lift_range

/-- The marked central involution is the original z. -/
theorem central_involution : C.quaternion (.a 2) = D.z := by
  obtain ⟨m, hm⟩ := C.range_core.symm ▸ HTypeAt.involution_mem_core (z := D.z)
  have hmZ : m ∈ center MinusExtraspecial.Model := by
    apply mem_center_iff.mpr
    intro a
    apply C.injective
    rw [map_mul, map_mul, hm]
    exact mem_centralizer_singleton_iff.mp (ambientCore_le D.z (C.core_mem a))
  rcases (MinusExtraspecial.mem_center_iff m).mp hmZ with hm1 | hmz
  · subst m
    have hz : D.z = 1 := hm.symm.trans (map_one _)
    have ho := D.localType.involution
    rw [hz, orderOf_one] at ho
    contradiction
  · change C.core (MinusExtraspecial.quaternion MinusExtraspecial.z) = D.z
    simpa only [hmz] using hm

/-- Construct both required fields using the actual subgroup image. -/
noncomputable def coreModel : CoreModel D where
  equiv := ((MulEquiv.subgroupCongr C.lift_range).symm.trans
    (MonoidHom.ofInjective C.lift_injective).symm).trans binaryTetrahedralEquivSL
  involution_mem := C.central_involution ▸ C.quaternion_mem_closure (.a 2)

end CubicCoordinates

/-- The source core action meets every hypothesis of the finite normal-form problem. -/
theorem nonempty_cubicCoordinates_of_normalForm (D : Seed G)
    (hn : HasCubicNormalForm) : Nonempty (CubicCoordinates D) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := D.X) 3 (by rw [D.card_X])
  have htG : orderOf (t : G) = 3 := (Subgroup.orderOf_coe t).trans ht
  let H := involutionCentralizer D.z
  let Q := localCore D.z
  let tH : H := ⟨t, D.X_le t.property⟩
  let b : MulAut Q := MulAut.conjNormal tH
  have htH : orderOf tH = 3 := (Subgroup.orderOf_coe tH).symm.trans htG
  have ht3 : tH ^ 3 = 1 := htH ▸ pow_orderOf_eq_one tH
  have hb3 : b ^ 3 = 1 := by
    change (MulAut.conjNormal tH : MulAut Q) ^ 3 = 1
    rw [← map_pow, ht3, map_one]
  have hb : b ≠ 1 := by
    intro hb
    have hker : tH ∈ (coreFrattiniAction D.z).ker := by
      change quotientAut (frattini Q) b = 1
      rw [hb, map_one]
    rw [D.localType.coreFrattiniAction_kernel] at hker
    have hd := Q.orderOf_dvd_natCard hker
    rw [D.localType.core_card, htH] at hd
    norm_num at hd
  let e : Q ≃* MinusExtraspecial.Model := D.localType.core_equiv.some
  let a : MulAut MinusExtraspecial.Model := MulAut.congr e b
  have ha3 : a ^ 3 = 1 := by
    dsimp only [a]
    rw [← map_pow, hb3, map_one]
  have ha : a ≠ 1 := by
    intro h
    apply hb
    exact (MulAut.congr e).injective (h.trans (map_one _).symm)
  obtain ⟨f, hf⟩ := hn a ha3 ha
  let e' : Q ≃* MinusExtraspecial.Model := e.trans f
  have he' (q : Q) : e' (b q) = cycle (e' q) := by
    simpa [a, MulAut.congr, e'] using hf (e q)
  have hinv (q : MinusExtraspecial.Model) : e'.symm (cycle q) = b (e'.symm q) := by
    apply e'.injective
    rw [e'.apply_symm_apply, he', e'.apply_symm_apply]
  let i : MinusExtraspecial.Model →* G :=
    H.subtype.comp (Q.subtype.comp e'.symm.toMonoidHom)
  refine ⟨⟨t, htG, i, H.subtype_injective.comp (Q.subtype_injective.comp e'.symm.injective),
    ?_, ?_⟩⟩
  · ext g
    constructor
    · rintro ⟨q, rfl⟩
      exact mem_map_of_mem H.subtype (e'.symm q).property
    · rintro ⟨q, hq, rfl⟩
      refine ⟨e' ⟨q, hq⟩, ?_⟩
      simp [i]
  · intro q
    change (((e'.symm (cycle q) : Q) : H) : G) =
      (t : G) * (((e'.symm q : Q) : H) : G) * (t : G)⁻¹
    rw [hinv]
    rfl

/-- Transport a cubic normal form to the actual core closure. -/
theorem nonempty_coreModel_of_normalForm (D : Seed G)
    (hn : HasCubicNormalForm) : Nonempty (CoreModel D) := by
  obtain ⟨C⟩ := nonempty_cubicCoordinates_of_normalForm D hn
  exact ⟨C.coreModel⟩

/-- The actual Q-conjugate closure is SL₂(3) and contains the distinguished z.
This is the local construction in the final paragraph of 47.5, from `Seed` alone. -/
theorem nonempty_coreModel (D : Seed G) : Nonempty (CoreModel D) :=
  nonempty_coreModel_of_normalForm D hasCubicNormalForm

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.SL23Local
