module

public import Theory.Mathieu.SchurMultipliers.M12Upper.LocalBound
public import Theory.GroupTheory.QuaternionBinaryCentralExtension.FixedLifts
public import Theory.GroupTheory.CentralExtensionInvariantPairing
public import Theory.GroupTheory.Commutator.CentralExtensionPairing

/-!
# Central binary commutator pairings over the first M₁₂ parabolic

Let `q : D →* C_M₁₂(z)` be a surjective central extension. Relative normality
of the marked quaternion factor forces every lift of `z` into the center of
`D`. Consequently the full preimage of the quaternion core has central
commutators and central squares. Its commutator pairing descends to the
actual embedded core, is invariant under the full parabolic, and has
exponent two. Its values generate the literal derived subgroup of that
preimage. No exponent assumption on the kernel, finiteness of `D`, or
perfectness is needed for these statements.

These are inputs to the relative local multiplier calculation in
`Calculation.Reduction`; they do not assert its remaining kernel count
or its detection of the full derived kernel inside the core.
Source: Aschbacher–Smith I.1.3(1), printed p.407, and the quaternion
parabolic geometry of 14.2.21, printed p.988.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Sporadic.Mathieu.SchurMultipliers.M12Upper
open M12SmallPair

noncomputable section
variable {D : Type*} [Group D]

@[expose] public def corePreimage (q : D →* firstParabolic) : Subgroup D :=
  core.comap (firstParabolic.subtype.comp q)

@[expose] public def coreProjection (q : D →* firstParabolic) : corePreimage q →* core :=
  (firstParabolic.subtype.comp q).subgroupComap core

public theorem coreProjection_surjective (q : D →* firstParabolic)
    (hq : Function.Surjective q) : Function.Surjective (coreProjection q) := by
  intro x
  obtain ⟨a, ha⟩ := hq ⟨x, core_le_firstParabolic x.property⟩
  refine ⟨⟨a, ?_⟩, ?_⟩
  · change (q a : M12) ∈ core
    rw [ha]
    exact x.property
  · apply Subtype.ext
    change (q a : M12) = x
    exact congrArg Subtype.val ha

/-- Every lift of the marked central involution is central in the full local extension. -/
public theorem lift_z_mem_center (q : D →* firstParabolic)
    (hq : Function.Surjective q) (hk : q.ker ≤ center D)
    (x : D) (hx : (q x : M12) = z) : x ∈ center D := by
  let L := leftFactor.subgroupOf firstParabolic
  have hL : leftFactor ≤ firstParabolic := le_sup_left.trans core_le_firstParabolic
  let e : L ≃* QuaternionGroup 2 :=
    (subgroupOfEquivOfLe hL).trans (MonoidHom.ofInjective leftEmbedding_injective).symm
  have hzL : z ∈ leftFactor := ⟨.a 2, by decide +kernel⟩
  have hxL : q x ∈ L := by change (q x : M12) ∈ leftFactor; rw [hx]; exact hzL
  apply mem_center_iff.mpr
  intro a
  refine q.commute_lift_of_quaternion_normalizer hq hk L e a x ?_ hxL ?_
  · apply mem_normalizer_iff.mpr
    intro y
    exact mem_normalizer_iff.mp (firstParabolic_normalizes_left (q a).property) y.val
  · apply e.symm.injective
    rw [MulEquiv.symm_apply_apply]
    apply Subtype.ext
    apply Subtype.ext
    change (q x : M12) = leftEmbedding (.a 2)
    rw [hx]
    decide +kernel

private theorem core_center_dichotomy (x : core) :
    x ∈ center core ↔ (x : M12) = 1 ∨ (x : M12) = z := by
  rw [coreQuaternionData.center_eq]
  exact factors_intersection_mem x

private theorem core_commutator_mem_center (x y : core) :
    ⁅x,y⁆ ∈ center core := by
  let _ := coreQuaternionData.quotient_elementary
  exact (Normal.quotient_commutative_iff_commutator_le.mp
    (inferInstance : IsMulCommutative (core ⧸ center core)))
      (commutator_mem_commutator (mem_top x) (mem_top y))

public theorem core_lift_commutator_mem_center (q : D →* firstParabolic)
    (hq : Function.Surjective q) (hk : q.ker ≤ center D)
    (a b : D) (ha : a ∈ corePreimage q) (hb : b ∈ corePreimage q) :
    ⁅a,b⁆ ∈ center D := by
  have he : ((⁅coreProjection q ⟨a,ha⟩,coreProjection q ⟨b,hb⟩⁆ : core) : M12) =
      (q ⁅a,b⁆ : M12) := by simp only [map_commutatorElement]; rfl
  rcases (core_center_dichotomy _).mp (core_commutator_mem_center
    (coreProjection q ⟨a,ha⟩) (coreProjection q ⟨b,hb⟩)) with h | h
  · apply hk
    apply Subtype.ext
    exact he.symm.trans h
  · exact lift_z_mem_center q hq hk _ (he.symm.trans h)

public theorem core_lift_derived_le_center (q : D →* firstParabolic)
    (hq : Function.Surjective q) (hk : q.ker ≤ center D) :
    ⁅corePreimage q, corePreimage q⁆ ≤ center D :=
  commutator_le.mpr (fun a ha b hb => core_lift_commutator_mem_center q hq hk a b ha hb)

private theorem core_lift_square_mem_center (q : D →* firstParabolic)
    (hq : Function.Surjective q) (hk : q.ker ≤ center D)
    (a : D) (ha : a ∈ corePreimage q) : a ^ 2 ∈ center D := by
  have he : (((coreProjection q ⟨a,ha⟩) ^ 2 : core) : M12) = (q (a^2) : M12) := by
    simp only [map_pow]; rfl
  rcases (core_center_dichotomy _).mp (coreQuaternionData.square_mem_center
    (coreProjection q ⟨a,ha⟩)) with h | h
  · apply hk
    apply Subtype.ext
    exact he.symm.trans h
  · exact lift_z_mem_center q hq hk _ (he.symm.trans h)

/-- Changing either lift leaves the commutator unchanged. -/
public theorem local_commutator_eq_of_image_eq (q : D →* firstParabolic)
    (hk : q.ker ≤ center D) {a a' b b' : D}
    (ha : (q a : M12) = q a') (hb : (q b : M12) = q b') :
    ⁅a,b⁆ = ⁅a',b'⁆ :=
  CentralExtension.commutator_eq_of_image_eq q hk (Subtype.ext ha) (Subtype.ext hb)

/-- An existential commuting-lift premise therefore applies to every pair of lifts. -/
public theorem commute_all_lifts_v_third (q : D →* firstParabolic)
    (hk : q.ker ≤ center D)
    (hvt : ∃ a b : D, (q a : M12) = v ∧ (q b : M12) = third ∧ Commute a b)
    (a b : D) (ha : (q a : M12) = v) (hb : (q b : M12) = third) : Commute a b := by
  obtain ⟨a',b',ha',hb',hab⟩ := hvt
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [local_commutator_eq_of_image_eq q hk (ha.trans ha'.symm) (hb.trans hb'.symm)]
  exact hab.commutator_eq


/-- The central commutator on the core descends through the literal local quotient.
Its values have exponent two and are invariant under the full parabolic. -/
public theorem exists_core_lift_pairing (q : D →* firstParabolic)
    (hq : Function.Surjective q) (hk : q.ker ≤ center D) :
    ∃ B : core →* (core →* center D),
      (∀ (x y : core) (a b : D), (q a : M12) = x → (q b : M12) = y →
        (B x y : D) = ⁅a,b⁆) ∧
      (∀ (g : firstParabolic) (x y : core),
        B (firstParabolicCoreAction g x) (firstParabolicCoreAction g y) = B x y) ∧
      (∀ x y, (B x y) ^ 2 = 1) ∧ (∀ x, B x x = 1) := by
  let P := corePreimage q
  let f := coreProjection q
  have hc (a b : P) : ⁅(a : D),(b : D)⁆ ∈ center D :=
    core_lift_commutator_mem_center q hq hk a b a.property b.property
  let d : P →* (P →* center D) := {
    toFun a := {
      toFun b := ⟨⁅(a : D),(b : D)⁆, hc a b⟩
      map_one' := by apply Subtype.ext; exact commutatorElement_one_right (a : D)
      map_mul' b c := by
        apply Subtype.ext
        change ⁅(a : D),(b : D)*(c : D)⁆ = ⁅(a : D),(b : D)⁆ * ⁅(a : D),(c : D)⁆
        rw [commutatorElement_mul_right_eq_mul_conj,
          mul_assoc, mul_assoc, ← mul_assoc (b : D),
          mem_center_iff.mp (hc a c) b, mul_inv_cancel_right] }
    map_one' := by ext b; exact commutatorElement_one_left (b : D)
    map_mul' a b := by
      ext c
      change ⁅(a : D)*(b : D),(c : D)⁆ = ⁅(a : D),(c : D)⁆ * ⁅(b : D),(c : D)⁆
      rw [commutatorElement_mul_left_eq_conj_mul,
        mem_center_iff.mp (hc b c) a, mul_inv_cancel_right,
        mem_center_iff.mp (hc a c) ⁅(b : D),(c : D)⁆] }
  have hd (a b : P) : (d a b : D) = ⁅(a : D),(b : D)⁆ := rfl
  have hker {a : P} (ha : a ∈ f.ker) : (a : D) ∈ q.ker := by
    apply Subtype.ext
    exact congrArg (fun x : core => (x : M12)) ha
  have hl : ∀ a ∈ f.ker, d a = 1 := by
    intro a ha
    ext b
    change ⁅(a : D),(b : D)⁆ = 1
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (mem_center_iff.mp (hk (hker ha)) b).symm
  have hr : ∀ a, f.ker ≤ (d a).ker := by
    intro a b hb
    apply Subtype.ext
    change ⁅(a : D),(b : D)⁆ = 1
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (mem_center_iff.mp (hk (hker hb)) a)
  obtain ⟨B,hB⟩ := CentralExtension.exists_descended_pairing f
    (coreProjection_surjective q hq) d hl hr
  have formula (x y : core) (a b : D) (ha : (q a : M12) = x)
      (hb : (q b : M12) = y) : (B x y : D) = ⁅a,b⁆ := by
    have hpa : a ∈ P := by change (q a : M12) ∈ core; rw [ha]; exact x.property
    have hpb : b ∈ P := by change (q b : M12) ∈ core; rw [hb]; exact y.property
    have hfa : f ⟨a,hpa⟩ = x := Subtype.ext ha
    have hfb : f ⟨b,hpb⟩ = y := Subtype.ext hb
    rw [← hfa, ← hfb, hB, hd]
  have lifts (x : core) : ∃ a : D, (q a : M12) = x := by
    obtain ⟨a,ha⟩ := hq ⟨x,core_le_firstParabolic x.property⟩
    exact ⟨a,congrArg Subtype.val ha⟩
  refine ⟨B,formula,?_,?_,?_⟩
  · intro g x y
    obtain ⟨r,hr⟩ := hq g
    obtain ⟨a,ha⟩ := lifts x
    obtain ⟨b,hb⟩ := lifts y
    apply Subtype.ext
    have hca : (q (r*a*r⁻¹) : M12) = firstParabolicCoreAction g x := by
      simp only [map_mul,map_inv,hr]
      change (g : M12)*(q a : M12)*(g : M12)⁻¹ = (g : M12)*x*(g : M12)⁻¹
      rw [ha]
    have hcb : (q (r*b*r⁻¹) : M12) = firstParabolicCoreAction g y := by
      simp only [map_mul,map_inv,hr]
      change (g : M12)*(q b : M12)*(g : M12)⁻¹ = (g : M12)*y*(g : M12)⁻¹
      rw [hb]
    rw [formula _ _ _ _ hca hcb, ← conjugate_commutatorElement, ← formula x y a b ha hb,
      mem_center_iff.mp (B x y).property r, mul_inv_cancel_right]
  · intro x y
    obtain ⟨a,ha⟩ := lifts x
    obtain ⟨b,hb⟩ := lifts y
    apply Subtype.ext
    have hs : (q (a^2) : M12) = (x^2 : core) := by
      simp only [map_pow]; change (q a : M12)^2 = (x : M12)^2; rw [ha]
    have he : (B x y)^2 = B (x^2) y := by simp only [map_pow,MonoidHom.pow_apply]
    rw [he,formula _ _ _ _ hs hb]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (mem_center_iff.mp (core_lift_square_mem_center q hq hk a
        (by change (q a : M12) ∈ core; rw [ha]; exact x.property)) b).symm
  · intro x
    obtain ⟨a,ha⟩ := lifts x
    apply Subtype.ext
    rw [formula _ _ _ _ ha ha]
    exact commutatorElement_self a

/-- The span of pairing values is exactly the derived subgroup of the core preimage. -/
public theorem core_lift_derived_eq_pairing_span (q : D →* firstParabolic)
    (hq : Function.Surjective q) (B : core →* (core →* center D))
    (hB : ∀ (x y : core) (a b : D), (q a : M12) = x → (q b : M12) = y →
      (B x y : D) = ⁅a,b⁆) :
    ⁅corePreimage q, corePreimage q⁆ =
      closure {w : D | ∃ x y : core, (B x y : D) = w} := by
  apply le_antisymm
  · apply commutator_le.mpr
    intro a ha b hb
    apply subset_closure
    exact ⟨coreProjection q ⟨a,ha⟩,coreProjection q ⟨b,hb⟩,hB _ _ a b rfl rfl⟩
  · apply (closure_le _).mpr
    rintro _ ⟨x,y,rfl⟩
    obtain ⟨a,ha⟩ := coreProjection_surjective q hq x
    obtain ⟨b,hb⟩ := coreProjection_surjective q hq y
    rw [hB x y a b (congrArg Subtype.val ha) (congrArg Subtype.val hb)]
    exact commutator_mem_commutator a.property b.property

/-- The lifted core's entire derived subgroup, including its kernel intersection,
has exponent two. No exponent assumption on the central kernel is used. -/
public theorem core_lift_derived_square (q : D →* firstParabolic)
    (hq : Function.Surjective q) (hk : q.ker ≤ center D)
    (d : D) (hd : d ∈ ⁅corePreimage q,corePreimage q⁆) : d^2 = 1 := by
  obtain ⟨B,hB,_,hs,_⟩ := exists_core_lift_pairing q hq hk
  let Z := (powMonoidHom 2 : center D →* center D).ker.map (center D).subtype
  have hle : ⁅corePreimage q,corePreimage q⁆ ≤ Z := by
    rw [core_lift_derived_eq_pairing_span q hq B hB]
    apply (closure_le _).mpr
    rintro _ ⟨x,y,rfl⟩
    exact ⟨B x y,hs x y,rfl⟩
  obtain ⟨c,hc,rfl⟩ := hle hd
  exact congrArg (fun x : center D => (x : D)) hc

end
end Sporadic.Mathieu.SchurMultipliers.M12Upper
