module

public import Theory.Mathieu.SchurMultipliers.M12Upper.LocalBound.Calculation.Reduction
public import Theory.GroupTheory.PGroup.NormalExtraspecialDerivedCenter

/-!
# The abelian-core quotient of a central first-parabolic extension

For a surjection onto the literal first M₁₂ parabolic, factor out the derived
subgroup of the quaternion-core preimage. Its image downstairs is exactly the
marked central line `{1,z}`. The matching action, rather than the original
parabolic map, descends to this quotient. Its kernel is abelian and is a
two-group whenever the original kernel is.

The explicit cubic matching actor has no fixed points on the core modulo its
center. A check on the two quaternion coordinates proves this statement;
therefore its fixed elements in the abelian lifted kernel are central in the
whole extension. These are the concrete inputs to the remaining S₃ transfer
argument, not a completed multiplier bound.

Source: Aschbacher–Smith I.1.3(1), printed p.407, and the quaternion-core
geometry in the proof of 14.2.21, printed p.988 (PDF p.1005).
-/

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Sporadic.Mathieu.SchurMultipliers.M12Upper
open M12SmallPair

noncomputable section
variable {D : Type*} [Group D]

public theorem corePreimage_eq_matching_kernel (q : D →* firstParabolic) :
    corePreimage q = (FirstCore.matchingQuotient.comp q).ker := by
  rw [← MonoidHom.comap_ker, ← FirstCore.core_eq_matching_ker]
  rfl

public instance corePreimage_normal (q : D →* firstParabolic) :
    (corePreimage q).Normal := by
  rw [corePreimage_eq_matching_kernel]
  infer_instance

@[expose] public def coreDerived (q : D →* firstParabolic) : Subgroup D :=
  ⁅corePreimage q,corePreimage q⁆

public instance coreDerived_normal (q : D →* firstParabolic) :
    (coreDerived q).Normal := inferInstanceAs (⁅corePreimage q,corePreimage q⁆.Normal)

public theorem corePreimage_image (q : D →* firstParabolic)
    (hq : Function.Surjective q) :
    (corePreimage q).map (firstParabolic.subtype.comp q) = core := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact hx
  · intro x hx
    obtain ⟨a,ha⟩ := coreProjection_surjective q hq ⟨x,hx⟩
    exact ⟨a,a.property,congrArg Subtype.val ha⟩

/-- The image of the subgroup being factored out is precisely the marked
central line. In particular `q` itself does not descend through it. -/
public theorem coreDerived_image (q : D →* firstParabolic)
    (hq : Function.Surjective q) :
    (coreDerived q).map (firstParabolic.subtype.comp q) =
      (center core).map core.subtype := by
  let : IsExtraspecial 2 core := extraspecial_core
  rw [coreDerived, Subgroup.map_commutator, corePreimage_image q hq,
    ← map_subtype_commutator, IsExtraspecial.commutator_eq_center_two]

public theorem mem_coreDerived_image_iff (q : D →* firstParabolic)
    (hq : Function.Surjective q) (x : M12) :
    x ∈ (coreDerived q).map (firstParabolic.subtype.comp q) ↔ x = 1 ∨ x = z := by
  rw [coreDerived_image q hq]
  constructor
  · rintro ⟨y,hy,rfl⟩
    rw [coreQuaternionData.center_eq] at hy
    exact (factors_intersection_mem y).mp hy
  · intro hx
    have hi := (factors_intersection_mem x).mpr hx
    refine ⟨⟨x, (show leftFactor ≤ core from le_sup_left) hi.1⟩, ?_, rfl⟩
    rw [coreQuaternionData.center_eq]
    exact hi

@[expose] public def matchingAfterCoreDerived (q : D →* firstParabolic) :
    (D ⧸ coreDerived q) →* Equiv.Perm (Fin 3) :=
  QuotientGroup.lift (coreDerived q) (FirstCore.matchingQuotient.comp q)
    (show coreDerived q ≤ (FirstCore.matchingQuotient.comp q).ker from
      (commutator_le_self _).trans (corePreimage_eq_matching_kernel q).le)

public theorem matchingAfterCoreDerived_mk (q : D →* firstParabolic) (d : D) :
    matchingAfterCoreDerived q (QuotientGroup.mk' (coreDerived q) d) =
      FirstCore.matchingQuotient (q d) := rfl

public theorem matchingAfterCoreDerived_surjective (q : D →* firstParabolic)
    (hq : Function.Surjective q) : Function.Surjective (matchingAfterCoreDerived q) :=
  QuotientGroup.lift_surjective_of_surjective (coreDerived q)
    (FirstCore.matchingQuotient.comp q) (FirstCore.matchingQuotient_surjective.comp hq) _

public theorem matchingAfterCoreDerived_kernel (q : D →* firstParabolic) :
    (matchingAfterCoreDerived q).ker =
      (corePreimage q).map (QuotientGroup.mk' (coreDerived q)) := by
  rw [matchingAfterCoreDerived, QuotientGroup.ker_lift, ← corePreimage_eq_matching_kernel]

public theorem matchingAfterCoreDerived_kernel_abelian (q : D →* firstParabolic) :
    IsMulCommutative (matchingAfterCoreDerived q).ker := by
  apply commutator_self_eq_bot_iff.mp
  rw [matchingAfterCoreDerived_kernel, ← Subgroup.map_commutator]
  exact (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']; exact le_rfl)

public theorem corePreimage_isPGroup (q : D →* firstParabolic)
    (hp : IsPGroup 2 q.ker) : IsPGroup 2 (corePreimage q) := by
  have hcore : IsPGroup 2 (core.subgroupOf firstParabolic) :=
    IsPGroup.of_card (n := 5) FirstCore.card_core_subgroupOf
  exact hcore.comap_of_ker_isPGroup q hp

public theorem matchingAfterCoreDerived_kernel_isPGroup (q : D →* firstParabolic)
    (hp : IsPGroup 2 q.ker) : IsPGroup 2 (matchingAfterCoreDerived q).ker := by
  rw [matchingAfterCoreDerived_kernel]
  exact (corePreimage_isPGroup q hp).map _

private theorem core_cubic_fixed_mod_center (x : M12) (hx : x ∈ core)
    (hfix : ⁅FirstCore.secondCycle,x⁆ = 1 ∨ ⁅FirstCore.secondCycle,x⁆ = z) :
    x = 1 ∨ x = z := by
  obtain ⟨a,b,rfl⟩ := (mem_core x).mp hx
  have ht : ∀ a b : QuaternionGroup 2,
      (⁅FirstCore.secondCycle,leftEmbedding a * rightEmbedding b⁆ = 1 ∨
        ⁅FirstCore.secondCycle,leftEmbedding a * rightEmbedding b⁆ = z) →
      leftEmbedding a * rightEmbedding b = 1 ∨ leftEmbedding a * rightEmbedding b = z := by
    decide +kernel
  exact ht a b hfix

/-- All fixed elements of the cubic action on the abelian kernel are central
in the entire quotient extension, with the literal matching map retained. -/
public theorem matchingAfterCoreDerived_fixed_central (q : D →* firstParabolic)
    (hq : Function.Surjective q) (hk : q.ker ≤ center D)
    (t : D) (ht : q t = ⟨FirstCore.secondCycle,FirstCore.secondCycle_mem⟩)
    (x : D ⧸ coreDerived q) (hx : x ∈ (matchingAfterCoreDerived q).ker)
    (hcomm : Commute (QuotientGroup.mk' (coreDerived q) t) x) :
    x ∈ center (D ⧸ coreDerived q) := by
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (coreDerived q) x
  have ha : a ∈ corePreimage q := by
    rw [corePreimage_eq_matching_kernel]
    exact hx
  have hcomm' : ⁅t,a⁆ ∈ coreDerived q := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (coreDerived q) ⁅t,a⁆ = 1
    rw [map_commutatorElement]
    exact hcomm.commutator_eq
  have hi : (q ⁅t,a⁆ : M12) = 1 ∨ (q ⁅t,a⁆ : M12) = z :=
    (mem_coreDerived_image_iff q hq _).mp ⟨⁅t,a⁆,hcomm',rfl⟩
  have hqa : (q a : M12) = 1 ∨ (q a : M12) = z := by
    apply core_cubic_fixed_mod_center _ ha
    rw [map_commutatorElement, ht] at hi
    exact hi
  have hcentral : a ∈ center D := by
    rcases hqa with hqa | hqa
    · exact hk (Subtype.ext hqa)
    · exact lift_z_mem_center q hq hk a hqa
  apply mem_center_iff.mpr
  intro y
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (coreDerived q) y
  exact congrArg (QuotientGroup.mk' (coreDerived q)) (mem_center_iff.mp hcentral b)

end
end Sporadic.Mathieu.SchurMultipliers.M12Upper
