module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Deleted.Coordinates
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Reduction

/-!
# The deleted-module actor contains the marked Klein four

An order-eight subgroup of S₃ × D has a nonidentity element in 1 × A₅:
otherwise projection to S₃ times the permutation sign would embed it in a
group of order twelve. Elementary abelianness makes this element an involution.
In the supplied point coordinates, it fixes the weight-four vector and hence
is one of the three double transpositions on its support. The even three-cycle
on that support fixes the tensor point. Relative normality in the entire point
centralizer therefore places all three double transpositions in the actor.

`actor_generators` proves the two memberships for every supplied coordinate
system. `actorPlacement_of_pointNormalization` applies them to the existing
placement interface; the source assembly owner supplies point normalization.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 14.4.10,
first proof paragraph, printed p.1010; the tensor alternatives in 14.4.2(5),
p.1006, and point-centralizer normality in 12.8.12(2), p.855.
-/

public section

open Subgroup TensorProduct Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Deleted
variable {D : Subgroup Five} (hAD : AltFive ≤ D)
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem exists_even_actor (A : Subgroup (Three × D)) (hcard : Nat.card A = 8) :
    ∃ a : AltFive, a ≠ 1 ∧ componentActor hAD a ∈ A := by
  let q : A →* Three × ℤˣ :=
    ((MonoidHom.fst Three D).prod
      (Equiv.Perm.sign.comp (D.subtype.comp (MonoidHom.snd Three D)))).comp A.subtype
  have hn : ¬ Function.Injective q := by
    intro hi
    have hh := Subgroup.card_dvd_of_injective q hi
    have hc : Nat.card (Three × ℤˣ) = 12 := by
      rw [Nat.card_prod, Nat.card_perm, Nat.card_fin, Nat.card_eq_fintype_card,
        Fintype.card_units_int]
      decide
    rw [hcard, hc] at hh
    norm_num at hh
  have hk : q.ker ≠ ⊥ := fun he => hn (q.ker_eq_bot_iff.mp he)
  obtain ⟨a, ha, hne⟩ := (Subgroup.nontrivial_iff_exists_ne_one _).mp
    ((Subgroup.nontrivial_iff_ne_bot _).mpr hk)
  have he : a.val.1 = 1 ∧ Equiv.Perm.sign a.val.2.val = 1 :=
    Prod.ext_iff.mp ha
  let b : AltFive := ⟨a.val.2.val, Equiv.Perm.mem_alternatingGroup.mpr he.2⟩
  refine ⟨b, ?_, ?_⟩
  · intro hb
    apply hne
    apply Subtype.ext
    exact Prod.ext he.1 (Subtype.ext (congrArg (fun x : AltFive => x.val) hb))
  · have hb : componentActor hAD b = a.val := Prod.ext he.1.symm rfl
    rw [hb]
    exact a.property

private theorem involution_cases : ∀ a : Five, a ^ 2 = 1 → Equiv.Perm.sign a = 1 →
    permAction a point = point → a ≠ 1 →
    a = first.val ∨ a = second.val ∨ a = (first * second).val := by
  decide +kernel

private theorem tmul_cancel {n : Natural} (hn : n ≠ 0) {v w : V}
    (h : n ⊗ₜ[ZMod 2] v = n ⊗ₜ[ZMod 2] w) : v = w := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hn
  have hh := congrArg (fun t => TensorProduct.lid (ZMod 2) V
    (TensorProduct.map l (LinearMap.id : V →ₗ[ZMod 2] V) t)) h
  simpa only [TensorProduct.map_tmul, LinearMap.id_apply, hl,
    TensorProduct.lid_tmul, one_smul] using hh

private theorem pure_fixes_iff {σ : Representation (ZMod 2) D V}
    (f : V ≃ₗ[ZMod 2] Core)
    (hf : ∀ (a : D) (v : V), f (σ a v) = permAction a.val (f v))
    (d : ComplementIntersectionData σ) (p : PointCoordinates f d) (a : AltFive) :
    sourceTensorAction σ (componentActor hAD (conjugate p.coordinate a)) d.point =
      d.point ↔ permAction a.val point = point := by
  have he : σ (inclusion hAD (conjugate p.coordinate a))
      (f.symm (permAction p.coordinate point)) =
      f.symm (permAction p.coordinate (permAction a.val point)) := by
    apply f.injective
    rw [hf, f.apply_symm_apply, f.apply_symm_apply]
    change permAction (p.coordinate * a.val * p.coordinate⁻¹)
      (permAction p.coordinate point) = _
    rw [← Module.End.mul_apply, ← map_mul]
    rw [show (p.coordinate * a.val * p.coordinate⁻¹) * p.coordinate =
      p.coordinate * a.val by group, map_mul, Module.End.mul_apply]
  rw [p.point_eq]
  change naturalAction 1 p.natural ⊗ₜ[ZMod 2]
    σ (inclusion hAD (conjugate p.coordinate a))
      (f.symm (permAction p.coordinate point)) = _ ↔ _
  rw [map_one, Module.End.one_apply, he]
  constructor
  · intro h
    have hv := f.symm.injective (tmul_cancel (p.natural_ne_zero f d) h)
    have hh := congrArg (permAction p.coordinate⁻¹) hv
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply, inv_mul_cancel_left] using hh
  · intro h
    rw [h]

private def componentMap (g : Five) : AltFive →* Three × D where
  toFun a := componentActor hAD (conjugate g a)
  map_one' := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change g * 1 * g⁻¹ = 1
      group
  map_mul' a b := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change g * (a.val * b.val) * g⁻¹ =
        (g * a.val * g⁻¹) * (g * b.val * g⁻¹)
      group

private theorem componentMap_injective (g : Five) :
    Function.Injective (componentMap hAD g) := by
  intro a b he
  have hh := congrArg (fun x : Three × D => x.2.val) he
  change g * a.val * g⁻¹ = g * b.val * g⁻¹ at hh
  exact Subtype.ext (conj_injective hh)

private theorem actor_conjugate_mem {σ : Representation (ZMod 2) D V}
    (f : V ≃ₗ[ZMod 2] Core)
    (hf : ∀ (a : D) (v : V), f (σ a v) = permAction a.val (f v))
    (d : ComplementIntersectionData σ) (p : PointCoordinates f d)
    (b a : AltFive) (hb : permAction b.val point = point)
    (ha : componentMap hAD p.coordinate a ∈ d.actor) :
    componentMap hAD p.coordinate (b * a * b⁻¹) ∈ d.actor := by
  let C := subspaceKernel (sourceTensorAction σ)
    (Submodule.span (ZMod 2) {d.point}) ⊤
  let j := componentMap hAD p.coordinate
  have hbfix := (pure_fixes_iff hAD f hf d p b).mpr hb
  change sourceTensorAction σ (j b) d.point = d.point at hbfix
  have hbC : j b ∈ C := by
    refine ⟨Subgroup.mem_top _, ?_⟩
    intro w hw
    obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul, hbfix]
  have haC : j a ∈ C := d.actor_le_pointCentralizer ha
  have hh := d.actor_normal.conj_mem (⟨j a, haC⟩ : C) ha (⟨j b, hbC⟩ : C)
  change j b * j a * (j b)⁻¹ ∈ d.actor at hh
  simpa only [map_mul, map_inv] using hh

private abbrev cycle := BinaryPermutation.CubicFixedSpace.Five.cycle

private theorem cycle_fixed : permAction cycle.val point = point := by
  apply Subtype.ext
  decide +kernel

private theorem cycle_first : cycle * first * cycle⁻¹ = first * second := by
  decide +kernel

private theorem cycle_second : cycle * second * cycle⁻¹ = first := by
  decide +kernel

private theorem cycle_third : cycle * (first * second) * cycle⁻¹ = second := by
  decide +kernel

/-- Relative normality in the full point centralizer places both pure
Klein-four generators in the elementary actor of order eight. -/
theorem actor_generators (_hcase : D = ⊤ ∨ D = AltFive)
    (σ : Representation (ZMod 2) D V) : ActorGenerators hAD σ := by
  intro f hf d p
  let := d.actor_elementary
  obtain ⟨a, hne, ha⟩ := exists_even_actor hAD d.actor d.actor_card
  let b := conjugate p.coordinate⁻¹ a
  let j := componentMap hAD p.coordinate
  have hba : conjugate p.coordinate b = a := by
    apply Subtype.ext
    change p.coordinate * (p.coordinate⁻¹ * a.val * (p.coordinate⁻¹)⁻¹) *
      p.coordinate⁻¹ = a.val
    group
  have hjb : j b = componentActor hAD a := by
    change componentActor hAD (conjugate p.coordinate b) = _
    rw [hba]
  have hb : j b ∈ d.actor := hjb ▸ ha
  have hbne : b ≠ 1 := by
    intro he
    apply hne
    have hh : componentActor hAD a = 1 := by rw [← hjb, he, map_one]
    exact Subtype.ext (congrArg (fun x : Three × D => x.2.val) hh)
  have hbpow : b ^ 2 = 1 := by
    apply componentMap_injective hAD p.coordinate
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (j b) hb
  have hbfix : permAction b.val point = point :=
    (pure_fixes_iff hAD f hf d p b).mp
      (d.point_fixed (j b) (d.actor_le_sylow hb))
  have hrot (x : AltFive) (hx : j x ∈ d.actor) :
      j (cycle * x * cycle⁻¹) ∈ d.actor :=
    actor_conjugate_mem hAD f hf d p cycle x cycle_fixed hx
  have hfirst (hx : j first ∈ d.actor) :
      j first ∈ d.actor ∧ j second ∈ d.actor := by
    have ht : j (first * second) ∈ d.actor := cycle_first ▸ hrot first hx
    exact ⟨hx, cycle_third ▸ hrot (first * second) ht⟩
  rcases involution_cases b.val (congrArg Subtype.val hbpow)
      (Equiv.Perm.mem_alternatingGroup.mp b.property) hbfix
      (fun he => hbne (Subtype.ext he)) with he | he | he
  · exact hfirst ((Subtype.ext he : b = first) ▸ hb)
  · have hs : j second ∈ d.actor := (Subtype.ext he : b = second) ▸ hb
    exact hfirst (cycle_second ▸ hrot second hs)
  · have ht : j (first * second) ∈ d.actor :=
      (Subtype.ext he : b = first * second) ▸ hb
    have hs : j second ∈ d.actor := cycle_third ▸ hrot (first * second) ht
    exact hfirst (cycle_second ▸ hrot second hs)

/-- With the actor placement proved, the independent point normalization
supplies the exact placement required by the deleted-module calculation. -/
theorem actorPlacement_of_pointNormalization (hcase : D = ⊤ ∨ D = AltFive)
    (σ : Representation (ZMod 2) D V) (hpoint : PointNormalization σ) :
    ActorPlacement hAD σ :=
  actorPlacement_of_normalization hpoint (actor_generators hAD hcase σ)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Deleted
