module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive.Cover
public import Mathlib.GroupTheory.GroupAction.Quotient


/-!
# Odd component orbits in central natural A₅ covers

Each noncentral component orbit projects bijectively onto the fifteen nonzero
natural vectors: fixed-point lifting identifies the two stabilizers. Summing
these fifteen lifts labels the orbit by a vector in the central kernel.
Translation by a kernel vector changes this label by that same vector. Hence
an actor fixing the kernel preserves every component orbit, and a two-group
of such actors has a fixed point in each orbit.

Binary kernels of dimension at most one are fixed by all actors. For an inner
natural actor, twisted uniqueness on the fully moved cover identifies the
full actor with the corresponding component element. These arguments require
no field structure on the central-line quotient and no outer orbit census.

Source: Aschbacher--Smith, 13.1.12, printed p.872/PDF p.889, using the central
natural fixed-lifting theorem of I.2.3 and uniqueness of covers from I.1.5.
-/

public noncomputable section

open Representation Representation.OneCohomology
open Representation.OneCohomology.CentralCoverOriginalAction
open Representation.SL2FourNatural
open scoped BigOperators
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive
namespace NaturalCover
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  (d : NaturalCover A W)

private abbrev Nonzero := {v : V // v ≠ 0}

private theorem card_nonzero : Fintype.card Nonzero = 15 := by
  classical
  change Fintype.card {v : V // v ≠ 0} = 15
  rw [Fintype.card_subtype_compl, SL2FourNatural.card_vector]
  simp

private theorem projection_ne_zero (l : SL) {w : W} (hw : d.projection w ≠ 0) :
    d.projection (d.component l w) ≠ 0 := by
  rw [d.projection.isIntertwining]
  exact fun h => hw ((action l).injective (h.trans (map_zero _).symm))

private theorem same_projection (l : SL) (w : W)
    (he : d.projection (d.component l w) = d.projection w) : d.component l w = w :=
  (d.fixed_iff_natural_fixed l w).mpr ((LinearMap.congr_fun (d.projection.isIntertwining' l) w).symm.trans he)

private theorem orbit_injective (g h : SL) (w : W)
    (he : d.projection (d.component g w) = d.projection (d.component h w)) :
    d.component g w = d.component h w := by
  have hh : d.component (h⁻¹ * g) w = w := by
    apply d.same_projection
    rw [d.projection.isIntertwining, map_mul, Module.End.mul_apply]
    rw [← d.projection.isIntertwining, he, d.projection.isIntertwining]
    simp [← Module.End.mul_apply, ← map_mul]
  have hh' := congrArg (d.component h) hh
  simpa [← Module.End.mul_apply, ← map_mul] using hh'

private noncomputable def lift (w : W) (hw : d.projection w ≠ 0) (v : Nonzero) : W :=
  d.component (Classical.choose (transitive_nonzero (d.projection w) v hw v.property)) w

private theorem lift_mem (w : W) (hw : d.projection w ≠ 0) (v : Nonzero) :
    ∃ l : SL, d.component l w = d.lift w hw v := ⟨_, rfl⟩

private theorem projection_lift (w : W) (hw : d.projection w ≠ 0) (v : Nonzero) :
    d.projection (d.lift w hw v) = v := by
  rw [lift, d.projection.isIntertwining]
  exact Classical.choose_spec (transitive_nonzero (d.projection w) v hw v.property)

private theorem lift_unique (w : W) (hw : d.projection w ≠ 0) (v : Nonzero)
    (l : SL) (hl : d.projection (d.component l w) = v) :
    d.component l w = d.lift w hw v := by
  obtain ⟨g,hg⟩ := d.lift_mem w hw v
  rw [← hg]
  exact d.orbit_injective l g w (hl.trans ((d.projection_lift w hw v).symm.trans
    (congrArg d.projection hg).symm))

private noncomputable def orbitSum (w : W) (hw : d.projection w ≠ 0) : W :=
  ∑ v : Nonzero, d.lift w hw v

private def permNonzero (e : V ≃ₗ[ZMod 2] V) : Equiv.Perm Nonzero :=
  { toFun v := ⟨e v, fun h => v.property (e.injective (h.trans e.map_zero.symm))⟩
    invFun v := ⟨e.symm v, fun h => v.property (e.symm.injective (h.trans e.symm.map_zero.symm))⟩
    left_inv v := Subtype.ext (e.symm_apply_apply v)
    right_inv v := Subtype.ext (e.apply_symm_apply v) }

private theorem sum_fixed (w : W) (hw : d.projection w ≠ 0) :
    d.orbitSum w hw ∈ fixed d.component := by
  intro l
  change d.component l (∑ v : Nonzero, d.lift w hw v) = _
  rw [map_sum]
  apply Fintype.sum_equiv (permNonzero (action l))
  intro v
  obtain ⟨g,hg⟩ := d.lift_mem w hw v
  rw [← hg]
  rw [← Module.End.mul_apply, ← map_mul]
  apply d.lift_unique
  rw [map_mul, Module.End.mul_apply, d.projection.isIntertwining, hg, d.projection_lift]
  rfl

private theorem actor_projection_ne_zero (a : A) {w : W} (hw : d.projection w ≠ 0) :
    d.projection (d.actor a w) ≠ 0 := by
  rw [d.quotient_action]
  exact fun h => hw ((actorEquiv d.naturalActor a).injective (h.trans (map_zero _).symm))

private theorem sum_actor (a : A) (w : W) (hw : d.projection w ≠ 0) :
    d.actor a (d.orbitSum w hw) =
      d.orbitSum (d.actor a w) (d.actor_projection_ne_zero a hw) := by
  change d.actor a (∑ v : Nonzero, d.lift w hw v) = _
  rw [map_sum]
  apply Fintype.sum_equiv (permNonzero (actorEquiv d.naturalActor a))
  intro v
  obtain ⟨g,hg⟩ := d.lift_mem w hw v
  rw [← hg, d.compatible]
  apply d.lift_unique
  rw [← d.compatible, d.quotient_action, hg, d.projection_lift]
  rfl

private theorem sum_same_orbit (g : SL) (w : W) (hw : d.projection w ≠ 0) :
    d.orbitSum (d.component g w) (d.projection_ne_zero g hw) = d.orbitSum w hw := by
  apply Finset.sum_congr rfl
  intro v _
  obtain ⟨l,hl⟩ := d.lift_mem (d.component g w) (d.projection_ne_zero g hw) v
  rw [← hl, ← Module.End.mul_apply, ← map_mul]
  apply d.lift_unique
  rw [map_mul, Module.End.mul_apply, hl, d.projection_lift]

private theorem sum_translate (w z : W) (hw : d.projection w ≠ 0)
    (hz : z ∈ d.projection.toLinearMap.ker) :
    d.orbitSum (w + z) (by simpa [map_add, show d.projection z = 0 from hz] using hw) =
      d.orbitSum w hw + z := by
  have he (v : Nonzero) :
      d.lift (w + z) (by simpa [map_add, show d.projection z = 0 from hz] using hw) v =
        d.lift w hw v + z := by
    obtain ⟨g,hg⟩ := d.lift_mem w hw v
    symm
    calc
      d.lift w hw v + z = d.component g (w + z) := by
        rw [map_add, d.cover.2.1 hz g, hg]
      _ = _ := by
        apply d.lift_unique
        rw [map_add, d.cover.2.1 hz g, map_add, show d.projection z = 0 from hz, add_zero, hg, d.projection_lift]
  simp only [orbitSum, he, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, card_nonzero]
  have h15 : (15 : ℕ) • z = z := by
    calc
      _ = (15 : ZMod 2) • z := (Nat.cast_smul_eq_nsmul (ZMod 2) 15 z).symm
      _ = z := by rw [show (15 : ZMod 2) = 1 by decide, one_smul]
  rw [h15]

/-- An actor fixing the central kernel preserves each component orbit. -/
theorem actor_mem_component_orbit (a : A)
    (ha : ∀ z ∈ d.projection.toLinearMap.ker, d.actor a z = z) (w : W) :
    ∃ l : SL, d.component l w = d.actor a w := by
  by_cases hw : d.projection w = 0
  · refine ⟨1, ?_⟩
    simpa using (ha w hw).symm
  obtain ⟨l,hl⟩ := transitive_nonzero (d.projection w) (d.projection (d.actor a w))
    hw (d.actor_projection_ne_zero a hw)
  let x := d.component l w
  let y := d.actor a w
  have hp : d.projection x = d.projection y :=
    (LinearMap.congr_fun (d.projection.isIntertwining' l) w).trans hl
  have hz : y - x ∈ d.projection.toLinearMap.ker := by
    change d.projection (y - x) = 0
    rw [map_sub, hp, sub_self]
  have hs : d.orbitSum x (d.projection_ne_zero l hw) =
      d.orbitSum y (d.actor_projection_ne_zero a hw) := by
    change d.orbitSum (d.component l w) _ = d.orbitSum (d.actor a w) _
    rw [d.sum_same_orbit l w hw, ← d.sum_actor a w hw]
    exact (ha _ (d.fixed_eq_kernel ▸ d.sum_fixed w hw)).symm
  have ht := d.sum_translate x (y-x) (d.projection_ne_zero l hw) hz
  have hexy : x + (y-x) = y := by abel
  simp only [hexy] at ht
  rw [← hs] at ht
  have hz0 : y - x = 0 := add_eq_left.mp ht.symm
  exact ⟨l, (sub_eq_zero.mp hz0).symm⟩

/-- If a two-group fixes the central kernel, a component translate of every
vector is fixed by that two-group. -/
theorem exists_fixed_component_translate (hp : IsPGroup 2 A)
    (hfix : ∀ a z, z ∈ d.projection.toLinearMap.ker → d.actor a z = z) (w : W) :
    ∃ l : SL, ∀ a : A, d.actor a (d.component l w) = d.component l w := by
  classical
  by_cases hw : d.projection w = 0
  · refine ⟨1, ?_⟩
    intro a
    simpa using hfix a w hw
  let O := Set.range (fun l : SL => d.component l w)
  have hstable (a : A) (x : O) : d.actor a x ∈ O := by
    obtain ⟨g,hg⟩ := x.property
    change d.component g w = (x : W) at hg
    obtain ⟨l,hl⟩ := d.actor_mem_component_orbit a (hfix a) w
    refine ⟨d.conjugation a g * l, ?_⟩
    change d.component (d.conjugation a g * l) w = d.actor a x
    rw [map_mul, Module.End.mul_apply, hl, ← d.compatible, hg]
  let : MulAction A O :=
    { smul a x := ⟨d.actor a x, hstable a x⟩
      one_smul x := Subtype.ext (by change d.actor 1 x = x; simp)
      mul_smul a b x := Subtype.ext (by
        change d.actor (a*b) x = d.actor a (d.actor b x)
        rw [map_mul, Module.End.mul_apply]) }
  let f : Nonzero → O := fun v => ⟨d.lift w hw v, d.lift_mem w hw v⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v z hvz
      apply Subtype.ext
      have hh := congrArg (fun x : O => d.projection x) hvz
      exact (d.projection_lift w hw v).symm.trans (hh.trans (d.projection_lift w hw z))
    · rintro ⟨x,g,rfl⟩
      refine ⟨⟨d.projection (d.component g w), d.projection_ne_zero g hw⟩, ?_⟩
      exact Subtype.ext (d.lift_unique w hw _ g rfl).symm
  have hcard : Nat.card O = 15 := by
    rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, card_nonzero]
  obtain ⟨x,hx⟩ := hp.nonempty_fixed_point_of_prime_not_dvd_card O (by rw [hcard]; decide)
  obtain ⟨l,hl⟩ := x.property
  refine ⟨l, ?_⟩
  intro a
  have hh := congrArg Subtype.val (MulAction.mem_fixedPoints.mp hx a)
  change d.actor a x = x at hh
  rwa [← hl] at hh

end NaturalCover
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive

namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive
namespace NaturalCover
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  (d : NaturalCover A W)

/-- The natural inner actor has exactly the same lift on a fully moved cover. -/
theorem actor_eq_component_of_natural (a : A) (l : SL)
    (ha : ∀ v, d.naturalActor a v = Natural l v) :
    ∀ w, d.actor a w = d.component l w := by
  have hc (g : SL) : d.conjugation a g = l * g * l⁻¹ := by
    apply action_faithful
    apply LinearEquiv.ext
    intro v
    have h := d.natural_compatible a g (Natural l⁻¹ v)
    rw [ha, ha] at h
    have hi : Natural l (Natural l⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [hi] at h
    change Natural (d.conjugation a g) v = Natural (l * g * l⁻¹) v
    calc
      _ = Natural l (Natural g (Natural l⁻¹ v)) := h.symm
      _ = _ := by rw [map_mul, map_mul]; rfl
  have he : d.actor a = d.component l := by
    apply CentralCoverOriginalAction.lift_unique d.component
      (d.component.comp (d.conjugation a).toMonoidHom) d.cover.2.2
      d.projection.toLinearMap (fun w hw g => d.cover.2.1 hw (d.conjugation a g))
    · exact d.compatible a
    · intro g w
      change d.component l (d.component g w) =
        d.component (d.conjugation a g) (d.component l w)
      rw [hc]
      simp [← Module.End.mul_apply, ← map_mul, mul_assoc]
    · intro w
      change d.projection (d.actor a w) = d.projection (d.component l w)
      rw [d.quotient_action, ha, d.projection.isIntertwining]
  exact fun w => LinearMap.congr_fun he w

/-- Rank zero and rank one binary kernels are fixed by every original actor. -/
theorem kernel_fixed_of_finrank_le_one [FiniteDimensional (ZMod 2) W]
    (hd : Module.finrank (ZMod 2) d.projection.toLinearMap.ker ≤ 1)
    (a : A) (z : W) (hz : z ∈ d.projection.toLinearMap.ker) : d.actor a z = z := by
  classical
  let K := d.projection.toLinearMap.ker
  let e : K ≃ₗ[ZMod 2] K :=
    { toFun z := ⟨d.actor a z, by
        change d.projection (d.actor a z) = 0
        rw [d.quotient_action, show d.projection z = 0 from z.property, map_zero]⟩
      invFun z := ⟨d.actor a⁻¹ z, by
        change d.projection (d.actor a⁻¹ z) = 0
        rw [d.quotient_action, show d.projection z = 0 from z.property, map_zero]⟩
      left_inv z := Subtype.ext (by simp [← Module.End.mul_apply, ← map_mul])
      right_inv z := Subtype.ext (by simp [← Module.End.mul_apply, ← map_mul])
      map_add' x y := Subtype.ext (map_add _ _ _)
      map_smul' c x := Subtype.ext (map_smul _ _ _) }
  obtain ⟨v,hv⟩ := finrank_le_one_iff.mp hd
  have he : e v = v := by
    obtain ⟨c,hc⟩ := hv (e v)
    fin_cases c
    · change (0 : ZMod 2) • v = e v at hc
      rw [zero_smul] at hc
      have hev : e v = 0 := hc.symm
      have hv0 : v = 0 := e.injective (hev.trans e.map_zero.symm)
      rw [hv0, map_zero]
    · change (1 : ZMod 2) • v = e v at hc
      simpa only [one_smul] using hc.symm
  obtain ⟨c,hc⟩ := hv ⟨z,hz⟩
  have hzfix : e ⟨z,hz⟩ = ⟨z,hz⟩ := by rw [← hc, map_smul, he]
  exact congrArg Subtype.val hzfix
end NaturalCover
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive
