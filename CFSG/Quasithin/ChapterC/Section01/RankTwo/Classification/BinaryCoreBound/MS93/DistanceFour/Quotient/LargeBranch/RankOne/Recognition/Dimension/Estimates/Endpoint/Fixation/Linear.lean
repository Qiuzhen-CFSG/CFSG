module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Estimates.Endpoint.Fixation.Interface
public import Theory.Representation.InvertedThreeFixed
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.NoncommRing

/-!
# Cubic and reflection saturation of the literal Y

The cubic norm is an idempotent whose image is cubic-fixed. Its kernel is
preserved by the inverting reflection. On that kernel, the complementary
reflection-fixed spaces and their displacement realization bound the dimension
by twice the reflection rank. Codimension at least four and rank at most two
force Y to equal the norm image and exhaust all displacement in the norm kernel.
Thus both generators fix Y, without any invariance hypothesis on Y.

The consumer uses the same marked representation and literal fixed preimage
as `CubicData.saturation_inputs`. Construction of the marked data and transport
to the full first actor remain with the source assembly.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.12)(1)--(2), printed p.910,
and the fixation assertion in the opening of (4.6.12)(5), printed p.911.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension.Fixation

local notation "F" => ZMod 2
variable {W : Type*} [AddCommGroup W] [Module F W]

private theorem twice (x : W) : x + x = 0 := by
  have h := @two_smul F W _ _ _ x
  rw [show (2 : F) = 0 by decide, zero_smul] at h
  exact h.symm

private def cubicNorm (t : Module.End F W) : Module.End F W := t ^ 2 + t + 1

private theorem cubicNorm_fixed (t : Module.End F W) (ht : t ^ 3 = 1) (x : W) :
    t (cubicNorm t x) = cubicNorm t x := by
  change t (t (t x) + t x + x) = t (t x) + t x + x
  rw [map_add, map_add]
  have h3 : t (t (t x)) = x := LinearMap.congr_fun ht x
  rw [h3]
  abel

private theorem cubicNorm_idempotent (t : Module.End F W) (ht : t ^ 3 = 1) :
    IsIdempotentElem (cubicNorm t) := by
  change cubicNorm t * cubicNorm t = cubicNorm t
  ext x
  change t (t (cubicNorm t x)) + t (cubicNorm t x) + cubicNorm t x = cubicNorm t x
  rw [cubicNorm_fixed t ht, cubicNorm_fixed t ht, twice, zero_add]

private theorem reflection_commutes_cubicNorm (t b : Module.End F W)
    (ht : t ^ 3 = 1) (hbt : b * t = t ^ 2 * b) :
    b * cubicNorm t = cubicNorm t * b := by
  have ht4 : t ^ 4 = t := by
    calc
      t ^ 4 = t ^ 3 * t := by rw [pow_succ]
      _ = t := by rw [ht, one_mul]
  have hbt2 : b * t ^ 2 = t * b := by
    calc
      b * t ^ 2 = (b * t) * t := by rw [pow_two, mul_assoc]
      _ = (t ^ 2 * b) * t := by rw [hbt]
      _ = t ^ 2 * (b * t) := by rw [mul_assoc]
      _ = t ^ 2 * (t ^ 2 * b) := by rw [hbt]
      _ = t ^ 4 * b := by rw [← mul_assoc, ← pow_add]
      _ = t * b := by rw [ht4]
  unfold cubicNorm
  simp only [mul_add, add_mul, mul_one, one_mul, hbt2, hbt]
  ac_rfl

variable [FiniteDimensional F W]

private theorem cubicNorm_ker_bound (t b : Module.End F W)
    (ht : t ^ 3 = 1) (hb : b ^ 2 = 1) (hbt : b * t = t ^ 2 * b) :
    Module.finrank F (LinearMap.ker (cubicNorm t)) ≤
      2 * Module.finrank F ↥(LinearMap.range (b - 1) ⊓ LinearMap.ker (cubicNorm t)) := by
  let U := LinearMap.ker (cubicNorm t)
  let tU : Module.End F U := {
    toFun := fun x => ⟨t x, by
      change (cubicNorm t * t) (x : W) = 0
      have hc : cubicNorm t * t = t * cubicNorm t := by
        unfold cubicNorm
        noncomm_ring
      rw [hc, Module.End.mul_apply, x.property, map_zero]⟩
    map_add' := by intro x y; ext; simp
    map_smul' := by intro c x; ext; simp }
  let bU : Module.End F U := {
    toFun := fun x => ⟨b x, by
      change (cubicNorm t * b) (x : W) = 0
      rw [← reflection_commutes_cubicNorm t b ht hbt, Module.End.mul_apply,
        x.property, map_zero]⟩
    map_add' := by intro x y; ext; simp
    map_smul' := by intro c x; ext; simp }
  have htU : tU ^ 2 + tU + 1 = 0 := by
    ext x
    change t (t (x : W)) + t (x : W) + (x : W) = 0
    exact x.property
  have hbU : bU * bU = 1 := by
    ext x
    change b (b (x : W)) = (x : W)
    exact LinearMap.congr_fun hb (x : W)
  have hbtU : bU * tU = tU ^ 2 * bU := by
    ext x
    change b (t (x : W)) = t (t (b (x : W)))
    exact LinearMap.congr_fun hbt (x : W)
  let B : Submodule F U := LinearMap.ker (bU - 1)
  have hdimB : Module.finrank F U ≤ 2 * Module.finrank F B := by
    have hcomp := Representation.InvertedThreeFixed.isCompl_fixed_map tU bU htU hbU hbtU
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq B (B.map tU)
    have hmap := Submodule.finrank_map_le tU B
    have hsumtop : B ⊔ B.map tU = ⊤ := hcomp.codisjoint.eq_top
    have hdisj : B ⊓ B.map tU = ⊥ := hcomp.disjoint.eq_bot
    rw [hsumtop, hdisj, finrank_top, finrank_bot] at hsum
    omega
  -- Each fixed vector in the moving space is the displacement of its t-translate.
  let phi : B →ₗ[F] ↥(LinearMap.range (b - 1) ⊓ U) := {
    toFun := fun x => ⟨((x : U) : W), ⟨⟨t (x : W), by
      have hx : bU (x : U) = (x : U) := sub_eq_zero.mp x.property
      have hdisp := Representation.InvertedThreeFixed.fixed_displacement tU bU htU hbtU
        (x : U) hx
      exact congrArg Subtype.val hdisp⟩, (x : U).property⟩⟩
    map_add' := by intro x y; apply Subtype.ext; rfl
    map_smul' := by intro c x; apply Subtype.ext; rfl }
  have hphi : Function.Injective phi := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(LinearMap.range (b - 1) ⊓ U) => (z : W)) hxy
  have hB_le : Module.finrank F B ≤ Module.finrank F ↥(LinearMap.range (b - 1) ⊓ U) := by
    have hm := phi.range.finrank_le
    rw [LinearMap.finrank_range_of_inj hphi] at hm
    exact hm
  exact hdimB.trans (Nat.mul_le_mul_left 2 hB_le)

/-- A binary cubic norm landing in a subspace of codimension at least four,
with inverting reflection rank at most two, forces both operators to fix it. -/
theorem fixed_of_cubic_norm_and_rank
    (t b : Module.End F W) (Y : Submodule F W)
    (ht : t ^ 3 = 1) (hb : b ^ 2 = 1) (hbt : b * t = t ^ 2 * b)
    (hnorm : ∀ w : W, (t ^ 2 + t + 1 : Module.End F W) w ∈ Y)
    (hcodim : 4 ≤ Module.finrank F (W ⧸ Y))
    (hrank : Module.finrank F (LinearMap.range (b - 1)) ≤ 2) :
    ∀ y ∈ Y, t y = y ∧ b y = y := by
  let C := LinearMap.range (cubicNorm t)
  let U := LinearMap.ker (cubicNorm t)
  let S := LinearMap.range (b - 1) ⊓ U
  have hCY : C ≤ Y := by
    rintro x ⟨w, rfl⟩
    exact hnorm w
  have hcomp : IsCompl C U :=
    LinearMap.IsIdempotentElem.isCompl (cubicNorm_idempotent t ht)
  have hCdim : Module.finrank F C + Module.finrank F U = Module.finrank F W :=
    LinearMap.finrank_range_add_finrank_ker (cubicNorm t)
  have hYdim := Y.finrank_quotient_add_finrank
  have hCYdim := Submodule.finrank_mono hCY
  have hUdim : Module.finrank F U ≤ 2 * Module.finrank F S :=
    cubicNorm_ker_bound t b ht hb hbt
  have hSrank : Module.finrank F S ≤ Module.finrank F (LinearMap.range (b - 1)) :=
    Submodule.finrank_mono inf_le_left
  have hCYeq : C = Y := Submodule.eq_of_le_of_finrank_eq hCY (by omega)
  have hSeq : S = LinearMap.range (b - 1) :=
    Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
  have hmove : LinearMap.range (b - 1) ≤ U := by
    rw [← hSeq]
    exact inf_le_right
  intro y hy
  have hyC : y ∈ C := hCYeq.symm ▸ hy
  have hty : t y = y := by
    obtain ⟨x, rfl⟩ := hyC
    exact cubicNorm_fixed t ht x
  have hbyC : b y ∈ C := by
    obtain ⟨x, rfl⟩ := hyC
    exact ⟨b x, LinearMap.congr_fun (reflection_commutes_cubicNorm t b ht hbt).symm x⟩
  have hdyC : (b - 1) y ∈ C := C.sub_mem hbyC hyC
  have hdyU : (b - 1) y ∈ U := hmove ⟨y, rfl⟩
  exact ⟨hty, sub_eq_zero.mp (Submodule.disjoint_def.mp hcomp.disjoint _ hdyC hdyU)⟩

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The literal endpoint bound and the two natural sections force the marked
cubic and reflection to fix Y. This discharges the linear step in (4.6.12)(5). -/
theorem CubicData.fixed_generators_of_endpoint_bound
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hs : ¬ s.SmallIntersection) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (cubic : CubicData d f s.middle)
    (hendpoint :
      (commutatorPreimage (V R (alpha R)) (Z R s.endpoint) (Z R (alpha R))).relIndex
        (V R (alpha R)) ≤ 4) :
    ∀ v ∈ d.subspace (Sections.fixedPreimage s.middle),
      d.representation cubic.cubic v = v ∧ d.representation cubic.reflection v = v := by
  obtain ⟨hcodim, hrank⟩ := cubic.saturation_inputs common radius hb s hs hbc d f hendpoint
  apply fixed_of_cubic_norm_and_rank
    (d.representation cubic.cubic) (d.representation cubic.reflection)
    (d.subspace (Sections.fixedPreimage s.middle))
    _ _ _ cubic.norm_mem hcodim hrank
  · rw [← map_pow, cubic.cube, map_one]
  · rw [← map_pow, cubic.square, map_one]
  · rw [← map_mul, cubic.inverts, map_mul, map_pow]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension.Fixation
