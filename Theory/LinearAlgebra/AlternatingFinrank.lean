module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Even dimension of alternating spaces

Hyperbolic splitting proves that a nondegenerate alternating space has even
dimension, including in characteristic two. Restricting to a complement of
the radical gives the corresponding parity statement for degenerate forms.

Adapted from ATLAS, Gerald Höhn, `Atlas/LinearAlgebra/SymplecticBasis.lean`
and `AlternatingFinrank.lean`. Changes: CFSG module boundaries and namespace,
a radical-complement consequence, and compatibility with this Lean version.
The adapted material is covered by the ATLAS Research and Attribution License
version 1.0; the complete license is in `AlternatingFinrank.LICENSE` alongside
this file. The same notice and license must accompany compiled distributions.
-/
public section

noncomputable section
namespace AlternatingForm
open LinearMap
section
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (B : LinearMap.BilinForm F V) (hA : B.IsAlt)

/-- Nondegeneracy supplies a normalized partner without a characteristic restriction. -/
private theorem exists_partner (hB : B.Nondegenerate) {e : V} (he : e ≠ 0) :
    ∃ f, B e f = 1 := by
  obtain ⟨v,hv⟩ : ∃ v, B e v ≠ 0 := by
    by_contra! h
    exact he (hB.1 e h)
  exact ⟨(B e v)⁻¹ • v, by simp [map_smul, hv]⟩

variable (e f : V) (hef : B e f = 1)

/-- The simultaneous orthogonal complement of the selected hyperbolic pair. -/
private def complement : Submodule F V := (B.flip e).ker ⊓ (B.flip f).ker

@[simp] private theorem mem_complement (x : V) :
    x ∈ complement B e f ↔ B x e = 0 ∧ B x f = 0 := Iff.rfl

/-- Projection onto the selected plane, in its normalized coordinates. -/
private def planeProjection : V →ₗ[F] V := (B.flip f).smulRight e - (B.flip e).smulRight f

@[simp] private theorem planeProjection_apply (x : V) :
    planeProjection B e f x = (B x f) • e - (B x e) • f := rfl

include hA hef
private theorem reversed_pairing : B f e = -1 := by rw [← hA.neg_eq e f, hef]

@[simp] private theorem projection_e : planeProjection B e f e = e := by
  simp [planeProjection_apply, hef, hA.self_eq_zero]

@[simp] private theorem projection_f : planeProjection B e f f = f := by
  simp [planeProjection_apply, reversed_pairing B hA e f hef, hA.self_eq_zero]

private theorem remainder_mem (x : V) : x - planeProjection B e f x ∈ complement B e f := by
  simp only [mem_complement, planeProjection_apply, map_sub, map_smul,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hA.self_eq_zero,
    reversed_pairing B hA e f hef, hef]
  constructor <;> ring

/-- The hyperbolic coordinates plus the actual complement give a direct decomposition. -/
private def split : V ≃ₗ[F] (F × F) × complement B e f where
  toFun x := ((B x f, -B x e), ⟨x-planeProjection B e f x, remainder_mem B hA e f hef x⟩)
  invFun z := z.1.1 • e + z.1.2 • f + z.2.val
  left_inv x := by
    simp only [planeProjection_apply, neg_smul]
    abel
  right_inv z := by
    rcases z with ⟨⟨r,s⟩,⟨w,hw⟩⟩
    have hw' := (mem_complement B e f w).mp hw
    apply Prod.ext
    · apply Prod.ext <;>
        simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
          hef, hA.self_eq_zero, reversed_pairing B hA e f hef, hw'.1, hw'.2]
    · apply Subtype.ext
      simp only [planeProjection_apply, map_add, map_smul, hef, hA.self_eq_zero,
        reversed_pairing B hA e f hef, hw'.1, hw'.2]
      simp
  map_add' x y := by
    apply Prod.ext
    · simp [map_add, add_comm]
    · apply Subtype.ext
      change x+y-planeProjection B e f (x+y) =
        (x-planeProjection B e f x)+(y-planeProjection B e f y)
      rw [map_add]
      abel
  map_smul' r x := by
    apply Prod.ext
    · simp [map_smul, mul_neg]
    · apply Subtype.ext
      simp [map_smul, smul_sub]

omit hef in
/-- The alternating restriction on the actual complement. -/
private theorem complement_alternating : (B.restrict (complement B e f)).IsAlt := by
  intro x
  exact hA.self_eq_zero x.val

/-- Nondegeneracy survives hyperbolic splitting. -/
private theorem complement_nondegenerate (hB : B.Nondegenerate) :
    (B.restrict (complement B e f)).Nondegenerate := by
  have hs : (B.restrict (complement B e f)).SeparatingLeft := by
    intro x hx
    apply Subtype.ext
    apply hB.1 x.val
    intro y
    obtain ⟨z,rfl⟩ := (split B hA e f hef).symm.surjective y
    rcases z with ⟨⟨r,s⟩,w⟩
    have hp := x.prop
    have hz : B x.val w.val = 0 := hx w
    change B x.val (r • e + s • f + w.val) = 0
    simp [map_add, map_smul, (mem_complement B e f x.val).mp hp, hz]
  refine ⟨hs, ?_⟩
  intro x hx
  apply hs x
  intro y
  change B x.val y.val = 0
  rw [← hA.neg_eq y.val x.val]
  change -((B.restrict (complement B e f)) y x) = 0
  rw [hx y, neg_zero]

private theorem finrank_complement [FiniteDimensional F V] :
    Module.finrank F (complement B e f) + 2 = Module.finrank F V := by
  have h := (split B hA e f hef).finrank_eq
  simpa [Module.finrank_prod, Module.finrank_self, Nat.add_comm] using h.symm

end
universe u v
variable {F : Type u} [Field F]

/-- Splitting off normalized alternating planes proves even dimension without
any restriction on the characteristic of the field. -/
theorem even_finrank {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V) (hA : B.IsAlt) (hB : B.Nondegenerate) :
    Even (Module.finrank F V) := by
  generalize hn : Module.finrank F V = n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases hn0 : n = 0
    · simp [hn0]
    · have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (M := V) (by omega)
      obtain ⟨a, ha⟩ := exists_ne (0 : V)
      obtain ⟨b, hab⟩ := exists_partner B hB ha
      let P := complement B a b
      have hd := finrank_complement B hA a b hab
      have hlt : Module.finrank F P < n := by dsimp only [P]; omega
      have he := ih (Module.finrank F P) hlt (B.restrict P)
        (complement_alternating B hA a b)
        (complement_nondegenerate B hA a b hab hB) rfl
      obtain ⟨k, hk⟩ := he
      refine ⟨k + 1, ?_⟩
      dsimp only [P] at hk
      omega

/-- The codimension of the radical of an alternating form is even. -/
theorem even_finrank_sub_finrank_ker {V : Type v} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (B : LinearMap.BilinForm F V) (hA : B.IsAlt) :
    Even (Module.finrank F V - Module.finrank F B.ker) := by
  obtain ⟨P, hP⟩ := B.ker.exists_isCompl
  have hs : (B.restrict P).SeparatingLeft := by
    intro x hx
    have hxker : (x : V) ∈ B.ker := by
      rw [LinearMap.mem_ker]
      ext y
      obtain ⟨z, w, hz, hw, rfl⟩ :=
        Submodule.codisjoint_iff_exists_add_eq.mp hP.codisjoint y
      have hz0 : B z x = 0 := LinearMap.congr_fun hz x
      have hxz : B x z = 0 := (hA.eq_iff).mpr hz0
      have hxw : B x w = 0 := hx ⟨w, hw⟩
      simp [hxz, hxw]
    have hx0 : (x : V) = 0 := hP.disjoint.le_bot ⟨hxker, x.property⟩
    exact Subtype.ext hx0
  have hnd : (B.restrict P).Nondegenerate := by
    refine ⟨hs, fun x hx => hs x fun y => ?_⟩
    exact (hA.eq_iff).mpr (hx y)
  have he := even_finrank (B.restrict P) (fun x => hA x) hnd
  have hd := Submodule.finrank_add_eq_of_isCompl hP
  rwa [← hd, Nat.add_sub_cancel_left]

end AlternatingForm
