module
public import Theory.GroupTheory.DihedralRelations
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Tactic.Group

/-!
# Literal order-sixteen Weyl evaluation

Two involutions whose product has eighth power one evaluate the abstract
sixteen-element dihedral group. Its two marked reflections generate it, so
local torus-conjugation equations extend to the entire Weyl action. This is
used by the full Ree normalizer presentation; no quotient relation is promoted
to a relation between lifts, and no injectivity is assumed.

Source: GLS3 2.3.2--4, `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section
namespace ReeF4.RootPresentationRecognition.WeylPresentation
open Subgroup
abbrev Weyl := DihedralGroup 8

def simple : Bool → Weyl
  | false => .sr 0
  | true => .sr 1

theorem simple_generate : closure (Set.range simple) = ⊤ := by
  apply top_unique
  intro w _
  have ha : simple false ∈ closure (Set.range simple) := subset_closure ⟨false,rfl⟩
  have hb : simple true ∈ closure (Set.range simple) := subset_closure ⟨true,rfl⟩
  have hr : (DihedralGroup.r 1 : Weyl) ∈ closure (Set.range simple) := by
    simpa only [simple, DihedralGroup.sr_mul_sr, sub_zero] using mul_mem ha hb
  have hp (i : ZMod 8) : (DihedralGroup.r i : Weyl) ∈ closure (Set.range simple) := by
    simpa only [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val] using pow_mem hr i.val
  cases w with
  | r i => exact hp i
  | sr i => simpa only [simple, DihedralGroup.sr_mul_r, zero_add] using mul_mem ha (hp i)

variable {G : Type*} [Group G]

/-- The literal two involutions and their mixed relation construct evaluation. -/
def lift (n : Bool → G) (hsq : ∀ s, n s ^ 2 = 1)
    (hmix : (n false * n true)^8 = 1) : Weyl →* G :=
  Theory.GroupTheory.DihedralRelations.ofRelations (n false * n true) (n false)
    hmix (hsq false) (by
      have h0 : n false * n false = 1 := by simpa only [pow_two] using hsq false
      have hi0 : (n false)⁻¹ = n false := inv_eq_of_mul_eq_one_right h0
      have hi1 : (n true)⁻¹ = n true := inv_eq_of_mul_eq_one_right
        (by simpa only [pow_two] using hsq true)
      simp only [mul_inv_rev,hi0,hi1,← mul_assoc,h0,one_mul])

@[simp] theorem lift_simple (n : Bool → G) (hsq : ∀ s, n s ^ 2 = 1)
    (hmix : (n false * n true)^8 = 1) (s : Bool) : lift n hsq hmix (simple s) = n s := by
  cases s
  · simp [lift,simple]
  · have hh : n false * n false = 1 := by simpa only [pow_two] using hsq false
    change n false * (n false * n true) ^ (1 : ZMod 8).val = n true
    rw [show (1 : ZMod 8).val = 1 from rfl, pow_one, ← mul_assoc, hh, one_mul]

/-- The two literal involutions generate exactly the evaluation image. -/
theorem lift_range (n : Bool → G) (hsq : ∀ s, n s ^ 2 = 1)
    (hmix : (n false * n true)^8 = 1) :
    (lift n hsq hmix).range = closure (Set.range n) := by
  rw [MonoidHom.range_eq_map, ← simple_generate, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y,⟨s,rfl⟩,rfl⟩
    exact ⟨s,(lift_simple n hsq hmix s).symm⟩
  · rintro ⟨s,rfl⟩
    exact ⟨simple s,⟨s,rfl⟩,lift_simple n hsq hmix s⟩

/-- Homomorphisms are determined by the two marked reflections. -/
theorem hom_ext {f g : Weyl →* G} (h : ∀ s, f (simple s) = g (simple s)) : f = g := by
  apply MonoidHom.ext
  intro w
  have hw : w ∈ closure (Set.range simple) := by rw [simple_generate]; trivial
  induction hw using Subgroup.closure_induction with
  | mem x hx => obtain ⟨s,rfl⟩ := hx; exact h s
  | one => simp only [map_one]
  | mul x y _ _ hx hy => simp only [map_mul,hx,hy]
  | inv x _ hx => simp only [map_inv,hx]

variable {T : Type*} [Group T]

/-- Checking conjugation on the two simple letters checks the full Weyl action. -/
theorem action_compatible (a : Weyl →* MulAut T) (h : T →* G) (n : Weyl →* G)
    (hs : ∀ s t, h (a (simple s) t) = n (simple s) * h t * (n (simple s))⁻¹)
    (w : Weyl) : h.comp (a w).toMonoidHom = (MulAut.conj (n w)).toMonoidHom.comp h := by
  have hw : w ∈ closure (Set.range simple) := by rw [simple_generate]; trivial
  suffices he : ∀ t, h (a w t) = n w * h t * (n w)⁻¹ from MonoidHom.ext he
  induction hw using Subgroup.closure_induction with
  | mem x hx => obtain ⟨s,rfl⟩ := hx; exact hs s
  | one => intro t; simp
  | mul x y _ _ hx hy =>
    intro t
    simp only [map_mul, MulAut.mul_apply, mul_inv_rev, hx, hy]
    group
  | inv x _ hx =>
    intro t
    have he := hx ((a x)⁻¹ t)
    simp only [MulAut.apply_inv_self] at he
    rw [map_inv, map_inv]
    have he' := congrArg (fun z => (n x)⁻¹ * z * n x) he
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one, inv_inv] using he'.symm

end ReeF4.RootPresentationRecognition.WeylPresentation
