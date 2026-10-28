module

public import Theory.Alternating.theorem_5_2_3
public import Mathlib.Algebra.Group.Shrink

/-!
# Sections over alternating subgroups from involutory root lifts

For a central extension with kernel of order at most two, an involutory lift
of the standard double transposition rules out a nontrivial derived kernel.
The proved Schur-cover root-square theorem then identifies the derived
subgroup with the alternating quotient and constructs a multiplicative
section. Restricting to the full preimage handles an embedded alternating
subgroup in a larger quotient. Shrinking the finite covering group allows
arbitrary ambient universes without changing the mathematical group.

This supplies the splitting step needed for the HS layers in
Aschbacher–Smith 16.3.5, printed p.1179; the input root squares are obtained
from I.2.2(5a), printed p.409, and the model marks discussed on p.411.
No splitting or covering-layer identification is assumed.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses.CoverLayers
open Subgroup Theory.GroupTheory
open GLS3.Chapter5.SchurPresentation
open RootFourSubgroup

/-- The standard double transposition in an alternating group. -/
def rootInvolution (n : ℕ) : alternatingGroup (Fin (n + 5)) :=
  ⟨rho1 n, rho1_mem_alternating n⟩

theorem rootInvolution_order (n : ℕ) : orderOf (rootInvolution n) = 2 := by
  apply orderOf_eq_prime_iff.mpr
  constructor
  · apply Subtype.ext
    exact (pow_two (rho1 n)).trans (rho1_sq n)
  · intro h
    exact rho1_ne_one n (congrArg Subtype.val h)

/-- Lifting the root involution to involutions removes the central kernel
from the derived subgroup, and hence constructs a section. -/
theorem exists_section_of_root_lifts_sq_one {H : Type*} [Group H] [Finite H]
    (n : ℕ) (f : H →* alternatingGroup (Fin (n + 5)))
    (hf : Function.Surjective f) (hz : f.ker ≤ center H)
    (hc : Nat.card f.ker ≤ 2)
    (hlift : ∀ x : H, f x = rootInvolution n → x ^ 2 = 1) :
    ∃ s : alternatingGroup (Fin (n + 5)) →* H, f.comp s = MonoidHom.id _ := by
  let e : Shrink.{0} H ≃* H := Shrink.mulEquiv
  let : Finite (Shrink.{0} H) := Finite.of_injective e e.injective
  let g := f.comp e.toMonoidHom
  have hg : Function.Surjective g := hf.comp e.surjective
  have hgz : g.ker ≤ center (Shrink.{0} H) := by
    intro x hx
    rw [mem_center_iff]
    intro y
    apply e.injective
    have hxz : e x ∈ center H := hz hx
    simpa only [map_mul] using mem_center_iff.mp hxz (e y)
  let D := _root_.commutator (Shrink.{0} H)
  let gD := g.comp D.subtype
  have hDcard : Nat.card gD.ker ≤ 2 := by
    apply le_trans _ hc
    let j : gD.ker → f.ker := fun x => ⟨e x.val.val, x.property⟩
    apply Nat.card_le_card_of_injective j
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val h)
  have hDker : gD.ker = ⊥ := by
    apply derivedKernel_eq_bot_of_root_lifts_sq_one n g hg hgz hDcard
    intro x hx
    apply Subtype.ext
    apply e.injective
    change e (x.val ^ 2) = e 1
    rw [map_pow, map_one]
    exact hlift (e x.val) hx
  have hDsurj : Function.Surjective gD := by
    have hmap : D.map g = ⊤ := by
      dsimp [D]
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hg]
      exact Group.IsPerfect.commutator_eq_top
    intro y
    obtain ⟨x, hx, hxy⟩ := (show y ∈ D.map g by rw [hmap]; trivial)
    exact ⟨⟨x, hx⟩, hxy⟩
  let d : D ≃* alternatingGroup (Fin (n + 5)) :=
    MulEquiv.ofBijective gD ⟨(MonoidHom.ker_eq_bot_iff _).mp hDker, hDsurj⟩
  refine ⟨e.toMonoidHom.comp (D.subtype.comp d.symm.toMonoidHom), ?_⟩
  apply MonoidHom.ext
  intro x
  exact d.apply_symm_apply x

/-- A root-square calculation in the original central extension gives a
section over a specified embedded alternating subgroup. -/
theorem exists_section_over_alternating {H Q : Type*} [Group H] [Finite H] [Group Q]
    (n : ℕ) (f : H →* Q) (hf : Function.Surjective f)
    (hz : f.ker ≤ center H) (hc : Nat.card f.ker ≤ 2)
    (j : alternatingGroup (Fin (n + 5)) →* Q) (hj : Function.Injective j)
    (hlift : ∀ x : H, f x = j (rootInvolution n) → x ^ 2 = 1) :
    ∃ s : alternatingGroup (Fin (n + 5)) →* H, f.comp s = j := by
  let P := j.range.comap f
  let e : alternatingGroup (Fin (n + 5)) ≃* j.range := MonoidHom.ofInjective hj
  let g : P →* alternatingGroup (Fin (n + 5)) :=
    e.symm.toMonoidHom.comp (f.subgroupComap j.range)
  have hfac (x : P) : j (g x) = f x.val := by
    exact congrArg Subtype.val (e.apply_symm_apply (f.subgroupComap j.range x))
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨x, hx⟩ := hf (j a)
    have hxp : x ∈ P := by change f x ∈ j.range; rw [hx]; exact ⟨a, rfl⟩
    refine ⟨⟨x, hxp⟩, hj ?_⟩
    exact (hfac ⟨x, hxp⟩).trans hx
  have hgz : g.ker ≤ center P := by
    intro x hx
    have hfx : f x.val = 1 := by rw [← hfac, hx, map_one]
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_center_iff.mp (hz hfx) y.val)
  have hgc : Nat.card g.ker ≤ 2 := by
    apply le_trans _ hc
    let k : g.ker → f.ker := fun x => ⟨x.val.val, by
      change f x.val.val = 1
      rw [← hfac, x.property, map_one]⟩
    apply Nat.card_le_card_of_injective k
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : f.ker => (z : H)) h))
  obtain ⟨s, hs⟩ := exists_section_of_root_lifts_sq_one n g hg hgz hgc (by
    intro x hx
    apply Subtype.ext
    exact hlift x.val ((hfac x).symm.trans (congrArg j hx)))
  refine ⟨P.subtype.comp s, ?_⟩
  apply MonoidHom.ext
  intro a
  exact (hfac (s a)).symm.trans (congrArg j (DFunLike.congr_fun hs a))

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses.CoverLayers
