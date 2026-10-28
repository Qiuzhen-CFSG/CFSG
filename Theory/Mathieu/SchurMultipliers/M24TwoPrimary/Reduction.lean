module

public import Theory.Mathieu.M24.LocalGeometry.LinearFourCore
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.Reduction
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.Transfer
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Restriction and transfer for the two-primary M₂₄ calculation

Restrict a perfect central cover of the actual Witt-design automorphism group
to the full preimage of its chosen octad stabilizer. The resulting surjection
has the identical central kernel. A section of this map excludes two from the
global kernel because the native stabilizer has odd index 759.

The local calculations use two concrete conditions: the preimage of the
pointwise octad kernel has exponent two, and an octad double transposition has
an involutory lift. Ambient conjugacy supplies the latter from the former once
the actual fusion witness is constructed. This file proves that transport;
it does not assert the existence of the witness or either local condition.

The generic prime-kernel quotient and local transfer theorems are reused from
the narrow existing Held and symplectic extension modules; neither import
assumes a multiplier value for any specific group.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, I.1.1–I.1.3,
printed p.407, and the exhaustive Mathieu entry of A.2.3(5), printed p.33;
GLS3 §6.1 and the native E₁₆.A₈ subgroup in Table 5.3e.
-/

open Subgroup PerfectCentralCovering
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.LinearFourCore

namespace Sporadic.Mathieu.SchurMultipliers.M24TwoPrimary
universe u

@[expose] public section
noncomputable section

/-- The stabilizer of the octad extending the native M₂₃ heptad. -/
abbrev OctadGroup := octadStabilizer seedOctad

/-- The pointwise kernel of the literal action on that octad. -/
noncomputable def octadKernel : Subgroup OctadGroup := (action seedOctad).ker

/-- An element inducing a double transposition on the eight octad points. -/
def IsOctadRoot (g : OctadGroup) : Prop :=
  (action seedOctad g).cycleType = {2, 2}

/-- Every element over the translation kernel has square one. -/
def ElementaryKernelPreimage {L : Type*} [Group L] (q : L →* OctadGroup) : Prop :=
  ∀ x, q x ∈ octadKernel → x ^ 2 = 1

/-- An involutory lift of an octad double transposition. -/
def HasInvolutoryRoot {L : Type*} [Group L] (q : L →* OctadGroup) : Prop :=
  ∃ x, x ^ 2 = 1 ∧ IsOctadRoot (q x)

variable {E : Type u} [Group E]

/-- The full preimage of the chosen octad stabilizer under the original cover. -/
abbrev octadPreimage (f : Cover E M24) :=
  (octadStabilizer seedOctad).comap f.toMonoidHom

/-- Restriction of the original covering map to the full octad preimage. -/
def octadProjection (f : Cover E M24) : octadPreimage f →* OctadGroup :=
  (f.toMonoidHom.comp (octadPreimage f).subtype).codRestrict _ (fun x => x.property)

/-- Restriction preserves the literal ambient covering map. -/
theorem octadProjection_coe (f : Cover E M24) (x : octadPreimage f) :
    (octadProjection f x : M24) = f.toMonoidHom x := rfl

/-- The restricted map is still onto the entire octad stabilizer. -/
theorem octadProjection_surjective (f : Cover E M24) :
    Function.Surjective (octadProjection f) := by
  intro y
  obtain ⟨x, hx⟩ := f.surjective y
  exact ⟨⟨x, by change f.toMonoidHom x ∈ octadStabilizer seedOctad; rw [hx]; exact y.property⟩,
    Subtype.ext hx⟩

/-- The restricted kernel remains central in the full preimage. -/
theorem octadProjection_ker_le_center (f : Cover E M24) :
    (octadProjection f).ker ≤ center (octadPreimage f) := by
  intro x hx
  have hfx : f.toMonoidHom x = 1 := congrArg Subtype.val hx
  rw [mem_center_iff]
  intro y
  exact Subtype.ext (mem_center_iff.mp (f.ker_le_center hfx) y)

/-- Restriction to a subgroup leaves the central kernel unchanged. -/
def octadKernelEquiv (f : Cover E M24) :
    (octadProjection f).ker ≃* f.toMonoidHom.ker where
  toFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
  invFun z := ⟨⟨z.val, by
    change f.toMonoidHom z.val ∈ octadStabilizer seedOctad
    rw [z.property]
    exact (octadStabilizer seedOctad).one_mem⟩, Subtype.ext z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The local and global kernels have exactly the same order. -/
theorem octadProjection_kernel_card (f : Cover E M24) :
    Nat.card (octadProjection f).ker = Nat.card f.toMonoidHom.ker :=
  Nat.card_congr (octadKernelEquiv f).toEquiv

/-- A section over the native octad stabilizer excludes two by its odd index 759. -/
theorem not_two_of_octad_section [Finite E] (f : Cover E M24)
    (s : OctadGroup →* octadPreimage f)
    (hs : (octadProjection f).comp s = MonoidHom.id OctadGroup) :
    ¬ 2 ∣ Nat.card f.toMonoidHom.ker := by
  apply not_dvd_card_kernel_of_section f (octadStabilizer seedOctad)
    (by rw [octadStabilizer_index]; decide)
    ((octadPreimage f).subtype.comp s)
  apply MonoidHom.ext
  intro x
  exact congrArg Subtype.val (DFunLike.congr_fun hs x)

/-- Ambient fusion transports an involutory translation lift to an octad root lift.
The conjugating element is lifted through the original surjection. -/
theorem hasInvolutoryRoot_of_fusion (f : Cover E M24)
    (helem : ElementaryKernelPreimage (octadProjection f))
    (v : octadKernel) (a : OctadGroup) (ha : IsOctadRoot a)
    (hconj : IsConj (v.val : M24) (a : M24)) :
    HasInvolutoryRoot (octadProjection f) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  obtain ⟨t, ht⟩ := f.surjective g
  obtain ⟨x, hx⟩ := f.surjective (v.val : M24)
  have hxin : x ∈ octadPreimage f := by
    change f.toMonoidHom x ∈ octadStabilizer seedOctad
    rw [hx]
    exact v.val.property
  have hxV : octadProjection f ⟨x, hxin⟩ ∈ octadKernel := by
    have he : octadProjection f ⟨x, hxin⟩ = v.val := Subtype.ext hx
    rw [he]
    exact v.property
  have hx2 : x ^ 2 = 1 := congrArg Subtype.val (helem ⟨x, hxin⟩ hxV)
  have himage : f.toMonoidHom ((MulAut.conj t) x) = a := by
    change f.toMonoidHom (t * x * t⁻¹) = a
    rw [map_mul, map_mul, map_inv, ht, hx]
    exact hg
  have hyin : (MulAut.conj t) x ∈ octadPreimage f := by
    change f.toMonoidHom ((MulAut.conj t) x) ∈ octadStabilizer seedOctad
    rw [himage]
    exact a.property
  refine ⟨⟨(MulAut.conj t) x, hyin⟩, ?_, ?_⟩
  · apply Subtype.ext
    change ((MulAut.conj t) x) ^ 2 = 1
    rw [← map_pow, hx2, map_one]
  · have he : octadProjection f ⟨(MulAut.conj t) x, hyin⟩ = a := Subtype.ext himage
    rwa [he]

end
end
end Sporadic.Mathieu.SchurMultipliers.M24TwoPrimary
