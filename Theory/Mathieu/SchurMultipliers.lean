module

public import Theory.Mathieu.SchurMultipliers.FiniteCovers
public import Theory.Mathieu.SchurMultipliers.Models
public import Theory.Mathieu.SchurMultipliers.M12DoubleCover
public import Theory.Mathieu.SchurMultipliers.M12Upper
public import Theory.Mathieu.SchurMultipliers.M23Kernel
public import Theory.Mathieu.SchurMultipliers.M24TwoPrimary
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.CoveringKernelCard

/-!
# Mathieu Schur multipliers

The native M₁₂ model has multiplier C₂. Universality gives a surjection onto
the concrete perfect double cover pulled back from Schur's cover of A₁₂;
restriction to kernels gives the lower bound of two. The independent
first-parabolic calculation supplies the matching upper bound.

Every finite perfect central cover of native M₁₁, M₂₃ or M₂₄ is injective.
For M₂₄ the two-primary exclusion combines with the already proved
two-group restriction. Thus every chosen universal kernel has the stated
group structure. The canonical universal projections are also instantiated.

Source: Aschbacher–Smith I.1.3, printed p.407, with the exhaustive lists
A.2.2–A.2.3. The independent M₂₂ calculation is outside this module.
-/

open Subgroup Theory.GroupTheory PerfectCentralCovering

namespace Sporadic.Mathieu
namespace SchurMultipliers

universe u

/-- The exact trivial multiplier of M₁₁, for every chosen universal covering.
In fact, the same identification holds without its universal property. -/
public theorem m11_schurMultiplier
    {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    (f : Covering L M11) :
    Nonempty (f.toMonoidHom.ker ≃* Multiplicative (ZMod 1)) := by
  let c : Cover L M11 :=
    { toMonoidHom := f.toMonoidHom
      surjective := f.surjective
      isPerfect := inferInstance
      ker_le_center := f.ker_le_center }
  have hk : f.toMonoidHom.ker = ⊥ := m11_cover_kernel_eq_bot c
  have : Subsingleton f.toMonoidHom.ker := by
    rw [hk]
    infer_instance
  let : Unique f.toMonoidHom.ker := ⟨⟨1⟩, fun x => Subsingleton.elim _ _⟩
  let : Unique (Multiplicative (ZMod 1)) := ⟨⟨1⟩, fun x => Subsingleton.elim _ _⟩
  exact ⟨MulEquiv.ofUnique⟩

/-- The double cover and the upper bound determine the order of every chosen
universal M₁₂ kernel. No universality of the constructed double cover is assumed. -/
public theorem m12_universal_kernel_card
    {L : Type u} [Group L] [Finite L] [IsQuasisimple L]
    (f : Covering L M12) (hf : Covering.IsUniversal.{0, u, 0} f) :
    Nat.card f.toMonoidHom.ker = 2 := by
  let : IsQuasisimple M12DoubleCover.Carrier := M12DoubleCover.cover.isQuasisimple
  let c := M12DoubleCover.cover.toCovering
  obtain ⟨h, hh, _⟩ := hf M12DoubleCover.Carrier c
  have hd := kernel_card_dvd_of_surjective_factor f.toMonoidHom c.toMonoidHom
    h.toMonoidHom h.surjective (congrArg Covering.toMonoidHom hh)
  have hc : Nat.card c.toMonoidHom.ker = 2 := M12DoubleCover.cover_card_ker
  rw [hc] at hd
  exact le_antisymm (m12_cover_kernel_card_le_two (ofCovering f))
    (Nat.le_of_dvd Nat.card_pos hd)

/-- I.1.3(1): the multiplier of actual M₁₂ is the cyclic group of order two,
for any chosen universal quasisimple covering. -/
public theorem m12_schurMultiplier
    {L : Type u} [Group L] [Finite L] [IsQuasisimple L]
    (f : Covering L M12) (hf : Covering.IsUniversal.{0, u, 0} f) :
    Nonempty (f.toMonoidHom.ker ≃* Multiplicative (ZMod 2)) :=
  ⟨mulEquivOfPrimeCardEq (m12_universal_kernel_card f hf) (by simp)⟩

/-- Every finite perfect central cover of native M₂₄ has trivial kernel. -/
public theorem m24_cover_kernel_eq_bot
    {E : Type*} [Group E] [Finite E] (f : Cover E M24) :
    f.toMonoidHom.ker = ⊥ := by
  let : Group.IsPerfect E := f.isPerfect
  exact Subgroup.card_eq_one.mp
    ((m24_cover_kernel_isTwoGroup f).card_eq_or_dvd.resolve_right
      (m24_cover_kernel_not_two f))

/-- The exact trivial multiplier of M₂₄. As for M₁₁ and M₂₃, universality
is unnecessary: every finite quasisimple covering has trivial kernel. -/
public theorem m24_schurMultiplier
    {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    (f : Covering L M24) :
    Nonempty (f.toMonoidHom.ker ≃* Multiplicative (ZMod 1)) := by
  have hk : f.toMonoidHom.ker = ⊥ := m24_cover_kernel_eq_bot (ofCovering f)
  have : Subsingleton f.toMonoidHom.ker := by
    rw [hk]
    infer_instance
  let : Unique f.toMonoidHom.ker := ⟨⟨1⟩, fun x => Subsingleton.elim _ _⟩
  let : Unique (Multiplicative (ZMod 1)) := ⟨⟨1⟩, fun x => Subsingleton.elim _ _⟩
  exact ⟨MulEquiv.ofUnique⟩

/-- The I.1.1 perfect-central-cover convention gives the same M₁₂ multiplier. -/
public theorem m12_perfectCover_schurMultiplier
    {L : Type u} [Group L] [Finite L]
    (f : Cover L M12) (hf : PerfectCentralCovering.IsUniversal.{u, 0, 0} f) :
    Nonempty (f.toMonoidHom.ker ≃* Multiplicative (ZMod 2)) := by
  let : IsQuasisimple L := f.isQuasisimple
  exact m12_schurMultiplier f.toCovering (PerfectCentralCovering.IsUniversal.toCovering f hf)

/-- The constructed M₁₁ universal projection has the trivial multiplier. -/
public theorem m11_universalProjection_schurMultiplier :
    Nonempty ((universalProjection M11).ker ≃* Multiplicative (ZMod 1)) :=
  m11_schurMultiplier (universalQuasisimpleCover M11)

/-- The constructed M₁₂ universal projection has multiplier C₂. -/
public theorem m12_universalProjection_schurMultiplier :
    Nonempty ((universalProjection M12).ker ≃* Multiplicative (ZMod 2)) :=
  m12_schurMultiplier (universalQuasisimpleCover M12)
    (universalQuasisimpleCover_isUniversal M12)

/-- The constructed M₂₃ universal projection has the trivial multiplier. -/
public theorem m23_universalProjection_schurMultiplier :
    Nonempty ((universalProjection M23).ker ≃* Multiplicative (ZMod 1)) :=
  m23_schurMultiplier (universalQuasisimpleCover M23)

/-- The constructed M₂₄ universal projection has the trivial multiplier. -/
public theorem m24_universalProjection_schurMultiplier :
    Nonempty ((universalProjection M24).ker ≃* Multiplicative (ZMod 1)) :=
  m24_schurMultiplier (universalQuasisimpleCover M24)

end SchurMultipliers

end Sporadic.Mathieu
