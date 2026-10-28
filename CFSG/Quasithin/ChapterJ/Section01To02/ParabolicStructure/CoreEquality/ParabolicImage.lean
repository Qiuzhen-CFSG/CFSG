module

public import CFSG.Quasithin.ChapterJ.Defs
public import CFSG.Quasithin.ChapterJ.Section01To02.Preliminaries
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.Center
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.Transvections
public import Theory.Representation.PSL3Two.NaturalOrbits
public import Theory.Representation.PSL3Two.FanoLocalStructure.ParabolicSpaces
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.Identification

/-!
# The actual point-parabolic image in J.2.2

The unique nonidentity element of Z(T) gives a nonzero vector in the natural
Ru1 coordinates. Equivariance and injectivity identify L ∩ H with its full
stabilizer preimage under the specified Ru1 quotient map. Transitivity of
SL₃(2) on nonzero vectors then identifies this image with a conjugate of the
standard point parabolic, and hence with S₄. Its literal kernel is S.

The same map is used for the Steinberg action in the core-equality proof;
no independent or incompatible quotient marking is chosen.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.2(1), printed p.432 (PDF p.443).
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ
open Subgroup Representation Matrix.PSL3Two
variable {G : Type*} [Group G] [Finite G]

/-- The literal overlap, with the ordering used to define L₁. -/
abbrev LocalSetup.parabolic (d : LocalSetup G) : Subgroup G := d.L ⊓ d.toTypeRuSetup.H

/-- Restriction of the common Ru1 quotient marking to the overlap. -/
def LocalSetup.parabolicMap (d : LocalSetup G) : d.parabolic →* BinaryLinearThree.Group :=
  d.ru1.quotientMap.comp (inclusion inf_le_left)

/-- The kernel of the restricted Ru1 marking is the original core S. -/
theorem LocalSetup.parabolicMap_kernel (d : LocalSetup G) :
    d.parabolicMap.ker = d.toTypeRuSetup.S.subgroupOf d.parabolic := by
  ext x
  change d.ru1.quotientMap ⟨x, x.property.1⟩ = 1 ↔ (x : G) ∈ d.toTypeRuSetup.S
  change (⟨x, x.property.1⟩ : d.L) ∈ d.ru1.quotientMap.ker ↔ _
  rw [d.ru1.quotient_kernel]
  rfl

/-- The parabolic is the inverse image of a point stabilizer, for the given Ru1 marking. -/
theorem LocalSetup.exists_parabolic_fixed_vector (d : LocalSetup G) :
    ∃ w : BinaryLinearThree.Vector, w ≠ 0 ∧ ∀ l : d.L,
      (l : G) ∈ d.toTypeRuSetup.H ↔
        BinaryLinearThree.W (d.ru1.quotientMap l) w = w := by
  obtain ⟨z, hz, huniq⟩ := (Nat.card_eq_two_iff' (1 : d.toTypeRuSetup.Z)).mp d.card_Z
  have hZV : d.toTypeRuSetup.Z ≤ d.V := d.center_eq.le.trans inf_le_left
  let v : d.V := ⟨z, hZV z.property⟩
  have hi : Function.Injective d.ru1.natural.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [d.ru1.natural.kernel_eq, bot_subgroupOf]
  refine ⟨(d.ru1.natural.coordinates v).toAdd, ?_, ?_⟩
  · intro hw
    have hv : v = 1 := hi (hw.trans d.ru1.natural.coordinates.map_one.symm)
    exact hz (Subtype.ext (congrArg (fun x : d.V => (x : G)) hv))
  · intro l
    have he := d.ru1.natural.equivariant l v
    constructor
    · intro hl
      have hc : (l : G) * z * (l : G)⁻¹ = z := by
        rw [← hl z z.property, mul_inv_cancel_right]
      have heq : (⟨l * v * (l : G)⁻¹, (mem_normalizer_iff.mp (d.ru1.natural.normalized l.property) v).mp v.property⟩ : d.V) = v := Subtype.ext hc
      rw [heq] at he
      exact he.symm
    · intro hl
      have heq := hi (Multiplicative.toAdd.injective (he.trans hl))
      have hc : (l : G) * z * (l : G)⁻¹ = z := congrArg Subtype.val heq
      change ∀ a ∈ d.toTypeRuSetup.Z, a * (l : G) = (l : G) * a
      intro a ha
      by_cases ha1 : a = 1
      · simp [ha1]
      have haz : (⟨a, ha⟩ : d.toTypeRuSetup.Z) = z :=
        huniq ⟨a, ha⟩ (fun h => ha1 (congrArg Subtype.val h))
      have haz' : a = (z : G) := congrArg Subtype.val haz
      rw [haz']
      exact (mul_inv_eq_iff_eq_mul.mp hc).symm

private theorem point_fixed (g : BinaryLinearThree.Group) :
    g ∈ pointParabolicSL ↔ BinaryLinearThree.W g flagPoint.val = flagPoint.val := by
  exact (BinaryLinearThree.FanoLocalStructure.ParabolicSpaces.mem_pointParabolic_iff_fixes_point g).trans
    Subtype.ext_iff

/-- The image of the literal Ru1 map on L ∩ H is a conjugate point parabolic. -/
theorem LocalSetup.parabolic_image (d : LocalSetup G) :
    ∃ g : BinaryLinearThree.Group,
      d.parabolicMap.range = pointParabolicSL.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨w, hw, hfix⟩ := d.exists_parabolic_fixed_vector
  obtain ⟨g, hg⟩ := BinaryLinearThree.natural_transitive_nonzero flagPoint.val w flagPoint.property hw
  refine ⟨g, ?_⟩
  have hconj (a : BinaryLinearThree.Group) :
      BinaryLinearThree.W a w = w ↔ a ∈ pointParabolicSL.map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    constructor
    · intro ha
      refine mem_map.mpr ⟨g⁻¹ * a * g, (point_fixed _).mpr ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      simpa only [map_mul, Module.End.mul_apply, Representation.inv_self_apply] using
        congrArg (BinaryLinearThree.W g⁻¹) ha
    · rintro ⟨b, hb, rfl⟩
      change BinaryLinearThree.W (g * b * g⁻¹) (BinaryLinearThree.W g flagPoint.val) = _
      simp only [map_mul, Module.End.mul_apply, Representation.inv_self_apply,
        (point_fixed b).mp hb]
  ext a
  constructor
  · rintro ⟨l, rfl⟩
    exact (hconj _).mp ((hfix ⟨l, l.property.1⟩).mp l.property.2)
  · intro ha
    obtain ⟨l, rfl⟩ := d.ru1.quotient_surjective a
    exact ⟨⟨l, l.property, (hfix l).mpr ((hconj _).mpr ha)⟩, rfl⟩

/-- The actual parabolic quotient is S₄. -/
def LocalSetup.parabolicImageEquivS4 (d : LocalSetup G) :
    d.parabolicMap.range ≃* Equiv.Perm (Fin 4) := by
  let g := Classical.choose d.parabolic_image
  have hg := Classical.choose_spec d.parabolic_image
  exact (MulEquiv.subgroupCongr hg).trans
    (((MulAut.conj g).subgroupMap pointParabolicSL).symm.trans
      Matrix.PSL3Two.MarkedAutomorphisms.pointEquivSymmetric)

end CFSG.Quasithin.ChapterJ
