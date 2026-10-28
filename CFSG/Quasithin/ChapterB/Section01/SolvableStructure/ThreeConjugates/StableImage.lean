module
public import Theory.Representation.BinaryOffender.Restriction
public import Theory.Representation.BinaryOffender.Stability

/-!
# Stable families on an invariant subspace

The nontrivial action images of a stable family form a stable family, provided
its members preserve the subspace and at least one acts nontrivially. Conjugacy
is transported through the surjective action homomorphism. For equal-weight
descent, lift an image subgroup to a subgroup containing the pointwise kernel;
the restriction weight equality then gives equal weight before restriction.

This supplies the stability step for `P⁺` in Aschbacher–Smith B.1.12, printed
p. 73 (PDF p. 84), using the proved restriction comparison of B.7.1. It uses
the original notion of stability, with no assumption that a stable family
equals its saturation.
-/

@[expose] public section
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (W : Submodule (ZMod 2) V)

/-- Conjugating a subgroup and restricting its action commute. -/
theorem restrictedSubgroup_conj (A : Subgroup G)
    (hA : A ≤ subspaceStabilizer ρ W) (g : subspaceStabilizer ρ W) :
    restrictedSubgroup ρ W (A.map (MulAut.conj (g : G)).toMonoidHom) =
      (restrictedSubgroup ρ W A).map
        (MulAut.conj (subspaceActionHom ρ W g)).toMonoidHom := by
  let f := subspaceActionHom ρ W
  ext x
  constructor
  · rintro ⟨b, ⟨a, ha, hab⟩, rfl⟩
    let aS : subspaceStabilizer ρ W := ⟨a, hA ha⟩
    have hb : b = g * aS * g⁻¹ := Subtype.ext hab.symm
    refine ⟨f aS, ⟨aS, ha, rfl⟩, ?_⟩
    rw [hb]
    change f g * f aS * (f g)⁻¹ = f (g * aS * g⁻¹)
    simp only [map_mul, map_inv]
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨g * a * g⁻¹, ⟨(a : G), ha, rfl⟩, ?_⟩
    change f (g * a * g⁻¹) = f g * f a * (f g)⁻¹
    simp only [map_mul, map_inv]

/-- The nontrivial images of members of a family on an invariant subspace. -/
def restrictedFamily (P : Set (Subgroup G)) : Set (Subgroup (subspaceActionImage ρ W)) :=
  {D | D ≠ ⊥ ∧ ∃ A ∈ P, restrictedSubgroup ρ W A = D}

variable [Finite G] [FiniteDimensional (ZMod 2) V]

/-- Stability passes to the nontrivial image family. Equal-weight descent is
lifted through the actual pointwise kernel before invoking source stability. -/
theorem IsStable.restrictedFamily {P : Set (Subgroup G)} (hP : IsStable ρ P)
    (hW : ∀ A ∈ P, A ≤ subspaceStabilizer ρ W)
    (hne : ∃ A ∈ P, ¬ W ≤ fixedSpace ρ A) :
    IsStable (subspaceImageRepresentation ρ W) (restrictedFamily ρ W P) := by
  have hnoncentral (A : Subgroup G) (_hA : A ≤ subspaceStabilizer ρ W)
      (hn : restrictedSubgroup ρ W A ≠ ⊥) : ¬ W ≤ fixedSpace ρ A := by
    intro hfix
    apply hn
    apply le_bot_iff.mp
    rintro x ⟨a, ha, rfl⟩
    apply subspaceImageRepresentation_injective ρ W
    ext w
    exact hfix w.property ⟨a, ha⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨A, hA, hn⟩ := hne
    exact ⟨restrictedSubgroup ρ W A,
      restrictedSubgroup_ne_bot ρ W (hW A hA) hn, A, hA, rfl⟩
  · rintro D ⟨hn, A, hA, rfl⟩
    exact (hP.2.1 A hA).restricted ρ W (hW A hA)
      (hnoncentral A (hW A hA) hn)
  · rintro D ⟨hn, A, hA, rfl⟩ g
    obtain ⟨gS, rfl⟩ := (stabilizerRepresentation ρ W).asGroupHom.rangeRestrict_surjective g
    refine ⟨?_, A.map (MulAut.conj (gS : G)).toMonoidHom,
      hP.2.2.1 A hA gS, restrictedSubgroup_conj ρ W A (hW A hA) gS⟩
    intro hb
    apply hn
    exact Subgroup.map_injective (MulAut.conj (subspaceActionHom ρ W gS)).injective
      (hb.trans (Subgroup.map_bot _).symm)
  · rintro D ⟨hn, A, hA, rfl⟩ E hE hED
    obtain ⟨B, hBA, hKB, hBE⟩ := exists_subgroup_restrictedSubgroup ρ W (hW A hA) E hED.1
    have hBn : B ≠ ⊥ := by
      intro hb
      apply hE.1
      rw [← hBE, hb, restrictedSubgroup_bot]
    have hew : EqualWeightLE ρ B A :=
      ((hP.2.1 A hA).image_weight_eq_iff ρ W (hW A hA) hBA hKB).mp
        (by rw [hBE]; exact hED.2) |>.1
    exact ⟨hE.1, B, hP.2.2.2 A hA B ((hP.2.1 A hA).1.of_le hBA hBn) hew, hBE⟩

end Representation.BinaryOffender
