module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.Conjugation
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.CharacterPowers

/-!
# Matching actual and concrete opposite F4 root pairs

Each concrete root weight occurs in the actual realization after torus
conjugacy. Distinctness of the concrete weights and equality of the finite
root counts make this correspondence surjective on the actual roots.
Inverse characters identify the corresponding negative roots. Uniqueness
at the concrete weights then identifies both actual closed subgroups with
the conjugated literal pair.

The given root-index equivalence supplies only the cardinality comparison;
no compatibility with the literal root curves or with a chosen base is
assumed. Torus conjugacy and root-weight uniqueness remain geometric inputs.

Source: GLS3 1.9.5(b),(c), `refs/KGroup/GLS3/Chapter1.tex`.
-/

public section
open Theory.AlgebraicGroup.StandardRootSystem
universe u

namespace Theory.AlgebraicGroup.F4Chevalley
variable {k : Type u} [Field k] [IsAlgClosed k]
noncomputable local instance matchingSplitTorusAlgebraicGroup :
    AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
  (splitTorus (k := k)).carrierAlgebraicGroup

/-- Opposite literal F4 roots have inverse characters, in every characteristic. -/
lemma concreteRootWeight_opposite (r : Root) :
    rootWeight (k := k) (typeF4RootPairing.reflectionPerm r r) =
      (rootWeight r)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  apply TorusCharacter.pointCharacter_injective
  ext s
  have hmul (a b : TorusWeight (splitTorus (k := k))) :
      (a * b).pointCharacter s = a.pointCharacter s * b.pointCharacter s := by
    change (dPointEquiv 1 (a.onPoints s * b.onPoints s) 0 : k) = _
    rw [dPointEquiv_mul]
    rfl
  rw [hmul, rootWeight_pointCharacter, rootWeight_pointCharacter]
  change (↑(∏ i, (dPointEquiv 4 ((splitTorusIso (k := k)).inv.onPoints s) i) ^
      torusRootExponent (typeF4RootPairing.reflectionPerm r r) i) : k) *
    (↑(∏ i, (dPointEquiv 4 ((splitTorusIso (k := k)).inv.onPoints s) i) ^
      torusRootExponent r i) : k) = (dPointEquiv (k := k) 1 1 0 : k)
  rw [dPointEquiv_one]
  simp only [Pi.one_apply, Units.val_one]
  have he (i) : torusRootExponent (typeF4RootPairing.reflectionPerm r r) i =
      -torusRootExponent r i := typeF4RootPairing.pairingIn_reflectionPerm_self_left ℤ r _
  simp only [he, zpow_neg, Finset.prod_inv_distrib]
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

end Theory.AlgebraicGroup.F4Chevalley

namespace Theory.AlgebraicGroup.RootGroupData
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Torus conjugacy and uniqueness at the concrete weights match both members
of every actual opposite pair. The equivalence `e` is used only for the root
count; it need not identify any literal curve with an actual subgroup. -/
theorem f4_oppositePair_eq_conjugate
    {T : ClosedSubgroup (F4Chevalley.Carrier (k := k))}
    (D : RootGroupData (F4Chevalley.Carrier (k := k)) T) (hD : D.IsRealization)
    (e : D.Root ≃ F4Chevalley.Root)
    (g : Variety.Point (F4Chevalley.Carrier (k := k)))
    (hT : T = (F4Chevalley.splitTorus (k := k)).conjugate g)
    (hunique : ∀ (r : F4Chevalley.Root) (Y : ClosedSubgroup (F4Chevalley.Carrier (k := k))),
      IsTorusRootSubgroup F4Chevalley.splitTorus Y →
      RootWeightEquation F4Chevalley.splitTorus Y (F4Chevalley.rootWeight r) →
      Y = F4Chevalley.rootSubgroup r)
    (a : D.Root) :
    ∃ r : F4Chevalley.Root,
      D.rootSubgroup a = (F4Chevalley.rootSubgroup r).conjugate g ∧
      D.rootSubgroup (D.neg a) = (F4Chevalley.rootSubgroup
        (typeF4RootPairing.reflectionPerm r r)).conjugate g := by
  subst T
  let S := F4Chevalley.splitTorus (k := k)
  let w := torusWeightConjugateEquiv S g
  have hex (r : F4Chevalley.Root) : ∃ α, D.rootWeight α = w (F4Chevalley.rootWeight r) := by
    have hroot : w (F4Chevalley.rootWeight r) ∈ TorusRootSet (S.conjugate g) :=
      IsTorusRoot.conjugate g ⟨_, (F4Chevalley.rootSubgroup_package r).1,
        (F4Chevalley.rootSubgroup_package r).2⟩
    rwa [← hD.2.1] at hroot
  choose f hf using hex
  have hfinj : Function.Injective f := by
    intro r s h
    apply F4Chevalley.concreteRootWeight_injective (k := k)
    apply w.injective
    rw [← hf r, ← hf s, h]
  have hfsurj : Function.Surjective f := by
    have hsurj := Finite.surjective_of_injective (e.injective.comp hfinj)
    intro α
    obtain ⟨r, hr⟩ := hsurj (e α)
    exact ⟨r, e.injective hr⟩
  have hwInv (χ : TorusWeight S) : w (χ⁻¹) = (w χ)⁻¹ := by
    rfl
  have hfneg (r) : f (typeF4RootPairing.reflectionPerm r r) = D.neg (f r) := by
    apply hD.1
    rw [hf, hD.2.2.2.1, hf, F4Chevalley.concreteRootWeight_opposite, hwInv]
  have hsub (r) : D.rootSubgroup (f r) = (F4Chevalley.rootSubgroup r).conjugate g := by
    obtain ⟨α, hα⟩ := D.exists_rootSubgroup_eq_conjugate_of_unique_weight g hD
      (F4Chevalley.rootSubgroup_package r).1 (F4Chevalley.rootSubgroup_package r).2
      (hunique r)
    have hweight : D.rootWeight α = w (F4Chevalley.rootWeight r) := by
      apply rootWeightEquation_unique (S.conjugate g) (D.rootSubgroup α)
        (hD.2.2.1 α).1.2 (hD.2.2.1 α).2
      rw [hα]
      exact ((F4Chevalley.rootSubgroup_package r).2).conjugate g
    have hαf : α = f r := hD.1 (hweight.trans (hf r).symm)
    rwa [hαf] at hα
  obtain ⟨r, rfl⟩ := hfsurj a
  exact ⟨r, hsub r, by rw [← hfneg]; exact hsub _⟩

end Theory.AlgebraicGroup.RootGroupData
