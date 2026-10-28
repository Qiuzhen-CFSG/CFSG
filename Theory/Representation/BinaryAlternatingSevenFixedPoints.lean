module

public import Theory.SpecificGroups.AlternatingSevenThreeCycleKleinFour
public import Theory.LinearAlgebra.BinaryFourCubicCentralizer
public import Theory.LinearAlgebra.BinaryFourCubicNormalForm
public import Mathlib.RepresentationTheory.Basic

/-!
# Three-cycle fixed points in faithful binary A₇ representations

A three-cycle centralizes a Klein four subgroup on its four unused letters.
Faithfulness preserves these distinct commuting involutions. If its matrix
has a fixed plane and an irreducible cubic plane, the binary matrix
centralizer calculation contradicts those involutions.

The cubic normal-form theorem shows that every nonidentity cubic operator on
a binary four-space with a nonzero fixed vector has this two-plane form.
Combining it with the centralizer obstruction proves that every three-cycle
acts without nonzero fixed vectors in every faithful four-dimensional binary
representation of A₇, without choosing a particular model. The conditional
reduction is also retained as a separate interface.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma I.1.6(8), printed p.408/PDF p.419. That source statement concerns
cohomology vanishing; this module supplies its fixed-point input.
-/

namespace Representation

/-- The cubic normal-form theorem implies the three-cycle fixed-point claim
for every faithful binary representation of A₇. -/
public theorem binaryAlternatingSeven_threeCycle_fixedPointFree_of_normalForm
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V)
    (hρ : Function.Injective ρ)
    (hnormal : ∀ t : Module.End (ZMod 2) V, t ^ 3 = 1 → t ≠ 1 →
      (∃ v : V, v ≠ 0 ∧ t v = v) →
      ∃ basis : Module.Basis (Fin 4) (ZMod 2) V,
        LinearMap.toMatrix basis basis t = BinaryFourCubic.fixedPlaneMatrix) :
    ∀ a : alternatingGroup (Fin 7),
      Equiv.Perm.IsThreeCycle (a : Equiv.Perm (Fin 7)) →
      ∀ v : V, ρ a v = v → v = 0 := by
  intro a ha v hv
  by_contra hvne
  have ha3 : a ^ 3 = 1 := by
    apply Subtype.ext
    change (a : Equiv.Perm (Fin 7)) ^ 3 = 1
    rw [← ha.orderOf]
    exact pow_orderOf_eq_one _
  have ht3 : ρ a ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
  have htne : ρ a ≠ 1 := by
    intro h
    have he : a = 1 := hρ (h.trans ρ.map_one.symm)
    exact ha.ne_one (congrArg Subtype.val he)
  obtain ⟨basis, hbasis⟩ := hnormal (ρ a) ht3 htne ⟨v, hvne, hv⟩
  obtain ⟨b, c, hb2, hc2, hbne, hcne, hbcne, hab, hac, hbc⟩ :=
    alternatingGroup.threeCycle_exists_commuting_involutions a ha
  let m := LinearMap.toMatrixAlgEquiv basis
  let f := m.toMonoidHom.comp ρ
  have hfinj : Function.Injective f := m.injective.comp hρ
  have hfa : f a = BinaryFourCubic.fixedPlaneMatrix := hbasis
  have hfb2 : f b ^ 2 = 1 := by rw [← map_pow, hb2, map_one]
  have hfc2 : f c ^ 2 = 1 := by rw [← map_pow, hc2, map_one]
  have hba : f b * BinaryFourCubic.fixedPlaneMatrix =
      BinaryFourCubic.fixedPlaneMatrix * f b := by
    rw [← hfa]
    exact (hab.map f).eq.symm
  have hca : f c * BinaryFourCubic.fixedPlaneMatrix =
      BinaryFourCubic.fixedPlaneMatrix * f c := by
    rw [← hfa]
    exact (hac.map f).eq.symm
  rcases BinaryFourCubic.commuting_involutions (f b) (f c) hba hca hfb2 hfc2
      (hbc.map f).eq with h | h | h
  · exact hbne (hfinj (h.trans f.map_one.symm))
  · exact hcne (hfinj (h.trans f.map_one.symm))
  · exact hbcne (hfinj h)

/-- Every three-cycle acts without nonzero fixed vectors in every faithful
four-dimensional binary representation of A₇. -/
public theorem binaryAlternatingSeven_threeCycle_fixedPointFree
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V)
    (hρ : Function.Injective ρ) (hdim : Module.finrank (ZMod 2) V = 4) :
    ∀ a : alternatingGroup (Fin 7),
      Equiv.Perm.IsThreeCycle (a : Equiv.Perm (Fin 7)) →
      ∀ v : V, ρ a v = v → v = 0 :=
  binaryAlternatingSeven_threeCycle_fixedPointFree_of_normalForm ρ hρ
    (BinaryFourCubic.exists_basis_fixedPlaneMatrix hdim)

end Representation
