module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl.Basic
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl.DiagramFixed.Tables

/-!
# The exact diagram-fixed D₄ Weyl group

The centralizer of the literal triality permutation inside the subgroup generated
by the four literal D₄ root reflections is dihedral of order twelve. Its two
simple reflections are the product of the three arm reflections and the central
reflection. The equivalence uses exactly the root words published in `Weyl.Basic`.

For exhaustive coverage, induction on the generated Weyl group proves preservation
of the dot product and of the relation that two roots use the same coordinate
axes. A diagram-fixed element is determined by its images of the first arm and
the central simple root: triality supplies the other two simple-root images,
and pairings with the simple roots separate all roots. The checked finite table
of admissible image pairs has exactly the twelve published folded words.
The same-axis invariant excludes the additional outer diagram automorphisms.

This realizes the centralizer convention of GLS3 §2.3.1 and the D₄-to-G₂ folding
of §§2.3.2–3 and 2.4.4 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section

open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.PositiveCoordinates.SumExchangeData

namespace Triality.Standard.ConcreteBruhat
open DiagramFixed Parabolics
noncomputable section

private def numbering : Equiv.Perm (TypeDRootIndex 4) ≃* Equiv.Perm (Fin 24) :=
  rootEnumeration.symm.permCongrHom

private lemma numbering_reflection (i : Fin 4) : numbering (rootReflection i) = reflection i := by
  apply Equiv.ext
  intro r
  change rootEnumeration.symm (rootReflection i (rootEnumeration r)) = reflectionTable i r
  rw [rootReflection, ← rootEnumeration_reflectionTable, Equiv.symm_apply_apply]

private lemma numbering_diagram : numbering typeD4DiagramEquiv.indexEquiv = diagram := by
  apply Equiv.ext
  intro r
  change rootEnumeration.symm (typeD4DiagramEquiv.indexEquiv (rootEnumeration r)) = diagram r
  rw [← rootEnumeration_diagram, Equiv.symm_apply_apply]

/-- The faithful action of the literal Weyl group in the checked root enumeration. -/
private def numberedRootWeyl : rootWeylGroup →* Equiv.Perm (Fin 24) :=
  numbering.toMonoidHom.comp rootWeylGroup.subtype

private lemma numberedRootWeyl_injective : Function.Injective numberedRootWeyl :=
  numbering.injective.comp Subtype.val_injective

private lemma numberedRootWeyl_generator (i : Fin 4) :
    numberedRootWeyl (rootWeylGenerator i) = reflection i := numbering_reflection i

private lemma numberedRootWeyl_representative (x : DihedralGroup 6) :
    numberedRootWeyl (rootRepresentative x) = representative x := by
  cases x <;>
    simp [rootRepresentative, representative, foldedRootReflection, map_mul, map_pow,
      numberedRootWeyl_generator, arm]

private lemma numberedRootWeyl_scalar (w : rootWeylGroup) (r s : Fin 24) :
    scalar (numberedRootWeyl w r) (numberedRootWeyl w s) = scalar r s := by
  have h (g : Equiv.Perm (TypeDRootIndex 4)) (hg : g ∈ rootWeylGroup) :
      ∀ r s, scalar (numbering g r) (numbering g s) = scalar r s := by
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨i, rfl⟩ := hg
      simpa only [numbering_reflection] using reflection_scalar i
    | one => simp
    | mul g h _ _ hg hh =>
      intro r s
      simp only [map_mul, Equiv.Perm.mul_apply, hg, hh]
    | inv g _ hg =>
      intro r s
      have h := hg ((numbering g)⁻¹ r) ((numbering g)⁻¹ s)
      simpa using h.symm
  exact h w.val w.property r s

private lemma numberedRootWeyl_sameAxes (w : rootWeylGroup) (r s : Fin 24) :
    sameAxes (numberedRootWeyl w r) (numberedRootWeyl w s) ↔ sameAxes r s := by
  have h (g : Equiv.Perm (TypeDRootIndex 4)) (hg : g ∈ rootWeylGroup) :
      ∀ r s, sameAxes (numbering g r) (numbering g s) ↔ sameAxes r s := by
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨i, rfl⟩ := hg
      simpa only [numbering_reflection] using reflection_sameAxes i
    | one => simp
    | mul g h _ _ hg hh =>
      intro r s
      simp only [map_mul, Equiv.Perm.mul_apply, hg, hh]
    | inv g _ hg =>
      intro r s
      have h := hg ((numbering g)⁻¹ r) ((numbering g)⁻¹ s)
      simpa using h.symm
  exact h w.val w.property r s

/-- Multiplicativity of the original, unchanged root-word function. -/
lemma rootRepresentative_mul (x y : DihedralGroup 6) :
    rootRepresentative (x * y) = rootRepresentative x * rootRepresentative y := by
  apply numberedRootWeyl_injective
  simp only [map_mul, numberedRootWeyl_representative, representative_mul]

/-- The twelve original root words are distinct in the literal Weyl group. -/
lemma rootRepresentative_injective : Function.Injective rootRepresentative := by
  intro x y h
  apply representative_injective
  simpa only [numberedRootWeyl_representative] using congrArg numberedRootWeyl h

/-- Every published root word centralizes the actual triality root permutation. -/
lemma rootRepresentative_fixed (x : DihedralGroup 6) :
    rootRepresentative x ∈ fixedRootWeylSubgroup := by
  rw [mem_fixedRootWeylSubgroup]
  apply numbering.injective
  simpa only [map_mul, numbering_diagram,
    ← show ∀ w : rootWeylGroup, numberedRootWeyl w = numbering w.val from fun _ => rfl,
    numberedRootWeyl_representative] using representative_commutes x

private lemma numberedRootWeyl_ext {u v : rootWeylGroup}
    (h : ∀ i : Fin 4, numberedRootWeyl u (simpleIndex i) =
      numberedRootWeyl v (simpleIndex i)) : u = v := by
  apply numberedRootWeyl_injective
  apply Equiv.ext
  intro r
  apply (numberedRootWeyl v).symm.injective
  simp only [Equiv.symm_apply_apply]
  apply scalar_separates
  intro i
  calc
    scalar ((numberedRootWeyl v).symm (numberedRootWeyl u r)) (simpleIndex i) =
        scalar (numberedRootWeyl u r) (numberedRootWeyl v (simpleIndex i)) := by
      rw [← numberedRootWeyl_scalar v, Equiv.apply_symm_apply]
    _ = scalar r (simpleIndex i) := by rw [← h, numberedRootWeyl_scalar]

private lemma numberedRootWeyl_fixed {w : rootWeylGroup} (hw : w ∈ fixedRootWeylSubgroup)
    (r : Fin 24) : diagram (numberedRootWeyl w r) = numberedRootWeyl w (diagram r) := by
  have h := congrArg numbering ((mem_fixedRootWeylSubgroup w).mp hw)
  simp only [map_mul, numbering_diagram] at h
  exact Equiv.congr_fun h r

private lemma fixedRootWeyl_ext {u v : rootWeylGroup}
    (hu : u ∈ fixedRootWeylSubgroup) (hv : v ∈ fixedRootWeylSubgroup)
    (h0 : numberedRootWeyl u (simpleIndex 0) = numberedRootWeyl v (simpleIndex 0))
    (h1 : numberedRootWeyl u (simpleIndex 1) = numberedRootWeyl v (simpleIndex 1)) : u = v := by
  apply numberedRootWeyl_ext
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · change numberedRootWeyl u (diagram (simpleIndex 0)) =
      numberedRootWeyl v (diagram (simpleIndex 0))
    rw [← numberedRootWeyl_fixed hu, ← numberedRootWeyl_fixed hv, h0]
  · change numberedRootWeyl u (diagram (diagram (simpleIndex 0))) =
      numberedRootWeyl v (diagram (diagram (simpleIndex 0)))
    rw [← numberedRootWeyl_fixed hu, ← numberedRootWeyl_fixed hv,
      ← numberedRootWeyl_fixed hu, ← numberedRootWeyl_fixed hv, h0]

/-- Every element of the actual diagram centralizer is one of the published root words. -/
lemma rootRepresentative_surjective_fixed (w : fixedRootWeylSubgroup) :
    ∃ x : DihedralGroup 6, rootRepresentative x = w.val := by
  let f := numberedRootWeyl w.val
  have comm := numberedRootWeyl_fixed w.property
  have hb : diagram (f (simpleIndex 1)) = f (simpleIndex 1) := comm (simpleIndex 1)
  have hab : scalar (f (simpleIndex 0)) (f (simpleIndex 1)) = -1 :=
    (numberedRootWeyl_scalar w.val _ _).trans (by decide +kernel)
  have ha : scalar (f (simpleIndex 0)) (diagram (f (simpleIndex 0))) = 0 := by
    rw [comm]
    exact (numberedRootWeyl_scalar w.val _ _).trans (by decide +kernel)
  have hs : sameAxes (diagram (f (simpleIndex 0)))
      (diagram (diagram (f (simpleIndex 0)))) := by
    rw [comm, comm]
    exact (numberedRootWeyl_sameAxes w.val _ _).mpr (by decide +kernel)
  obtain ⟨x, hx0, hx1⟩ := pair_coverage _ _ hb hab ha hs
  refine ⟨x, fixedRootWeyl_ext (rootRepresentative_fixed x) w.property ?_ ?_⟩
  · simpa only [numberedRootWeyl_representative] using hx0
  · simpa only [numberedRootWeyl_representative] using hx1


@[simp] lemma rootRepresentative_one : rootRepresentative 1 = 1 := by
  rfl

/-- The published root words form a faithful homomorphism. -/
def rootRepresentativeHom : DihedralGroup 6 →* rootWeylGroup where
  toFun := rootRepresentative
  map_one' := rootRepresentative_one
  map_mul' := rootRepresentative_mul

/-- The Weyl group of the folded G₂ system is the entire diagram centralizer. -/
def rootDihedralEquiv : DihedralGroup 6 ≃* fixedRootWeylSubgroup :=
  MulEquiv.ofBijective
    (rootRepresentativeHom.codRestrict fixedRootWeylSubgroup rootRepresentative_fixed)
    ⟨fun _ _ h => rootRepresentative_injective (congrArg Subtype.val h), by
      intro w
      obtain ⟨x, hx⟩ := rootRepresentative_surjective_fixed w
      exact ⟨x, Subtype.ext hx⟩⟩

@[simp] lemma rootDihedralEquiv_val (x : DihedralGroup 6) :
    (rootDihedralEquiv x).val = rootRepresentative x := rfl

@[simp] lemma rootRepresentative_sr_zero :
    rootRepresentative (.sr 0) = foldedRootReflection .arms := by
  simp [rootRepresentative]

@[simp] lemma rootRepresentative_sr_one :
    rootRepresentative (.sr 1) = foldedRootReflection .central := by
  apply numberedRootWeyl_injective
  rw [numberedRootWeyl_representative]
  rw [foldedRootReflection, numberedRootWeyl_generator]
  decide +kernel

@[simp] lemma rootRepresentative_simple (a : Node) :
    rootRepresentative (relativeReflection a) = foldedRootReflection a := by
  cases a
  · exact rootRepresentative_sr_zero
  · exact rootRepresentative_sr_one

@[simp] lemma rootDihedralEquiv_sr_zero :
    (rootDihedralEquiv (.sr 0)).val = foldedRootReflection .arms := rootRepresentative_sr_zero

@[simp] lemma rootDihedralEquiv_sr_one :
    (rootDihedralEquiv (.sr 1)).val = foldedRootReflection .central := rootRepresentative_sr_one

/-- The product of the arm and central reflections has order six. -/
lemma foldedRootReflection_mul_orderOf :
    orderOf (foldedRootReflection .arms * foldedRootReflection .central) = 6 := by
  have h : rootRepresentativeHom (.r 1) =
      foldedRootReflection .arms * foldedRootReflection .central := by
    change rootRepresentative (.r 1) = _
    change (_ : rootWeylGroup) ^ 1 = _
    exact pow_one _
  rw [← h, orderOf_injective rootRepresentativeHom rootRepresentative_injective,
    DihedralGroup.orderOf_r_one]

/-- The entire diagram-fixed Weyl subgroup has twelve elements. -/
lemma fixedRootWeylSubgroup_card : Nat.card fixedRootWeylSubgroup = 12 := by
  rw [← Nat.card_congr rootDihedralEquiv.toEquiv, DihedralGroup.nat_card]

end
end Triality.Standard.ConcreteBruhat
