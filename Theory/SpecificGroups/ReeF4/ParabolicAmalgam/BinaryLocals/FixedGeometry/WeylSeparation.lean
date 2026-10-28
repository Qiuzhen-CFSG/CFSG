module
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.WeylLifts
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.WeylSeparation.PositiveGeometry
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.WeylSeparation.RootAction
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.WeylSeparation.RootFaithfulness
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.WeylSeparation.SimpleWitnesses
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates.MatrixRelations

/-!
# Separation of fixed Weyl representatives by positive coordinates

A normalizing Weyl representative must carry every detected simple-root
coordinate to a positive root. The reason is elementary matrix geometry:
positive elements send Cartan vectors into the nonnegative-root space, while
Weyl representatives preserve the Cartan space and permute the root rows.
Minimal Weyl-word length then forces the Weyl action to be trivial, and
faithfulness on the actual root vectors makes the representative itself one.

The actual mixed-root commutation and B₂ swap relations construct fixed positive
elements detecting all four simple-root coordinates. Discharging these matrix
relations gives unconditional separation in the full group `Model 0`:
`weyl_normalizer_eq_one` makes every normalizing Weyl representative one, and
`weyl_mem_unipotent` supplies the exact separation premise of
`FixedGeometry.unipotent_index_odd_of_bruhat`. No Bruhat coverage, odd index,
Sylow maximality or simplicity is assumed.

Source: the positive-chamber argument in the Chevalley construction;
Aschbacher–Smith F.1.12(I)(5) and the full ²F₄(2) case,
`refs/quasithin.pdf`, printed pp.263–264.
-/

public section
noncomputable section
namespace ReeF4.Parabolics.Binary.FixedGeometry.WeylSeparation
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped Matrix

private theorem weyl_eq_one_of_simple_positive (w : typeF4RootPairing.weylGroup)
    (hp : ∀ i : typeF4RootPairing_base.support,
      typeF4RootPairing_base.IsPos (typeF4RootPairing.weylGroupToPerm w i)) : w = 1 := by
  let b := typeF4RootPairing_base
  obtain ⟨l, hlen, hprod⟩ := b.wordLength_spec w
  by_cases hl : l = []
  · subst l
    simpa using hprod.symm
  · let j := l.getLast hl
    let p := l.dropLast
    have he : p ++ [j] = l := List.dropLast_append_getLast hl
    have hw : w * b.simpleReflection j = b.wordProd p := by
      rw [← hprod, ← he, b.wordProd_append]
      change (b.wordProd p * b.simpleReflection j) * b.simpleReflection j = _
      rw [mul_assoc, b.simpleReflection_mul_self, mul_one]
    have hbound := b.wordLength_le (w * b.simpleReflection j) p hw.symm
    have hinc := b.wordLength_mul_simpleReflection_of_isPos w j (hp j)
    have hlens : p.length + 1 = l.length := by rw [← he]; simp
    omega

private theorem RootAction.cartan {n : Model 0} {w : typeF4RootPairing.weylGroup}
    (h : RootAction n w) (v : F4Chevalley.BasisIndex → CoefficientField 0)
    (hv : CartanSupported v) : CartanSupported (matrix n *ᵥ v) := by
  intro r
  obtain ⟨s, rfl⟩ := (typeF4RootPairing.weylGroupToPerm w).surjective r
  rw [h.onCoordinate]
  exact hv s

/-- Simple-root coordinate witnesses force a normalizing Weyl representative to be one. -/
theorem weyl_normalizer_eq_one_of_simpleCoordinates
    (hdet : SimpleCoordinateWitnesses) (n : Model 0) (hn : n ∈ weylSubgroup 0)
    (hN : n ∈ Subgroup.normalizer (unipotent 0 : Set (Model 0))) : n = 1 := by
  obtain ⟨w, hw⟩ := exists_rootAction n hn
  have hw1 : w = 1 := by
    apply weyl_eq_one_of_simple_positive
    intro i
    obtain ⟨k, rfl⟩ := typeF4RootPairing_baseEquiv.surjective i
    obtain ⟨x, hx, j, hj⟩ := hdet k
    let c : F4Chevalley.BasisIndex → CoefficientField 0 := Pi.single (Sum.inl j) 1
    have hc : CartanSupported c := by intro r; simp [c]
    have hxc : n * x * n⁻¹ ∈ unipotent 0 :=
      (Subgroup.mem_normalizer_iff.mp hN x).mp hx
    have hpos := unipotent_cartan_positive (n * x * n⁻¹) hxc
      (matrix n *ᵥ c) (hw.cartan c hc)
    by_contra hneg
    have hz := hpos (typeF4RootPairing.weylGroupToPerm w (typeF4SimpleRootIndex k)) hneg
    have he : matrix (n * x * n⁻¹) *ᵥ (matrix n *ᵥ c) =
        matrix n *ᵥ (matrix x *ᵥ c) := by
      rw [Matrix.mulVec_mulVec, ← map_mul]
      simp only [mul_assoc, inv_mul_cancel, mul_one, map_mul, Matrix.mulVec_mulVec]
    rw [he, hw.onCoordinate] at hz
    exact hj (by simpa only [c, Matrix.mulVec_single_one, Matrix.col_apply] using hz)
  apply eq_one_of_fixes_roots
  intro r
  simpa only [hw1, map_one, Equiv.Perm.one_apply] using hw.onRoot r

/-- The precise separation premise for the binary Bruhat assembly, conditional
only on construction of the concrete simple-root coordinate witnesses. -/
theorem weyl_mem_unipotent_of_simpleCoordinates (hdet : SimpleCoordinateWitnesses) :
    ∀ n ∈ weylSubgroup 0,
      n ∈ Subgroup.normalizer (unipotent 0 : Set (Model 0)) → n ∈ unipotent 0 := by
  intro n hn hN
  rw [weyl_normalizer_eq_one_of_simpleCoordinates hdet n hn hN]
  exact (unipotent 0).one_mem

/-- The actual binary fixed positive subgroup detects every simple-root coordinate. -/
theorem simpleCoordinateWitnesses : SimpleCoordinateWitnesses :=
  simpleCoordinateWitnesses_of_blockRelations
    (RadicalCoordinates.FixedCoordinates.mixedRootCommutation 0)
    (RadicalCoordinates.FixedCoordinates.b2RootSwap 0)

/-- In the full binary Ree group, a fixed Weyl representative normalizing the
positive subgroup is the identity. -/
theorem weyl_normalizer_eq_one (n : Model 0) (hn : n ∈ weylSubgroup 0)
    (hN : n ∈ Subgroup.normalizer (unipotent 0 : Set (Model 0))) : n = 1 :=
  weyl_normalizer_eq_one_of_simpleCoordinates simpleCoordinateWitnesses n hn hN

/-- Unconditional Weyl separation: the precise normalizer premise required by
`FixedGeometry.unipotent_index_odd_of_bruhat`. -/
theorem weyl_mem_unipotent :
    ∀ n ∈ weylSubgroup 0,
      n ∈ Subgroup.normalizer (unipotent 0 : Set (Model 0)) → n ∈ unipotent 0 :=
  weyl_mem_unipotent_of_simpleCoordinates simpleCoordinateWitnesses

end ReeF4.Parabolics.Binary.FixedGeometry.WeylSeparation
