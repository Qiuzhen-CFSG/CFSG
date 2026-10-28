module

public import Theory.AlgebraicGroup.Borel.ElementCoverage.Defs
public import Theory.AlgebraicGroup.Dimension.Fiber
import all Theory.AlgebraicGroup.Dimension.Fiber

/-!
# Affine conjugation fibres and fixed homogeneous-space points

The conjugation morphism `G × H → G` has the conjugacy saturation as its image.
A finite fixed-point set on the genuine Plücker homogeneous space covers any
one conjugation fibre by finitely many closed coset slices. An irreducible
closed subset of the fibre lies in one slice. Its first coordinate, translated
back into `H`, has a polynomial inverse on that subset, so its polynomial
functions are quotients of those on `H` and its dimension is at most `dim H`.

Source: Borel, *Linear Algebraic Groups*, §11.9(2),
`refs/KGroup/Bor1/Chapter4.tex`. This is the affine counterpart of the incidence
variety in the source proof; no completeness or separability is used.
-/

namespace Theory.AlgebraicGroup.BorelElementCoverage

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- The regular map `(g, a) ↦ g a g⁻¹`, with `a` in the closed subgroup. -/
@[expose] public def subgroupConjugation (H : ClosedSubgroup G) :
    Variety.Morphism (Variety.prod G H.carrierVariety) G :=
  let p := Variety.Morphism.fst G H.carrierVariety
  let q := H.inclusion.toVariety.comp (Variety.Morphism.snd G H.carrierVariety)
  let m := (AlgebraicGroup.mulMorphism G).comp (p.pair q)
  (AlgebraicGroup.mulMorphism G).comp (m.pair ((AlgebraicGroup.invMorphism G).comp p))

omit [IsAlgClosed k] in
public theorem subgroupConjugation_apply (H : ClosedSubgroup G)
    (z : Variety.Point (Variety.prod G H.carrierVariety)) :
    (subgroupConjugation H).toFun z =
      (Variety.prodPointEquiv G H.carrierVariety z).1 *
        H.inclusion.onPoints (Variety.prodPointEquiv G H.carrierVariety z).2 *
          (Variety.prodPointEquiv G H.carrierVariety z).1⁻¹ := by
  simp [subgroupConjugation, Variety.Morphism.comp, Variety.Morphism.pair,
    Variety.Morphism.fst, Variety.Morphism.snd, AlgebraicGroup.mulMorphism,
    AlgebraicGroup.invMorphism, AlgebraicGroup.Morphism.onPoints]

omit [IsAlgClosed k] in
/-- The affine conjugation image is exactly the source union of conjugates. -/
public theorem subgroupConjugation_range (H : ClosedSubgroup G) :
    Set.range (subgroupConjugation H).toFun = conjugacySaturation H := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    let g := (Variety.prodPointEquiv G H.carrierVariety z).1
    let a := (Variety.prodPointEquiv G H.carrierVariety z).2
    refine ⟨g, ?_⟩
    rw [subgroupConjugation_apply]
    change g⁻¹ * (g * H.inclusion.onPoints a * g⁻¹) * g ∈ H.toSubgroup
    have ha : H.inclusion.onPoints a ∈ H.toSubgroup := (H.pointEquiv a).property
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right,
      inv_mul_cancel, mul_one] using ha
  · rintro ⟨g, hg⟩
    let a : Variety.Point H.carrierVariety := H.pointEquiv.symm ⟨g⁻¹ * x * g, hg⟩
    refine ⟨(Variety.prodPointEquiv G H.carrierVariety).symm (g, a), ?_⟩
    rw [subgroupConjugation_apply, Equiv.apply_symm_apply]
    have ha : H.inclusion.onPoints a = g⁻¹ * x * g := by
      change (H.pointEquiv (H.pointEquiv.symm _)).val = _
      simp only [Equiv.apply_symm_apply]
    rw [ha]
    group

private theorem fixed_projection_iff (H : ClosedSubgroup G) (y g : Variety.Point G) :
    y • Bor1.borelHomogeneousSpace.projection H g =
        Bor1.borelHomogeneousSpace.projection H g ↔
      g⁻¹ * y * g ∈ H.toSubgroup := by
  constructor
  · intro h
    exact (H.mem_conjugate_iff g y).mp
      ((Bor1.projectivization_fixed_iff_mem_conjugate H g y).mp
        (congrArg Subtype.val h))
  · intro h
    apply Subtype.ext
    exact (Bor1.projectivization_fixed_iff_mem_conjugate H g y).mpr
      ((H.mem_conjugate_iff g y).mpr h)

/-- Finitely many fixed points mean finitely many cosets `gH` in the
transporter of an element into `H`. Representatives themselves transport it. -/
public theorem finite_fixed_points_coset_cover (H : ClosedSubgroup G) (y : Variety.Point G)
    (hfinite : Set.Finite {q : Bor1.borelHomogeneousSpace H | y • q = q}) :
    ∃ s : Finset (Variety.Point G),
      (∀ g ∈ s, g⁻¹ * y * g ∈ H.toSubgroup) ∧
      ∀ g : Variety.Point G, g⁻¹ * y * g ∈ H.toSubgroup →
        ∃ t ∈ s, t⁻¹ * g ∈ H.toSubgroup := by
  classical
  let F := {q : Bor1.borelHomogeneousSpace H // y • q = q}
  let : Fintype F := hfinite.fintype
  choose r hr using fun q : F => Bor1.borelHomogeneousSpace.projection_surjective H q.val
  refine ⟨Finset.univ.image r, ?_, ?_⟩
  · intro g hg
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hg
    apply (fixed_projection_iff H y (r q)).mp
    rw [hr q]
    exact q.property
  · intro g hg
    let q : F := ⟨Bor1.borelHomogeneousSpace.projection H g,
      (fixed_projection_iff H y g).mpr hg⟩
    refine ⟨r q, Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩, ?_⟩
    obtain ⟨b, hb, hgb⟩ := (Bor1.borelHomogeneousSpace.projection_eq_iff H (r q) g).mp
      (hr q)
    simpa [hgb] using hb

omit [IsAlgClosed k] in
private theorem closedSubset_dimension_le_of_polynomial_retraction
    {V W : Variety k} {S : Set (Variety.Point V)} (hS : IsZariskiClosed V S)
    (hSi : IsIrreducible S)
    (hWi : IsIrreducible (Set.univ : Set (Variety.Point W)))
    (f : Variety.Morphism W V)
    (r : Variety.Morphism (Variety.closedSubvariety hS) W)
    (hfr : ∀ x, f.toFun (r.toFun x) = (Variety.closedSubvarietyPointEquiv hS x).val) :
    Variety.dimension (Variety.closedSubvariety hS) ≤ Variety.dimension W := by
  let e := Variety.closedSubvarietyPointHomeomorph hS
  let : IrreducibleSpace S := Subtype.irreducibleSpace hSi
  let : IrreducibleSpace (Variety.Point (Variety.closedSubvariety hS)) :=
    e.irreducibleSpace_iff.mpr inferInstance
  have hVi := IrreducibleSpace.isIrreducible_univ (Variety.Point (Variety.closedSubvariety hS))
  rw [dimension_eq_trdeg_polynomialFunction_of_isIrreducible _ hVi,
    dimension_eq_trdeg_polynomialFunction_of_isIrreducible _ hWi]
  apply trdeg_le_of_surjective r.pullbackAlgHom
  intro a
  obtain ⟨p, hp⟩ := a.representedBy
  refine ⟨f.pullbackAlgHom (Variety.PolynomialFunction.ofPolynomial V p), ?_⟩
  apply Variety.PolynomialFunction.ext
  intro x
  change evalPolynomial (f.toFun (r.toFun x)).val p = a x
  rw [hfr]
  exact (hp x).symm

/-- Every irreducible closed subset of the chosen conjugation fibre has
 dimension at most that of the connected subgroup. -/
public theorem subgroupConjugation_fiber_dimension_le
    (H : ClosedSubgroup G)
    (hHi : IsIrreducible (Set.univ : Set (Variety.Point H.carrierVariety)))
    (y : Variety.Point G)
    (hfinite : Set.Finite {q : Bor1.borelHomogeneousSpace H | y • q = q})
    (S : Set (Variety.Point (Variety.prod G H.carrierVariety)))
    (hS : IsZariskiClosed (Variety.prod G H.carrierVariety) S)
    (hSi : IsIrreducible S)
    (hSf : S ⊆ {z | (subgroupConjugation H).toFun z = y}) :
    Variety.dimension (Variety.closedSubvariety hS) ≤ Variety.dimension H.carrierVariety := by
  classical
  let V := Variety.prod G H.carrierVariety
  let p := Variety.Morphism.fst G H.carrierVariety
  obtain ⟨s, hstrans, hscover⟩ := finite_fixed_points_coset_cover H y hfinite
  let C (t : Variety.Point G) : Set (Variety.Point V) :=
    {z | t⁻¹ * p.toFun z ∈ H.toSubgroup}
  have hC (t : Variety.Point G) : IsClosed (C t) :=
    Variety.isClosed_iff_isZariskiClosed.mpr
      (((AlgebraicGroup.leftMulMorphism G t⁻¹).comp p).isZariskiClosed_preimage
        H.isZariskiClosed)
  have hcover : S ⊆ ⋃₀ ↑(s.image C) := by
    intro z hz
    have hz' : (subgroupConjugation H).toFun z = y := hSf hz
    rw [subgroupConjugation_apply] at hz'
    have hmem : (p.toFun z)⁻¹ * y * p.toFun z ∈ H.toSubgroup := by
      rw [← hz']
      change ((Variety.prodPointEquiv G H.carrierVariety z).1)⁻¹ *
        ((Variety.prodPointEquiv G H.carrierVariety z).1 *
          H.inclusion.onPoints (Variety.prodPointEquiv G H.carrierVariety z).2 *
            ((Variety.prodPointEquiv G H.carrierVariety z).1)⁻¹) *
              (Variety.prodPointEquiv G H.carrierVariety z).1 ∈ H.toSubgroup
      have hmem : H.inclusion.onPoints (Variety.prodPointEquiv G H.carrierVariety z).2 ∈
          H.toSubgroup := (H.pointEquiv (Variety.prodPointEquiv G H.carrierVariety z).2).property
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right,
        inv_mul_cancel, mul_one] using hmem
    obtain ⟨t, ht, htz⟩ := hscover (p.toFun z) hmem
    exact Set.mem_sUnion.mpr ⟨C t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, htz⟩
  obtain ⟨T, hT, hST⟩ := isIrreducible_iff_sUnion_isClosed.mp hSi (s.image C)
    (by intro T hT; obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hT; exact hC t) hcover
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hT
  let a : Variety.Point H.carrierVariety := H.pointEquiv.symm ⟨t⁻¹ * y * t, hstrans t ht⟩
  have ha : H.inclusion.onPoints a = t⁻¹ * y * t := by
    change (H.pointEquiv (H.pointEquiv.symm _)).val = _
    simp only [Equiv.apply_symm_apply]
  let f : Variety.Morphism H.carrierVariety V :=
    ((AlgebraicGroup.leftMulMorphism G t).comp H.inclusion.toVariety).pair
      (AlgebraicGroup.inverseConjugateMorphism H.carrierVariety a)
  let r : Variety.Morphism (Variety.closedSubvariety hS) H.carrierVariety :=
    ((AlgebraicGroup.leftMulMorphism G t⁻¹).comp p).restrictClosedSubvariety
      hS H.isZariskiClosed (fun z hz => hST hz)
  apply closedSubset_dimension_le_of_polynomial_retraction hS hSi hHi f r
  intro x
  let z := (Variety.closedSubvarietyPointEquiv hS x).val
  have hz : (subgroupConjugation H).toFun z = y :=
    hSf (Variety.closedSubvarietyPointEquiv hS x).property
  have hr : H.inclusion.onPoints (r.toFun x) = t⁻¹ * p.toFun z := by
    exact Variety.Morphism.restrictClosedSubvariety_apply _ _ _ _ x
  apply (Variety.prodPointEquiv G H.carrierVariety).injective
  apply Prod.ext
  · change t * H.inclusion.onPoints (r.toFun x) = p.toFun z
    rw [hr, mul_inv_cancel_left]
  · apply H.inclusion_injective
    change H.inclusion.onPoints
      ((AlgebraicGroup.inverseConjugateMorphism H.carrierVariety a).toFun (r.toFun x)) =
        H.inclusion.onPoints (Variety.prodPointEquiv G H.carrierVariety z).2
    rw [AlgebraicGroup.inverseConjugateMorphism_apply, map_mul, map_mul, map_inv, ha, hr]
    have hz' : (p.toFun z)⁻¹ * y * p.toFun z =
        H.inclusion.onPoints (Variety.prodPointEquiv G H.carrierVariety z).2 := by
      rw [← hz, subgroupConjugation_apply]
      change ((Variety.prodPointEquiv G H.carrierVariety z).1)⁻¹ *
        ((Variety.prodPointEquiv G H.carrierVariety z).1 *
          H.inclusion.onPoints (Variety.prodPointEquiv G H.carrierVariety z).2 *
            ((Variety.prodPointEquiv G H.carrierVariety z).1)⁻¹) *
              (Variety.prodPointEquiv G H.carrierVariety z).1 = _
      group
    rw [← hz']
    group

end Theory.AlgebraicGroup.BorelElementCoverage
