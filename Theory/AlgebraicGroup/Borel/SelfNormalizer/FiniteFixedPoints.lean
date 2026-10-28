module

public import Theory.AlgebraicGroup.Borel.SelfNormalizer.TorusCommutator
public import Theory.AlgebraicGroup.Borel.SelfNormalizer.FiniteFixedPoints.ChevalleyLine
public import Theory.AlgebraicGroup.Borel.SelfNormalizer.FiniteFixedPoints.NormalBorel

/-!
# Assembly of the finite fixed-torus branch of Borel self-normalization

The normalizer Chevalley line has a regular character, and the finite fixed-torus
calculation proves that the Borel fixes its nonzero vector. Constancy of that
vector orbit forces the full line stabilizer to be `G`, hence makes the Borel
normal. The genuine normal affine quotient and completeness argument then gives
`B = G`.

The complete-space vector-orbit argument remains an explicit hypothesis of
`eq_top_of_finite_fixedPoints_of_vectorOrbit_constancy`; this module does not
yet claim the unconditional finite fixed-torus branch. The orbit map on `G`
is regular and right B-invariant, but regular descent is not inferred from
a point equivalence.

Source: Borel, *Linear Algebraic Groups*, Theorem 11.16(iii),
`refs/KGroup/Bor1/Chapter4.tex`, line 229.
-/

universe u
namespace Theory.AlgebraicGroup.BorelSelfNormalizer

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

omit [IsAlgClosed k] in
/-- A constant Chevalley vector orbit forces its full line stabilizer to be `G`. -/
public theorem normalizer_eq_top_of_chevalleyOrbit_constant (B : ClosedSubgroup G)
    (hconstant : ∀ g : Variety.Point G,
      (normalizerChevalleyOrbitMorphism B).toFun g =
        (normalizerChevalleyOrbitMorphism B).toFun 1) :
    B.normalizer = ClosedSubgroup.top := by
  apply SetLike.ext
  intro g
  constructor
  · intro _
    trivial
  · intro _
    apply (normalizerChevalleyLine_stabilizer B g).mp
    have hg := (normalizerChevalleyOrbitMorphism_eq_iff B g 1).mp (hconstant g)
    simp only [map_one, Units.val_one, Module.End.one_apply] at hg
    rw [hg]
    exact Submodule.mem_span_singleton_self _

/-- Complete the source's `G = N_G(B)` to `B = G` tail after vector-orbit constancy. -/
public theorem eq_top_of_chevalleyOrbit_constant
    (hG : Variety.IsConnected G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (hconstant : ∀ g : Variety.Point G,
      (normalizerChevalleyOrbitMorphism B).toFun g =
        (normalizerChevalleyOrbitMorphism B).toFun 1) :
    B = ClosedSubgroup.top := by
  apply borel_eq_top_of_normal hG B hB
  apply Subgroup.normalizer_eq_top_iff.mp
  change B.normalizer.toSubgroup = ⊤
  rw [normalizer_eq_top_of_chevalleyOrbit_constant B hconstant]
  rfl

/-- Conditional finite-fixed assembly. The sole remaining geometric input says
that a B-fixed vector in this rational representation is G-fixed. It is a
separate complete-homogeneous-space theorem, not part of the Borel hypotheses. -/
public theorem eq_top_of_finite_fixedPoints_of_vectorOrbit_constancy
    (hG : Variety.IsConnected G)
    (B T : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (hT : IsMaximalTorus T) (hTB : T ≤ B)
    (n : Variety.Point G) (hnB : n ∈ B.normalizer.toSubgroup)
    (hnT : n ∈ T.normalizer.toSubgroup) (hfixed : (fixedTorusPoints T n).Finite)
    (hgeometry : ∀ d : NormalizerChevalleySpace B,
      (∀ b : Variety.Point G, b ∈ B.toSubgroup →
        ((normalizerChevalleyRepresentation B).action b).1 d = d) →
      ∀ g : Variety.Point G, ((normalizerChevalleyRepresentation B).action g).1 d = d) :
    B = ClosedSubgroup.top := by
  have hfixedB := normalizerChevalleyVector_fixed_by_borel B T hB hT hTB n hnB hnT hfixed
  have hfixedG := hgeometry (normalizerChevalleyVector B) hfixedB
  apply eq_top_of_chevalleyOrbit_constant hG B hB
  intro g
  apply (normalizerChevalleyOrbitMorphism_eq_iff B g 1).mpr
  rw [hfixedG g, hfixedG 1]

end Theory.AlgebraicGroup.BorelSelfNormalizer
