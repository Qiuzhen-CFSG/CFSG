module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Reorientation.Geometry
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair

/-!
# The two orientations in 13.8.7

The earlier F.9 conclusions are stated uniformly over genuine critical pairs,
as in their source statements. In the reverse asymmetric case F.9.15 detects
a critical neighbor. The constructed geodesic reversal exchanges the literal
denominators, including both stabilizer adjustments. The proved oriented
impossibility can therefore be applied to this newly constructed pair.

`EarlierGeometry` enumerates only F.9.11, F.9.13 and F.9.15 consequences.
The other explicit inputs are precisely those of `no_asymmetric_criticalPair`:
the marked natural geometry of 13.2/13.5, the earlier centralizer bounds,
and the genuine module alternatives in 13.8.5 and 13.7.6. Neither symmetry
nor either asymmetric impossibility is an input.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.7,
printed pp.948–949, and F.9.13–17, printed pp.322–324.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.Reorientation
open AsymmetricPair
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData
variable {G : Type*} [Group G] {L T H V : Subgroup G}

/-- Earlier F.9 statements for one genuine critical pair. Use a uniform
family of these statements when selecting a different pair. -/
structure EarlierGeometry (c : CriticalPair L T H V) (V₃ Z : Subgroup G) : Prop where
  length : 3 ≤ c.path.length
  VH_endpoint : Source.VH H V ≤ vertexGroup L T H c.gamma
  Vgamma_H : c.Vgamma ≤ H
  DH_kernel : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z) =
    Source.UH H V₃ ⊓ c.Qgamma
  Dgamma_kernel : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) Z =
    c.Ugamma V₃ ⊓ Source.QH H
  lines_disjoint : Z ⊓ c.Aone Z = ⊥
  cross_centralizes : ⁅Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z),
    Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) Z⁆ = ⊥
  first_kernel : c.Vgamma ⊓ firstKernel L T H (base L T H true) =
    Source.Egamma c.Vgamma (Source.UH H V₃) Z

variable [Finite G]

/-- The full equivalence of 13.8.7 under H=G₁=C_G(z), with V₁=⟨z⟩.
The reverse critical pair is constructed inside this proof. -/
theorem strict_iff
    {L T H V : Subgroup G} (c : CriticalPair L T H V)
    (V₂ V₃ L₂ M : Subgroup G) (z : V)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 V]
    [IsMulCommutative (Source.VH H V)]
    [((zpowers (z : G)).subgroupOf (Source.UH H V₃)).Normal]
    (Q : CenterQuotientAction H (Source.UH H V₃) (zpowers (z : G)))
    (P : MarkedPlaneAction L₂ T V V₂)
    (hH : H = centralizer ({(z : G)} : Set G))
    (hcard : Nat.card (zpowers (z : G)) = 2)
    (hz : P.moduleEquiv (Additive.ofMul z) = pairVector 4 5)
    (hZ₂ : zpowers (z : G) ≤ V₂) (hZ₃ : zpowers (z : G) ≤ V₃)
    (b : Source.UH H V₃) (hb : (b : G) ∈ V₂) (hbZ : (b : G) ∉ zpowers (z : G))
    (hM : normalizer (zpowers (z : G)) ⊓ normalizer V₃ ≤ M)
    (a : CoverGeometry.NaturalAction M V)
    (f : CoverGeometry.NaturalFlag a T (zpowers (z : G)) V₃)
    (hLV : L ≤ normalizer V)
    (htrans : ∀ x ∈ V, x ≠ 1 → ∃ l ∈ L, MulAut.conj l (z : G) = x)
    (hHC : ⁅Source.VH H V, Source.HC H V₃⁆ ≤ zpowers (z : G))
    (hQ : ⁅Source.QH H, V₃⁆ ≤ zpowers (z : G))
    (hmodels : (∃ t : H, Q.action t ≠ 1 ∧ binaryLinear (Q.action t) ∈
        LinearEquiv.transvections (ZMod 2) (Additive (Source.Utilde H V₃ (zpowers (z : G))))) →
      (Nonempty (Q.Model linearFourRepresentation) ∨
        Nonempty (Q.Model (BinaryPermutation.naturalRepresentation (Fin 6))) ∨
        ∃ N : Q.Model (BinaryPermutation.coreRepresentation (Fin 7)),
          (N.moduleEquiv (CenterQuotientAction.vector b)).val =
            Pi.single (4 : Fin 7) 1 + Pi.single 5 1) ∨
      Nonempty (CoverHyperplanes.CoverCoordinates H V₃ (zpowers (z : G))))
    (hgeo : ∀ d : CriticalPair L T H V, EarlierGeometry d V₃ (zpowers (z : G))) :
    Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone (zpowers (z : G))) < Source.UH H V₃ ↔
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) (zpowers (z : G)) < c.Ugamma V₃ := by
  have hno (d : CriticalPair L T H V) := no_asymmetric_criticalPair d
    V₂ V₃ L₂ M z Q P hH hcard hz hZ₂ hZ₃ b hb hbZ hM a f hLV htrans hHC hQ
    (hgeo d).VH_endpoint (hgeo d).Vgamma_H (hgeo d).DH_kernel
    (hgeo d).Dgamma_kernel (hgeo d).lines_disjoint (hgeo d).cross_centralizes hmodels
  have hZ : H ≤ normalizer (zpowers (z : G)) := by
    intro h hh
    exact mem_normalizer_iff_map_conj_eq.mpr
      (CoverGeometry.fixes_central_line H (z : G) h hH hh)
  have hUV : Source.UH H V₃ ≤ Source.VH H V := conjugateSpanBy_mono f.hyperplane_le le_rfl
  have hγH : c.Ugamma V₃ ≤ H := (map_mono hUV).trans (hgeo c).Vgamma_H
  have hUA : Source.UH H V₃ ≤ normalizer (c.Aone (zpowers (z : G))) := by
    have hn := map_mono (f := (MulAut.conj (c.gb : G)).toMonoidHom) hZ
    rw [map_equiv_normalizer_eq] at hn
    rw [← c.vertexGroup_gamma] at hn
    exact (hUV.trans (hgeo c).VH_endpoint).trans hn
  constructor
  · intro hs
    by_contra hn
    have he := eq_of_le_of_not_lt (commutatorPreimage_le (c.Ugamma V₃)
      (Source.UH H V₃) (zpowers (z : G))) hn
    exact hno c ⟨hs, he⟩
  · intro hs
    by_contra hn
    have he := eq_of_le_of_not_lt (commutatorPreimage_le (Source.UH H V₃)
      (c.Ugamma V₃) (c.Aone (zpowers (z : G)))) hn
    obtain ⟨r⟩ := exists_reversal_of_strict c V₃ (zpowers (z : G))
      (hgeo c).length f.hyperplane_le (hgeo c).Vgamma_H hZ (hgeo c).first_kernel hs
    exact hno r.pair (reverse_asymmetry r V₃ (zpowers (z : G)) hZ hγH hUA he hs)

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.Reorientation
end
