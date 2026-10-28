module
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Pairing
public import Theory.Representation.BinaryOffender.CommutatorRank
/-!
# Displacement through the actual M22 pair-line quotient

Restrict the quotient map to the ambient displacement image. Its image is
exactly the displacement image on the ten-dimensional cocode. Its kernel is
the intersection with the marked pair line. Rank-nullity therefore preserves
displacement when the pair class lies outside that image, and subtracts one
when it lies inside. No involution rank or incidence calculation is assumed
or asserted here; those geometric tests are separate obligations.

Source: the quotient in Aschbacher--Smith H.13.1 and the calculation required
in H.14.4, printed pp.395,397--398, combined manuscript of 1 March 2004.
-/

public section
noncomputable section
open Sporadic.Mathieu Representation.BinaryOffender
namespace MathieuCode

private theorem m22_displacement_quotient_rank_nullity (g : m22PairStabilizer) :
    fixedCodim m22OuterCocodeRepresentation (Subgroup.zpowers g) +
      Module.finrank (ZMod 2)
        (m22PairLine.comap (LinearMap.range (cocodeRepresentation g.val - LinearMap.id)).subtype) =
      fixedCodim cocodeRepresentation (Subgroup.zpowers g.val) := by
  let R := LinearMap.range (cocodeRepresentation g.val - LinearMap.id)
  let f : R →ₗ[ZMod 2] M22Cocode := m22PairLine.mkQ.comp R.subtype
  have hr : f.range = (m22OuterCocodeRepresentation g - LinearMap.id).range := by
    ext v
    constructor
    · rintro ⟨⟨w, u, hu⟩, rfl⟩
      refine ⟨m22PairLine.mkQ u, ?_⟩
      change m22PairLine.mkQ (cocodeRepresentation g.val u) - m22PairLine.mkQ u =
        m22PairLine.mkQ w
      rw [← map_sub]
      exact congrArg m22PairLine.mkQ hu
    · rintro ⟨u, rfl⟩
      obtain ⟨v, rfl⟩ := m22PairLine.mkQ_surjective u
      refine ⟨⟨cocodeRepresentation g.val v - v, ⟨v, rfl⟩⟩, ?_⟩
      exact map_sub m22PairLine.mkQ _ _
  have hk : f.ker = m22PairLine.comap R.subtype := by
    ext v
    exact Submodule.Quotient.mk_eq_zero m22PairLine
  rw [fixedCodim_zpowers_eq_displacement_rank, fixedCodim_zpowers_eq_displacement_rank,
    ← hr, ← hk]
  exact f.finrank_range_add_finrank_ker

/-- Quotienting by a pair outside the displacement image preserves displacement. -/
theorem m22Outer_cocode_displacement_of_pair_not_mem (g : m22PairStabilizer)
    (h : m22PairClass ∉ LinearMap.range (cocodeRepresentation g.val - LinearMap.id)) :
    fixedCodim m22OuterCocodeRepresentation (Subgroup.zpowers g) =
      fixedCodim cocodeRepresentation (Subgroup.zpowers g.val) := by
  have hn := m22_displacement_quotient_rank_nullity g
  have hd : Disjoint (LinearMap.range (cocodeRepresentation g.val - LinearMap.id)) m22PairLine :=
    Submodule.disjoint_span_singleton_of_notMem h
  have hz : m22PairLine.comap
      (LinearMap.range (cocodeRepresentation g.val - LinearMap.id)).subtype = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro v hv
    apply Subtype.ext
    exact (Submodule.disjoint_def.mp hd) v.val v.property hv
  rw [hz, finrank_bot, add_zero] at hn
  exact hn

/-- Quotienting by a pair in the displacement image removes exactly one dimension. -/
theorem m22Outer_cocode_displacement_of_pair_mem (g : m22PairStabilizer)
    (h : m22PairClass ∈ LinearMap.range (cocodeRepresentation g.val - LinearMap.id)) :
    fixedCodim m22OuterCocodeRepresentation (Subgroup.zpowers g) + 1 =
      fixedCodim cocodeRepresentation (Subgroup.zpowers g.val) := by
  have hn := m22_displacement_quotient_rank_nullity g
  have hl : m22PairLine ≤ LinearMap.range (cocodeRepresentation g.val - LinearMap.id) :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr h)
  rw [(Submodule.comapSubtypeEquivOfLe hl).finrank_eq, finrank_m22PairLine] at hn
  exact hn
end MathieuCode
