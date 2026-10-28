module
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.Orbits
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.PairResidual.Stabilizer
public import Theory.Mathieu.M22.Properties.TwoRank

/-!
# The second centralizer inside the point group

Restriction of the original Todd projection maps C_M(t) onto the literal
pair-vector stabilizer, with kernel the original E. The resulting quotient
isomorphism retains this map and identifies C_M(t)/E with Aut(M₂₂), giving
its two-rank bound of five. This concerns C_M(t); equality with the full
ambient centralizer requires the later fixed-coset argument.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (6.3)(2),(c), p.602.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.JankoFour.SourceFusion
open LocalGeometry LocalGeometry.LocalSubgroups SourceIncidence
open Sporadic.Mathieu MathieuCode
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

noncomputable abbrev secondCentralizer (a : LocalData h) : Subgroup G :=
  centralizer (second a) ⊓ a.P.M

theorem second_centralizer_iff (a : LocalData h) (m : a.P.M) :
    (m : G) ∈ centralizer (second a) ↔
      cocodeRepresentation (a.P.projection m) (pairVector ⟨{0,1},by decide⟩) =
        pairVector ⟨{0,1},by decide⟩ := by
  rw [mem_centralizer_singleton_iff]
  have hh := vector_conj a.P m (pairVector ⟨{0,1},by decide⟩)
  change (m : G) * second a * (m : G)⁻¹ = _ at hh
  constructor
  · intro he
    rw [he,mul_inv_cancel_right] at hh
    exact (congrArg Multiplicative.toAdd (a.P.vectorEmbedding_injective hh)).symm
  · intro he
    rw [he] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh

/-- The restriction of the original Todd quotient to C_M(t). -/
noncomputable def secondCentralizerProjection (a : LocalData h) :
    secondCentralizer a →*
      cocodeVectorStabilizer cocodeRepresentation (pairVector ⟨{0,1},by decide⟩) where
  toFun m := ⟨a.P.projection ⟨m.val,m.property.2⟩,
    (second_centralizer_iff a ⟨m.val,m.property.2⟩).mp m.property.1⟩
  map_one' := Subtype.ext (map_one a.P.projection)
  map_mul' m n := Subtype.ext (map_mul a.P.projection
    ⟨m.val,m.property.2⟩ ⟨n.val,n.property.2⟩)

theorem secondCentralizerProjection_surjective (a : LocalData h) :
    Function.Surjective (secondCentralizerProjection a) := by
  intro g
  obtain ⟨m,hm⟩ := a.projection_surjective g.val
  have hc : (m : G) ∈ centralizer (second a) :=
    (second_centralizer_iff a m).mpr (by rw [hm]; exact g.property)
  exact ⟨⟨m, hc, m.property⟩, Subtype.ext hm⟩

theorem secondCentralizerProjection_ker (a : LocalData h) :
    (secondCentralizerProjection a).ker = a.P.E.subgroupOf (secondCentralizer a) := by
  ext m
  change (⟨a.P.projection ⟨m.val,m.property.2⟩,_⟩ :
    cocodeVectorStabilizer cocodeRepresentation (pairVector ⟨{0,1},by decide⟩)) = 1 ↔ _
  rw [Subtype.ext_iff]
  change (⟨m.val,m.property.2⟩ : a.P.M) ∈ a.P.projection.ker ↔ _
  rw [a.P.projection_ker]
  rfl

instance secondCentralizer_radical_normal (a : LocalData h) :
    (a.P.E.subgroupOf (secondCentralizer a)).Normal := by
  rw [←secondCentralizerProjection_ker a]
  infer_instance

/-- The actual centralizer quotient, with its unchanged Todd projection. -/
noncomputable def secondCentralizerQuotientEquiv (a : LocalData h) :
    (secondCentralizer a ⧸ a.P.E.subgroupOf (secondCentralizer a)) ≃*
      cocodeVectorStabilizer cocodeRepresentation (pairVector ⟨{0,1},by decide⟩) :=
  (QuotientGroup.quotientMulEquivOfEq (secondCentralizerProjection_ker a).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (secondCentralizerProjection_surjective a))

theorem secondCentralizerQuotientEquiv_mk (a : LocalData h) (m : secondCentralizer a) :
    secondCentralizerQuotientEquiv a (QuotientGroup.mk' _ m) =
      secondCentralizerProjection a m := rfl

/-- AS91 (6.3)(2): the quotient of the centralizer inside the point group is
the automorphism group of the actual Mathieu group M₂₂. -/
theorem secondCentralizer_quotient (a : LocalData h) :
    Nonempty ((secondCentralizer a ⧸ a.P.E.subgroupOf (secondCentralizer a)) ≃*
      MulAut M22) := by
  obtain ⟨e⟩ := pairVector_stabilizer_equiv ⟨{0,1},by decide⟩
  exact ⟨(secondCentralizerQuotientEquiv a).trans e⟩

/-- The rank bound in source (6.3)(c), on the original centralizer quotient. -/
theorem secondCentralizer_quotient_rank_le (a : LocalData h) :
    primeRank 2 (secondCentralizer a ⧸ a.P.E.subgroupOf (secondCentralizer a)) ≤ 5 := by
  obtain ⟨e⟩ := secondCentralizer_quotient a
  rw [primeRank_equiv 2 e]
  exact m22_automorphism_twoRank_le_five

end Theory.GroupTheory.Recognition.JankoFour.SourceFusion

