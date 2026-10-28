module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LeviLifts.Seeds
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LeviLifts.Cocycles
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.Displacement

/-!
# Promotion of the P-fixed seed to a Levi-fixed lift

The seed is constructed from the quadratic conjugate axis group, with the
original quotient map retained. In rank one, averaging over an odd index
produces the Levi-fixed lift. For binary Levi groups of rank at least two,
the natural cocycle calculations kill the displacement cocycle: the fixed
coordinate is killed by perfectness, and the natural coordinate by vanishing
of H¹ or by the explicit SL₃(2) exceptional-cocycle calculation.

The outstanding geometric inputs below are an actual Levi action equivalence
and elementary-root placement, or an actual odd subgroup index. They do not
assume fixed lifting or splitting. The full source result still requires
constructing these inputs from the coherent quotient marking.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.9(1), printed pp.92–93.
-/

@[expose] public section
open Representation Representation.BinaryOffender Representation.OneCohomology
open Matrix.SpecialLinearGroup
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting.LeviLifts
open QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {n : ℕ} {ρ : Representation (ZMod 2) G V}
  {d : DoubleNatural F n ρ} (m : QuotientCoordinates d)
  {i j : Fin n} (hij : i ≠ j)

/-- The seed subgroup as a subgroup of the literal Levi, for relative index. -/
noncomputable def seedInLevi : Subgroup (m.K j) :=
  (seedGroup m hij).subgroupOf (m.K j)

/-- The geometric binary input: an actual natural-plus-fixed decomposition of
the original submodule restricted to K, with an elementary transvection in P.
Changing the actor marking may absorb the contragredient orientation. -/
structure BinaryLeviCoordinates where
  action : ActionEquiv (d.space.toRepresentation.comp (m.K j).subtype) (binaryModel (n - 1))
  root : ∃ a b : Fin (n - 1), ∃ hab : a ≠ b,
    (action.groupEquiv.symm (transvection hab 1)).val ∈ seedGroup m hij

/-- Odd index suffices to promote every constructed P-fixed lift. In n = 3
the missing geometric assertion is that P is the full root Sylow of K. -/
theorem fixed_lifts_of_odd_index (hq : IsQuadratic ρ (m.Q j))
    (hindex : Odd (seedInLevi m hij).index) : m.FixedLifts j := by
  intro z hz
  obtain ⟨v, hP, hv⟩ := seed_fixed_lifts m hij hq hz
  have hK : d.space.toSubmodule.mkQ v ∈ fixedSpace d.space.quotientRepresentation (m.K j) := by
    intro k
    rw [hv]
    exact k.property.2.2 z hz
  obtain ⟨w, hw, he⟩ := lift_of_odd_index ρ d.space (m.K j) (seedInLevi m hij)
    hindex v hK (fun p => hP ⟨p.val.val, p.property⟩)
  exact ⟨w, hw, he.trans hv⟩

/-- The complete cocycle argument for every binary dimension at least four,
including the SL₃(2) Levi exception, under actual geometric coordinates. -/
theorem fixed_lifts_of_binary_coordinates (hn : 4 ≤ n)
    (hq : IsQuadratic ρ (m.Q j)) (b : BinaryLeviCoordinates m hij) : m.FixedLifts j := by
  intro z hz
  obtain ⟨v, hP, hv⟩ := seed_fixed_lifts m hij hq hz
  have hK : d.space.toSubmodule.mkQ v ∈ fixedSpace d.space.quotientRepresentation (m.K j) := by
    intro k
    rw [hv]
    exact k.property.2.2 z hz
  let f := relativeCocycle ρ d.space (m.K j) v hK
  let E := cocyclesCongr (d.space.toRepresentation.comp (m.K j).subtype)
    (binaryModel (n - 1)) b.action.groupEquiv b.action.linearEquiv b.action.intertwines
  obtain ⟨a, c, hac, ht⟩ := b.root
  have hf : f.val (b.action.groupEquiv.symm (transvection hac 1)) = 0 := by
    apply Subtype.ext
    exact sub_eq_zero.mpr (hP ⟨_, ht⟩)
  have hEf : (E f).val (transvection hac 1) = 0 := by
    change b.action.linearEquiv (f.val (b.action.groupEquiv.symm (transvection hac 1))) = 0
    rw [hf, map_zero]
  obtain ⟨u, hu⟩ := binaryModel_principal (by omega : 3 ≤ n - 1) (E f) hac hEf
  have hprincipal : principal (d.space.toRepresentation.comp (m.K j).subtype)
      (b.action.linearEquiv.symm u) = f := by
    apply E.injective
    rw [cocyclesCongr_principal, LinearEquiv.apply_symm_apply]
    exact hu
  obtain ⟨w, hw, he⟩ := lift_of_principal ρ d.space (m.K j) v hK
    (b.action.linearEquiv.symm u) hprincipal
  exact ⟨w, hw, he.trans hv⟩

/-- The two independent matrix-geometry obligations for the source family. -/
def SourceLeviGeometry : Prop :=
  (n = 3 → Odd (seedInLevi m hij).index) ∧
  (F.degree = 1 → 4 ≤ n → Nonempty (BinaryLeviCoordinates m hij))

/-- Conditional final assembly of the Levi step: the extra inputs are purely
matrix geometry, and quadraticity is used to construct the fixed seed. -/
theorem fixed_lifts_of_geometry (hfamily : SourceFamily F n)
    (hq : IsQuadratic ρ (m.Q j)) (hgeometry : SourceLeviGeometry m hij) : m.FixedLifts j := by
  rcases hfamily with hn | ⟨hF, hn⟩
  · exact fixed_lifts_of_odd_index m hij hq (hgeometry.1 hn)
  · obtain ⟨b⟩ := hgeometry.2 hF hn
    exact fixed_lifts_of_binary_coordinates m hij hn hq b

/-- Literal fixed-line-vector consumer of the constructed Levi lifts. -/
theorem exists_fixed_lineVector_of_geometry (hfamily : SourceFamily F n)
    (hq : IsQuadratic ρ (m.Q j)) (hgeometry : SourceLeviGeometry m hij) :
    ∃ v : V, v ∈ fixedSpace ρ (m.K j) ∧
      d.space.toSubmodule.mkQ v = m.lineVector j :=
  m.exists_fixed_lineVector j (fixed_lifts_of_geometry m hij hfamily hq hgeometry)

/-- The local-complement consumer uses exactly the original quotient map,
axis group and Levi. Its remaining orbit premises concern the known quotient. -/
theorem local_complement_of_geometry (hfamily : SourceFamily F n)
    (hq : IsQuadratic ρ (m.Q j)) (hgeometry : SourceLeviGeometry m hij)
    (hnorm : ∀ k ∈ m.K j, ∀ x ∈ m.Q j, k * x * k⁻¹ ∈ m.Q j)
    (hfree : ∀ x : m.Q j,
      d.space.quotientRepresentation x (m.lineVector j) = m.lineVector j → (x : G) = 1)
    (hout : m.lineVector j ∉ fixedSpace d.space.quotientRepresentation (m.Q j))
    (hcover : ∀ z : V ⧸ d.space.toSubmodule, ∃ c : ZMod 2, ∃ x : m.Q j,
      z = c • m.lineVector j +
        (d.space.quotientRepresentation x (m.lineVector j) - m.lineVector j)) :
    ∃ C : Submodule (ZMod 2) V, IsCompl d.space.toSubmodule C ∧
      m.K j ⊔ m.Q j ≤ subspaceStabilizer ρ C := by
  obtain ⟨v, hv, hπ⟩ := exists_fixed_lineVector_of_geometry m hij hfamily hq hgeometry
  refine ⟨localSpace ρ (m.Q j) hq v, ?_, ?_⟩
  · apply localSpace_isCompl ρ (m.Q j) hq v d.space
    · simpa only [hπ] using hfree
    · simpa only [hπ] using hout
    · simpa only [hπ] using hcover
  · exact localSpace_invariant ρ (m.Q j) hq v (m.K j) hnorm (fun k hk => hv ⟨k,hk⟩)

end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting.LeviLifts
