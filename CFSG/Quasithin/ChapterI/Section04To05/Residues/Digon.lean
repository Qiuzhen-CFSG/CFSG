module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.QuotientParabolics
public import CFSG.Quasithin.ChapterI.Section04To05.Geometry
public import Theory.SpecificGroups.SymmetricThreeProduct.Parabolics.ArbitrarySylow

/-!
# The actual line residue of a D-system

D2 identifies the line-group quotient with S₃×S₃. D3 and the actual Sylow
image identify its two maximal parabolics with the coordinate pair, in
either order. Their product and index three lift through the literal core
quotient. Thus the original line group is the setwise product of its two
intersections, and its residue is a three-by-three digon. The string
containments follow for the original cosets, without extra geometry inputs.

Source: Aschbacher–Smith I.5.3(4–5) and I.5.6, printed pp.419–420.
-/

public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] {D : Diagram} (S : DSystem D G)

theorem line_parabolics_product_indices :
    (localParabolic S.family 1 0).index = 3 ∧
    (localParabolic S.family 1 2).index = 3 ∧
    ∀ x : S.family 1, ∃ p ∈ localParabolic S.family 1 0,
      ∃ r ∈ localParabolic S.family 1 2, p * r = x := by
  obtain ⟨e⟩ := S.line_quotient
  let f := S.localQuotientMap 1 e
  have hf : Function.Surjective f := S.localQuotientMap_surjective 1 e
  have hk := S.localQuotientMap_ker_le 1 e
  let P := localParabolic S.family 1 0
  let R := localParabolic S.family 1 2
  have hm := S.line_parabolics.map f hf hk
  obtain ⟨T, hT⟩ := S.localQuotient_sylow 1 e
  have hTP : (T : Subgroup SymmetricThreeProduct.G) ≤ P.map f := by
    rw [hT, ← hm.borel_eq]
    exact inf_le_left
  have hTR : (T : Subgroup SymmetricThreeProduct.G) ≤ R.map f := by
    rw [hT, ← hm.borel_eq]
    exact inf_le_right
  obtain ⟨hp, hr, hprod⟩ := SymmetricThreeProduct.distinct_coatoms_product T
    (P.map f) (R.map f) hm.left_maximal hm.right_maximal hTP hTR hm.distinct
  have hkP : f.ker ≤ P := hk.trans (S.line_parabolics.borel_eq ▸ inf_le_left)
  have hkR : f.ker ≤ R := hk.trans (S.line_parabolics.borel_eq ▸ inf_le_right)
  refine ⟨(P.index_map_eq hf hkP).symm.trans hp,
    (R.index_map_eq hf hkR).symm.trans hr, ?_⟩
  intro x
  obtain ⟨a, ha, b, hb, hab⟩ := hprod (f x)
  obtain ⟨p, hp, rfl⟩ := ha
  refine ⟨p, hp, p⁻¹ * x, ?_, mul_inv_cancel_left p x⟩
  change p⁻¹ * x ∈ R
  rw [← comap_map_eq_self hkR]
  change f (p⁻¹ * x) ∈ R.map f
  rw [map_mul, map_inv, ← hab, inv_mul_cancel_left]
  exact hb

/-- The middle product is derived from D2–D3, not supplied as a geometry premise. -/
theorem middleProduct : CosetGeometry.MiddleProduct S.family := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, r, hr, he⟩ := S.line_parabolics_product_indices.2.2 ⟨x, hx⟩
    exact Set.mem_mul.mpr ⟨p.val, ⟨p.property, hp⟩, r.val, ⟨r.property, hr⟩,
      congrArg Subtype.val he⟩
  · rintro ⟨p, hp, r, hr, rfl⟩
    exact (S.family 1).mul_mem hp.1 hr.1

theorem line_residue_digon (l : S.Line) :
    Nat.card {v : S.Residue ⟨1, l⟩ // v.val.type = 0} = 3 ∧
    Nat.card {v : S.Residue ⟨1, l⟩ // v.val.type = 2} = 3 ∧
    ∀ u v : S.Residue ⟨1, l⟩, u.val.type ≠ v.val.type → S.Incident u.val v.val :=
  CosetGeometry.line_residue_three_by_three S.family S.middleProduct
    S.line_parabolics_product_indices.1 S.line_parabolics_product_indices.2.1 l

/-- The original string incidence, I.5.6: a point on a line lies in each plane on that line. -/
theorem point_line_plane {x : S.Point} {l : S.Line} {π : S.Plane}
    (hx : S.Inc x l) (hπ : S.Inc l π) : S.Inc x π :=
  CosetGeometry.incident_of_incident_line S.family S.middleProduct hx hπ

end Quasithin.I5.DSystem
