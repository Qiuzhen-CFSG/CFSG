module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Basic
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Duality
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.TransvectionSubgroups

/-!
# Point radicals are preserved up to inverse transpose

For an arbitrary automorphism of the actual binary linear group, its image
of a point radical consists of the identity and transvections. The common-image
or common-kernel theorem puts this subgroup inside a point or hyperplane
radical, and self-centralization makes this containment an equality. The
actual inverse-transpose formula for hyperplane radicals then orients this
single image. Conjugacy propagates that orientation to all point radicals.

The general assembly takes these two geometric facts as explicit premises.
For dimensions four and five, `preservesPointRadicals_or_graph` discharges
both premises using `TransvectionSubgroups` and `Duality`, giving unconditional
coverage for every automorphism of the actual binary linear group.

Source: GLS3, Theorem 2.5.12(b–e,i) and §2.7,
`refs/KGroup/GLS3/chapter2.tex`, lines 1111–1115. Removing the fixed inner
conjugation from the source's graph formula gives the inverse transpose
used in `graphLinear` and leaves the outer coverage problem unchanged.
-/

@[expose] public section

namespace BinaryLinear.OuterCyclic

/-- Conditional assembly: a common-image/common-kernel theorem for transvection
subgroups and the actual inverse-transpose action on hyperplane radicals suffice.
Neither geometric premise is asserted by this reduction. -/
theorem preservesPointRadicals_or_graph_of_transvection_geometry {n : ℕ} (hn : 2 ≤ n)
    (hclass : ∀ H : Subgroup (LinearGroup n),
      (∀ t ∈ H, t ≠ 1 → IsTransvection t) →
      (∃ v : Space n, v ≠ 0 ∧ H ≤ pointRadical n v) ∨
      (∃ f : Space n →ₗ[ZMod 2] ZMod 2, f ≠ 0 ∧ H ≤ hyperplaneRadical n f))
    (hgraph : ∀ f : Space n →ₗ[ZMod 2] ZMod 2, f ≠ 0 →
      ∃ w : Space n, w ≠ 0 ∧
        (hyperplaneRadical n f).map (graphLinear n).toMonoidHom = pointRadical n w)
    (a : MulAut (LinearGroup n)) :
    PreservesPointRadicals a ∨ PreservesPointRadicals (graphLinear n * a) := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : Space n)
  have hR := hclass ((pointRadical n v).map a.toMonoidHom)
    (fun t ht ht1 => map_pointRadical_isTransvection hn a hv ht ht1)
  rcases hR with ⟨w, hw, hle⟩ | ⟨f, hf, hle⟩
  · exact Or.inl (preservesPointRadicals_of_one a hv hw
      (map_pointRadical_eq_of_le_radical hn a hv _ hle))
  · have he := map_pointRadical_eq_of_le_radical hn a hv _ hle
    obtain ⟨w, hw, hgraphw⟩ := hgraph f hf
    apply Or.inr
    apply preservesPointRadicals_of_one (graphLinear n * a) hv hw
    change (pointRadical n v).map
      ((graphLinear n).toMonoidHom.comp a.toMonoidHom) = pointRadical n w
    rw [← Subgroup.map_map, he]
    exact hgraphw

/-- Every automorphism in dimensions four and five preserves point radicals
after a possible inverse transpose. -/
theorem preservesPointRadicals_or_graph {n : ℕ} (hn : n = 4 ∨ n = 5)
    (a : MulAut (LinearGroup n)) :
    PreservesPointRadicals a ∨ PreservesPointRadicals (graphLinear n * a) :=
  preservesPointRadicals_or_graph_of_transvection_geometry (by omega)
    (transvectionSubgroup_le_point_or_hyperplane hn) (graph_hyperplaneRadical hn) a

end BinaryLinear.OuterCyclic
