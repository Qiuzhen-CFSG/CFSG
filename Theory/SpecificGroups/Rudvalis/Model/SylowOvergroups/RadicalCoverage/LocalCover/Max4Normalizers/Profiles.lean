module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.Geometry
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Invariance

/-!
# Invariant sizes of adjacency-profile fibers on the marked 28 points

A set-stabilizing model element permutes the marked points and preserves the
certified Rudvalis orbital. It therefore maps each fiber of equal adjacency
profiles bijectively onto the fiber at the image point. Fiber cardinality is
an invariant of the full ambient set stabilizer.

This provides the conceptual step for the first-image bound. The proposed
numerical characterization of the image set by fiber size remains a separate
finite certificate; no multiplicity computation is asserted here.

Source: the ATLAS degree-4060 model and max4 words preserved in this repository;
GLS3 Table 5.3r. This supports the independent geometric route to the [Asc86b]
application on Aschbacher--Smith printed p.511.
-/

open scoped Pointwise

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers

@[expose] public def sameProfile (x y : Fin 4060) : Prop :=
  ∀ z ∈ pointSet, OuterNormalizer.adj z x ↔ OuterNormalizer.adj z y

private theorem profile_forward (g : Model) (hg : g ∈ pointSetStabilizer)
    {x y : Fin 4060} (h : sameProfile x y) : sameProfile (g • x) (g • y) := by
  have hG := OuterNormalizer.model_le_relationAut
    OuterNormalizer.aPerm_mem_relationAut OuterNormalizer.bPerm_mem_relationAut
  intro z hz
  have hz' : g⁻¹ • z ∈ pointSet :=
    ((mem_pointSetStabilizer g⁻¹).mp (pointSetStabilizer.inv_mem hg) z).mpr hz
  have hx := hG g.property (g⁻¹ • z) x
  have hy := hG g.property (g⁻¹ • z) y
  change OuterNormalizer.adj (g • (g⁻¹ • z)) (g • x) ↔ _ at hx
  change OuterNormalizer.adj (g • (g⁻¹ • z)) (g • y) ↔ _ at hy
  rw [smul_inv_smul] at hx hy
  exact hx.trans ((h _ hz').trans hy.symm)

public theorem sameProfile_smul_iff (g : Model) (hg : g ∈ pointSetStabilizer)
    (x y : Fin 4060) : sameProfile (g • x) (g • y) ↔ sameProfile x y := by
  constructor
  · intro h
    have hi := profile_forward g⁻¹ (pointSetStabilizer.inv_mem hg) h
    simpa only [inv_smul_smul] using hi
  · exact profile_forward g hg

@[expose] public def profileFiber (x : Fin 4060) : Set (Fin 4060) := {y | sameProfile x y}

public theorem profileFiber_smul (g : Model) (hg : g ∈ pointSetStabilizer)
    (x : Fin 4060) : g • profileFiber x = profileFiber (g • x) := by
  ext y
  obtain ⟨z, rfl⟩ := MulAction.surjective g y
  rw [Set.smul_mem_smul_set_iff]
  exact (sameProfile_smul_iff g hg x z).symm

public theorem profileFiber_card_smul (g : Model) (hg : g ∈ pointSetStabilizer)
    (x : Fin 4060) : (profileFiber (g • x)).ncard = (profileFiber x).ncard := by
  have he : g.val '' profileFiber x = profileFiber (g • x) := profileFiber_smul g hg x
  rw [← he, Set.ncard_image_of_injective _ g.val.injective]

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers
