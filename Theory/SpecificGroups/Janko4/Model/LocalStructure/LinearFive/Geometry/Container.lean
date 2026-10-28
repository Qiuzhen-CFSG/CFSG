module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Geometry.Occurrences
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.MathieuCase

/-!
# The positioned source centralizer container and F-branch normalizer

An element of X outside E has nontrivial image in the original octad kernel.
Its local centralizer stabilizes that octad. The source's nonfirst-class
involution in X ∩ E puts the full ambient centralizer inside max1, giving the
literal bound C(X) ≤ D. The final theorem discharges both the container and
global occurrence premises of the one-or-two-F normalizer argument.

The hypothesis that the chosen 2B witness is in E records the positioning used
before KW (1988), Proposition 2.2.2; it is not inferred merely from X ≤ F.
Orthogonal-subgroup occurrence and transport to this position remain separate.
Source: KW (1988), Proposition 2.2.3, p.491, first paragraph.
-/
@[expose] public noncomputable section
namespace Janko4.LocalStructure.LinearFive.Geometry
open Subgroup Cardinality NativeNormalizer
open Sporadic.Mathieu M24LocalGeometry MathieuCode
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup

/-- A nontrivial octad-kernel image puts the whole local centralizer in D. -/
theorem centralizer_le_D_of_le_M (X : Subgroup Model) (hXQ : X ≤ Q)
    (hXE : ¬ X ≤ E) (hCM : centralizer (X : Set Model) ≤ M) :
    centralizer (X : Set Model) ≤ D := by
  obtain ⟨x,hxX,hxE⟩ := SetLike.not_le_iff_exists.mp hXE
  have hxQ := hXQ hxX
  obtain ⟨a,ha,he⟩ := mem_map.mp hxQ
  change (a : Model) = x at he
  have han : projection a ≠ 1 := by
    intro h
    have hk : a ∈ localKernel matrixA_mul_self matrixB_pow_four := by
      rw [← MathieuHallActors.projection_ker, MonoidHom.mem_ker]
      exact h
    exact hxE (mem_map.mpr ⟨a,hk,he⟩)
  intro c hc
  let d : M := ⟨c,hCM hc⟩
  have hd : projection d ∈ centralizer ({projection a} : Set M24) := by
    apply mem_centralizer_singleton_iff.mpr
    have hh : d*a = a*d := by
      apply Subtype.ext
      change c*(a : Model) = (a : Model)*c
      rw [he]
      exact ((mem_centralizer_iff.mp hc) x hxX).symm
    simpa only [map_mul] using congrArg projection hh
  exact mem_map.mpr ⟨d,octad_kernel_centralizer_le_stabilizer O (projection a) ha han hd,rfl⟩

/-- The source F branch after its 2B witness has been positioned in E.
The zero-form condition is unnecessary for this centralizer calculation once
X is in F and the original nonfirst-class witness lies in X ∩ E. -/
theorem source_F_centralizer_container (X : Subgroup Model)
    (hXF : X ≤ F) (hXE : ¬ X ≤ E) (t : Model) (htX : t ∈ X) (htE : t ∈ E)
    (ht2 : orderOf t = 2) (hnt : ¬ IsConj Janko4.a t) :
    centralizer (X : Set Model) ≤ D := by
  apply centralizer_le_D_of_le_M X (hXF.trans F_le_Q) hXE
  have ht1 : t ≠ 1 := by intro he; rw [he,orderOf_one] at ht2; omega
  exact (centralizer_le (Set.singleton_subset_iff.mpr htX)).trans
    (ElementaryNormalizerCover.kernel_nonfirst_centralizer_le_max1 t htE ht1 hnt)

/-- All native occurrence and centralizer premises in the positioned F branch
are discharged; the result uses the full generated F normalizer. -/
theorem source_F_normalizer_alternatives (X : Subgroup Model)
    (hXF : X ≤ F) (hXE : ¬ X ≤ E) (t : Model) (htX : t ∈ X) (htE : t ∈ E)
    (ht2 : orderOf t = 2) (hnt : ¬ IsConj Janko4.a t) :
    normalizer (X : Set Model) ≤ M_F ∨ normalizer (X : Set Model) ≤ M :=
  native_two_occurrence_normalizer X hXF
    (source_F_centralizer_container X hXF hXE t htX htE ht2 hnt)

end Janko4.LocalStructure.LinearFive.Geometry
