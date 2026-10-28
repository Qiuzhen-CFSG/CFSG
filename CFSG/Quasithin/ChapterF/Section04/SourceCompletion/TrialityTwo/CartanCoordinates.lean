module
public import Theory.SpecificGroups.Triality.BinaryTorusEndpoints
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityTwo.CartanReflections

/-!
# Exact coordinates for the original binary-triality reflection pair

The native endpoint-normalizer theorem applies to both preimages of the same
Cartan-aligned pair. The arms preimage has one long-root correction, and the
central preimage has one simple-root scalar on the left and one long-root
correction on the right. The actual completion evaluates these words through
its unchanged middle and endpoint maps, using both commuting squares.

The order bound therefore supplies an actual order-six pair in this explicit
coordinate family. The native sixth-power relation for that pair remains a
separate mathematical obligation; no ambient recognition is asserted.
Source: Aschbacher--Smith F.4.15--17, pp.281--283 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.SourceCompletion.TrialityTwo.Completion
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.ConcreteBruhat _root_.Triality.Standard.BinaryTorusEndpoints
variable {G : Type*} [Group G] (c : Completion G)

/-- The actual left marking evaluates the coordinate word with the same
middle factors and the fixed native reflection. -/
theorem left_endpointWord (a b : Fin 3 → fixedField parameters) (t : torus parameters) :
    c.left (endpointWord .arms a b t) =
      c.middle (fixedBorel a) * c.left (simpleEndpoint .arms) *
        c.middle (fixedBorel b) * c.middle (torusBorel t) := by
  simp only [endpointWord,map_mul]
  rfl

/-- The right commuting square gives the same literal middle factors. -/
theorem right_endpointWord (a b : Fin 3 → fixedField parameters) (t : torus parameters) :
    c.right (endpointWord .central a b t) =
      c.middle (fixedBorel a) * c.right (simpleEndpoint .central) *
        c.middle (fixedBorel b) * c.middle (torusBorel t) := by
  have hm (x : borel parameters) : c.right (amalgam.right x) = c.middle x :=
    (DFunLike.congr_fun c.compatible x).symm
  simp only [endpointWord,map_mul]
  change c.right (amalgam.right (fixedBorel a)) * c.right (simpleEndpoint .central) *
    c.right (amalgam.right (fixedBorel b)) * c.right (amalgam.right (torusBorel t)) = _
  rw [hm,hm,hm]

/-- A torus-normalizing pair has exact native words, with a single fixed
unipotent factor at the arms endpoint and one leading scalar at the central
endpoint. The given pair and maps are unchanged. -/
theorem torus_endpoint_coordinates
    (s : parabolic parameters .arms) (t : parabolic parameters .central)
    (hsout : c.left s ∉ c.middle.range) (htout : c.right t ∉ c.middle.range)
    (hsN : modelCompletion.left s ∈ normalizer (torus parameters : Set Model))
    (htN : modelCompletion.right t ∈ normalizer (torus parameters : Set Model)) :
    ∃ a : Fin 3 → fixedField parameters, ∃ b : fixedField parameters,
      ∃ d : Fin 3 → fixedField parameters, ∃ z w : torus parameters,
      s = endpointWord .arms a 0 z ∧ t = endpointWord .central (Pi.single 0 b) d w := by
  have hsB : (s : Model) ∉ borel parameters := by
    intro h
    exact hsout ⟨⟨s,h⟩,rfl⟩
  have htB : (t : Model) ∉ borel parameters := by
    intro h
    exact htout ⟨⟨t,h⟩,DFunLike.congr_fun c.compatible ⟨t,h⟩⟩
  obtain ⟨a,z,he⟩ := arms_normalizing_coordinates s hsB hsN
  obtain ⟨b,d,w,hf⟩ := central_normalizing_coordinates t htB htN
  exact ⟨a,b,d,z,w,he,hf⟩

variable [Finite G]

/-- The actual order bound produces an order-six pair among these exact
coordinate words, with both original endpoint maps and their torus retained. -/
theorem exists_endpoint_coordinates_of_order_bound
    (horder : Nat.card G ≤ Nat.card Model) :
    ∃ a : Fin 3 → fixedField parameters, ∃ b : fixedField parameters,
      ∃ d : Fin 3 → fixedField parameters, ∃ z w : torus parameters,
      let s := endpointWord .arms a 0 z
      let t := endpointWord .central (Pi.single 0 b) d w
      s^2=1 ∧ t^2=1 ∧ c.left s∉c.middle.range ∧ c.right t∉c.middle.range ∧
        (c.left s*c.right t)^6=1 ∧ orderOf (c.left s*c.right t)=6 ∧
        c.left s ∈ normalizer (borelTorus.map c.middle : Set G) ∧
        c.right t ∈ normalizer (borelTorus.map c.middle : Set G) ∧
        modelCompletion.left s ∈ normalizer (torus parameters : Set Model) ∧
        modelCompletion.right t ∈ normalizer (torus parameters : Set Model) := by
  obtain ⟨s,t,hs,ht,hsout,htout,hpow,ho,hsQ,htQ,hsN,htN⟩ :=
    c.exists_torus_normalizing_endpoint_involutions_of_order_bound horder
  obtain ⟨a,b,d,z,w,he,hf⟩ := c.torus_endpoint_coordinates s t hsout htout hsN htN
  refine ⟨a,b,d,z,w,?_⟩
  dsimp only
  rw [←he,←hf]
  exact ⟨hs,ht,hsout,htout,hpow,ho,hsQ,htQ,hsN,htN⟩

end CFSG.Quasithin.ChapterF.SourceCompletion.TrialityTwo.Completion
