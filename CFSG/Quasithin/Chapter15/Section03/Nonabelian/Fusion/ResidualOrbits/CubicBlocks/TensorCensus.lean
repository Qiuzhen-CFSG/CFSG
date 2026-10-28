module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Action
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.TensorCensus.Enumeration

/-!
# The four orbits of the cubic tensor block

The checked binary-coordinate calculation enumerates the six determinant-one
frames and the four translations. Its formula is definitionally the published
block transformation. On the distinguished subgroup the translation term
vanishes, leaving the nine nonzero singular matrices and the six invertible
matrices. The other two orbits have twelve and thirty-six elements. Both
inside classes span the distinguished subgroup: every element is a product
of two elements of either class.

This proves the intrinsic model census. Applying it to the source group still
requires the actual action coordinates used by `Transport.lean`.

Source: Aschbacher–Smith, 15.3.61(2), printed pp.1150–1151.
-/

public section
open Subgroup Matrix
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks
open TensorEnumeration

private def frame (i : Fin 6) : Frame := ⟨frameMatrix i, frame_det i⟩

private theorem frame_surjective : Function.Surjective frame := by
  intro l
  obtain ⟨i, hi⟩ := frames_exhaust l.val l.property
  exact ⟨i, Subtype.ext hi⟩

private theorem encode_injective : Function.Injective encode :=
  Function.LeftInverse.injective decode_encode

private theorem step_eq (l r : Fin 6) (t : Fin 4) (x : BlockModel) :
    step l r t (encode x) = encode (transform (frame l) (frame r) (shift t) x) := by
  simp only [step, decode_encode]
  rfl

private theorem transform_translation (l r : Frame) (t u : BinaryPlane)
    (x : BlockModel) (hx : x ∈ modelV) : transform l r t x = transform l r u x := by
  change first x = 0 at hx
  simp only [transform, hx, mulVec_zero, Pi.zero_apply, zero_mul, add_zero]

private theorem related_linear_codes (z : BlockModel) (hz : z ∈ modelV) (x : BlockModel) :
    Related z x ↔ encode x ∈ linearOrbit (encode z) := by
  constructor
  · rintro ⟨l, r, t, rfl⟩
    obtain ⟨i, rfl⟩ := frame_surjective l
    obtain ⟨j, rfl⟩ := frame_surjective r
    apply Finset.mem_image.mpr
    refine ⟨(i, j), Finset.mem_univ _, ?_⟩
    change step i j 0 (encode z) = _
    rw [step_eq, transform_translation (frame i) (frame j) (shift 0) t z hz]
  · intro h
    obtain ⟨⟨i, j⟩, _, hij⟩ := Finset.mem_image.mp h
    change step i j 0 (encode z) = encode x at hij
    rw [step_eq] at hij
    exact ⟨frame i, frame j, shift 0, encode_injective hij⟩

private theorem related_affine_codes (z x : BlockModel) :
    Related z x ↔ encode x ∈ affineOrbit (encode z) := by
  constructor
  · rintro ⟨l, r, t, rfl⟩
    obtain ⟨i, rfl⟩ := frame_surjective l
    obtain ⟨j, rfl⟩ := frame_surjective r
    obtain ⟨k, rfl⟩ := shifts_exhaust t
    apply Finset.mem_image.mpr
    exact ⟨(i, j, k), Finset.mem_univ _, step_eq i j k z⟩
  · intro h
    obtain ⟨⟨i, j, k⟩, _, hijk⟩ := Finset.mem_image.mp h
    change step i j k (encode z) = encode x at hijk
    rw [step_eq] at hijk
    exact ⟨frame i, frame j, shift k, encode_injective hijk⟩

private theorem related_singular_codes (z : BlockModel) (hz : Singular z) (x : BlockModel) :
    Related z x ↔ encode x ∈ singularCodes := by
  rw [related_linear_codes z hz.1, singular_orbit _ ((singular_spec z).mp hz)]

private theorem related_nonsingular_codes (v : BlockModel) (hv : Nonsingular v)
    (x : BlockModel) : Related v x ↔ encode x ∈ nonsingularCodes := by
  rw [related_linear_codes v hv.1, nonsingular_orbit _ ((nonsingular_spec v).mp hv)]

private theorem related_outsideOne_codes (x : BlockModel) :
    Related outsideOne x ↔ encode x ∈ outsideOneCodes := by
  rw [related_affine_codes, show encode outsideOne = 1 from rfl, outsideOne_orbit]

private theorem related_outsideTwo_codes (x : BlockModel) :
    Related outsideTwo x ↔ encode x ∈ outsideTwoCodes := by
  rw [related_affine_codes, show encode outsideTwo = 17 from rfl, outsideTwo_orbit]

private theorem card_from_codes (z : BlockModel) (s : Finset ℕ)
    (h : ∀ x, Related z x ↔ encode x ∈ s) (hb : ∀ n ∈ s, n < 64) :
    Nat.card {x // Related z x} = s.card := by
  let f : {x // Related z x} → s := fun x => ⟨encode x.val, (h x.val).mp x.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      exact Subtype.ext (encode_injective (congrArg Subtype.val hxy))
    · intro n
      have hn : encode (decode n.val) = n.val := encode_decode ⟨n.val, hb _ n.property⟩
      refine ⟨⟨decode n.val, (h _).mpr ?_⟩, Subtype.ext hn⟩
      simpa only [hn] using n.property
  exact (Nat.card_congr (Equiv.ofBijective f hf)).trans (Nat.card_eq_finsetCard s)

private theorem span_from_codes (s : Finset ℕ) (hb : ∀ n ∈ s, n < 64)
    (hin : ∀ x : BlockModel, encode x ∈ s → x ∈ modelV)
    (hp : ∀ n ∈ insideCodes, ∃ a ∈ s, ∃ b ∈ s, decode n = decode a * decode b) :
    closure {x : BlockModel | encode x ∈ s} = modelV := by
  apply le_antisymm
  · exact (closure_le modelV).mpr hin
  · intro x hx
    obtain ⟨a, ha, b, hbb, he⟩ := hp (encode x) ((inside_spec x).mp hx)
    have hdecode (n : ℕ) (hn : n ∈ s) : encode (decode n) ∈ s := by
      rwa [encode_decode ⟨n, hb n hn⟩]
    rw [← decode_encode x, he]
    exact mul_mem (subset_closure (hdecode a ha)) (subset_closure (hdecode b hbb))

/-- The exact binary tensor model has its four asserted orbits, and both
inside orbits generate the distinguished four-dimensional subgroup. -/
theorem tensorCensus : TensorCensus where
  singular_card z hz :=
    (card_from_codes z singularCodes (related_singular_codes z hz) code_bounds.1).trans
      code_cards.1
  nonsingular_card v hv :=
    (card_from_codes v nonsingularCodes (related_nonsingular_codes v hv)
      code_bounds.2.1).trans code_cards.2.1
  outsideOne_card :=
    (card_from_codes outsideOne outsideOneCodes related_outsideOne_codes
      code_bounds.2.2.1).trans code_cards.2.2.1
  outsideTwo_card :=
    (card_from_codes outsideTwo outsideTwoCodes related_outsideTwo_codes
      code_bounds.2.2.2).trans code_cards.2.2.2
  singular_span z hz := by
    have he : {x | Related z x} = {x | encode x ∈ singularCodes} :=
      Set.ext (related_singular_codes z hz)
    rw [he]
    exact span_from_codes singularCodes code_bounds.1
      (fun x hx => ((singular_spec x).mpr hx).1) singular_products
  nonsingular_span v hv := by
    have he : {x | Related v x} = {x | encode x ∈ nonsingularCodes} :=
      Set.ext (related_nonsingular_codes v hv)
    rw [he]
    exact span_from_codes nonsingularCodes code_bounds.2.1
      (fun x hx => ((nonsingular_spec x).mpr hx).1) nonsingular_products
  cover z hz v hv x hx := by
    have hn : (⟨encode x, encode_lt x⟩ : Fin 64) ≠ 0 := by
      intro h
      apply hx
      apply encode_injective
      exact congrArg Fin.val h
    rcases TensorEnumeration.cover ⟨encode x, encode_lt x⟩ hn with h | h | h | h
    · exact Or.inl ((related_singular_codes z hz x).mpr h)
    · exact Or.inr (Or.inl ((related_nonsingular_codes v hv x).mpr h))
    · exact Or.inr (Or.inr (Or.inl ((related_outsideOne_codes x).mpr h)))
    · exact Or.inr (Or.inr (Or.inr ((related_outsideTwo_codes x).mpr h)))

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks
