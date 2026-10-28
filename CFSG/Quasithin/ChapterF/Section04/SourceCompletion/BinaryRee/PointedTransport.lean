module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.BinaryRee.Presentation
/-!
# Transporting the pointed pair census through the original completion

Smallness supplies adjacent apartment involutions outside the actual common
Borel. Endpoint faithfulness turns them into literal model involutions. A common
Borel conjugator in the finite model census then transports through both
original inclusion maps, preserving the eighth-power relation. Three intrinsic
bad-pair exclusions consequently select the standard pair.

The finite census and its three word exclusions remain explicit inputs to this
transport lemma; the final source assembly supplies their concrete producers.
No model product order is transported to an unrelated completion.

Source: Aschbacher--Smith F.4.4, F.4.8 and F.4.15--17, pp.274,278,281--283.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee.Completion
open SimpleGraph SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory
local notation "B" => Tits.ExceptionalParabolics.FullRee.B
local notation "P" => Tits.ExceptionalParabolics.FullRee.first
local notation "Q" => Tits.ExceptionalParabolics.FullRee.second
local notation "α" => Tits.ExceptionalParabolics.FullRee.amalgam
variable {G : Type*} [Group G] (c : Completion G)

private theorem left_conjugate {x r : P} (b : B)
    (h : (x : ReeF4.Model 0) = b * r * (b : ReeF4.Model 0)⁻¹) :
    c.left x = MulAut.conj (c.middle b) (c.left r) := by
  have he : x = (α).left b * r * ((α).left b)⁻¹ := Subtype.ext h
  rw [he, map_mul, map_mul, map_inv]
  rfl

private theorem right_conjugate {x s : Q} (b : B)
    (h : (x : ReeF4.Model 0) = b * s * (b : ReeF4.Model 0)⁻¹) :
    c.right x = MulAut.conj (c.middle b) (c.right s) := by
  have he : x = (α).right b * s * ((α).right b)⁻¹ := Subtype.ext h
  have hb : c.middle b = c.right ((α).right b) := DFunLike.congr_fun c.compatible b
  rw [he, map_mul, map_mul, map_inv, hb]
  rfl

/-- The original source smallness gives a pair to which the finite model census applies. -/
theorem exists_endpoint_involution_pair (hsmall : c.Small) :
    ∃ x : P, ∃ y : Q, (x : ReeF4.Model 0) ∉ B ∧ (y : ReeF4.Model 0) ∉ B ∧
      x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ (c.left x * c.right y) ^ 8 = 1 := by
  obtain ⟨p, _, _, _, s, ⟨x, rfl⟩, t, ⟨y, rfl⟩, hs2, ht2, hsn, htn, hst, _⟩ :=
    exists_marked_reflection_pair c hsmall
  refine ⟨x, y, ?_, ?_, ?_, ?_, hst⟩
  · intro hx
    apply hsn
    exact ⟨⟨x, hx⟩, rfl⟩
  · intro hy
    apply htn
    exact ⟨⟨y, hy⟩, DFunLike.congr_fun c.compatible ⟨y, hy⟩⟩
  · apply c.left_injective
    rwa [map_pow, map_one]
  · apply c.right_injective
    rwa [map_pow, map_one]

/-- A common Borel conjugator transports a model census pair through both original inclusions. -/
theorem braid_of_pair_conjugate (x r : P) (y s : Q) (b : B)
    (hx : (x : ReeF4.Model 0) = b * r * (b : ReeF4.Model 0)⁻¹)
    (hy : (y : ReeF4.Model 0) = b * s * (b : ReeF4.Model 0)⁻¹)
    (h : (c.left x * c.right y) ^ 8 = 1) : (c.left r * c.right s) ^ 8 = 1 := by
  rw [left_conjugate c b hx, right_conjugate c b hy, ← map_mul, ← map_pow] at h
  exact (MulAut.conj (c.middle b)).injective (h.trans (map_one _).symm)

/-- The literal four-orbit census and its three local exclusions select the canonical pair. -/
theorem standard_braid_of_four_pair_census (hsmall : c.Small)
    (u z : B) (r : P) (s : Q)
    (hcensus : ∀ x y : ReeF4.Model 0, x ∈ P → y ∈ Q → x ∉ B → y ∉ B →
      x ^ 2 = 1 → y ^ 2 = 1 →
      ∃ b : B, ∃ i j : Bool,
        x = b * (if i then (z : ReeF4.Model 0) * r else r) * (b : ReeF4.Model 0)⁻¹ ∧
        y = b * (if j then (u : ReeF4.Model 0)⁻¹ * s * u else s) * (b : ReeF4.Model 0)⁻¹)
    (hshift : (c.left r * (c.middle u)⁻¹ * c.right s * c.middle u) ^ 8 ≠ 1)
    (htwist : (c.middle z * c.left r * c.right s) ^ 8 ≠ 1)
    (hboth : (c.middle z * c.left r * (c.middle u)⁻¹ * c.right s * c.middle u) ^ 8 ≠ 1) :
    (c.left r * c.right s) ^ 8 = 1 := by
  obtain ⟨x, y, hnx, hny, hx2, hy2, hxy⟩ := exists_endpoint_involution_pair c hsmall
  obtain ⟨b, i, j, hxr, hys⟩ := hcensus x y x.property y.property hnx hny
    (congrArg Subtype.val hx2) (congrArg Subtype.val hy2)
  let r' : P := if i then (α).left z * r else r
  let s' : Q := if j then ((α).right u)⁻¹ * s * (α).right u else s
  have hxr' : (x : ReeF4.Model 0) = b * r' * (b : ReeF4.Model 0)⁻¹ := by
    cases i <;> exact hxr
  have hys' : (y : ReeF4.Model 0) = b * s' * (b : ReeF4.Model 0)⁻¹ := by
    cases j <;> exact hys
  have h := braid_of_pair_conjugate c x r' y s' b hxr' hys' hxy
  have hu : c.right ((α).right u) = c.middle u := (DFunLike.congr_fun c.compatible u).symm
  have hz : c.left ((α).left z) = c.middle z := rfl
  cases i <;> cases j
  · exact h
  · apply (hshift ?_).elim
    simpa only [r', s', Bool.false_eq_true, Bool.true_eq, if_false, if_true,
      map_mul, map_inv, hu, mul_assoc] using h
  · apply (htwist ?_).elim
    simpa only [r', s', Bool.false_eq_true, Bool.true_eq, if_false, if_true,
      map_mul, hz, mul_assoc] using h
  · apply (hboth ?_).elim
    simpa only [r', s', Bool.false_eq_true, Bool.true_eq, if_false, if_true,
      map_mul, map_inv, hu, hz, mul_assoc] using h

end CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee.Completion
