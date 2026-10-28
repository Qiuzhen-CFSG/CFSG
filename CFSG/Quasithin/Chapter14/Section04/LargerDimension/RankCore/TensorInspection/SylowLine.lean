module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.Action
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.SingularExclusions
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.TensorInspection.AlternatingCore
public import Theory.Representation.BinaryPermutation.FiveTensorFixedLine

/-!
# The Sylow-fixed marked line in the S₅ × S₃ tensor alternative

Map the actual Sylow subgroup of H through H/O₂(H) and the model
isomorphism. Equality of the conjugated central-quotient classes gives
fixedness of the marked vector by this model Sylow subgroup. Noncentrality
makes the vector nonzero, so the fixed-line calculation supplies nonzero
pure tensor coordinates with singular first factor. Low moved rank then
identifies a pure transposition, whose displacement excludes this vector.

This discharges the singular-coordinate and displacement-exclusion steps
of 14.4.6(a), retaining only the earlier-source fixedness of the literal
class of s in U/Z(U). The parent tensor inspection owns assembly of that
fixedness premise and the other tensor alternatives.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Lemma 14.4.6(a), printed p.1008.
-/

public section

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore
open BinaryPermutation Subgroup TensorProduct
variable {H V : Type*} [Group H] [Finite H] (U : Subgroup H) [U.Normal]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- The literal Sylow-fixed central-quotient class has singular pure tensor
coordinates. The Sylow subgroup is mapped through H/O₂(H) and the given model
isomorphism; no Sylow marking or tensor coordinates for s are assumed. -/
theorem SourceAction.tensor_sylow_fixed_coordinates
    (d : SourceAction H U V)
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3))
    (f : V ≃ₗ[ZMod 2] FiveTensorLowRank.Space)
    (hf : ∀ a v, f (d.representation a v) = FiveTensorLowRank.action (e a) (f v))
    (T : Sylow 2 H) (s : U) (hs : s ∉ center U)
    (hfixed : ∀ t ∈ T,
      QuotientGroup.mk' (center U) (MulAut.conjNormal t s) =
        QuotientGroup.mk' (center U) s) :
    ∃ u : core (Fin 5), ∃ w : core (Fin 3),
      u ≠ 0 ∧ w ≠ 0 ∧ FiveGeometry.form u = 0 ∧
        f (d.vector s) = u ⊗ₜ[ZMod 2] w := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let P := T.mapSurjective hq
  apply FiveTensorFixedLine.sylow_fixed_coordinates P (f (d.vector s))
  · intro h
    have hv : d.vector s = 0 := f.injective (h.trans (map_zero f).symm)
    have he : d.coordinates (QuotientGroup.mk' (center U) s) = 1 := hv
    exact hs ((QuotientGroup.eq_one_iff s).mp (d.coordinates.map_eq_one_iff.mp he))
  · intro g hg
    obtain ⟨t, ht, rfl⟩ := hg
    change FiveTensorLowRank.action (e (QuotientGroup.mk' (pCore 2 H) t))
      (f (d.vector s)) = f (d.vector s)
    rw [← hf, ← d.conjugation]
    exact congrArg (fun c => f (d.coordinates c).toAdd) (hfixed t ht)

/-- Source 14.4.6(a) under its earlier-source central-quotient fixedness input:
every nonidentity actor of moved rank at most two is a pure transposition, has
rank two, and its displacement does not contain the literal marked image Ṽ₂. -/
theorem SourceAction.tensor_sylow_fixed_exclusion
    (d : SourceAction H U V)
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3))
    (f : V ≃ₗ[ZMod 2] FiveTensorLowRank.Space)
    (hf : ∀ a v, f (d.representation a v) = FiveTensorLowRank.action (e a) (f v))
    (T : Sylow 2 H) (V₂ : Subgroup H) (s : U)
    (hs : (s : H) ∈ V₂) (hne : s ∉ center U)
    (hfixed : ∀ t ∈ T,
      QuotientGroup.mk' (center U) (MulAut.conjNormal t s) =
        QuotientGroup.mk' (center U) s)
    (a : H ⧸ pCore 2 H) (ha : a ≠ 1) (hr : d.movedRank a ≤ 2) :
    (∃ i j : Fin 5, i ≠ j ∧ e a = (Equiv.swap i j, 1)) ∧
      d.movedRank a = 2 ∧ ¬ d.image V₂ ≤ d.moved a := by
  obtain ⟨⟨i, j, hij, he⟩, hrank⟩ := d.tensor_symmetric_lowRank U e f hf a ha hr
  obtain ⟨u, w, hu, hw, hsing, hmark⟩ :=
    d.tensor_sylow_fixed_coordinates U e f hf T s hne hfixed
  refine ⟨⟨i, j, hij, he⟩, hrank, ?_⟩
  apply d.tensor_line_not_le_moved U (coreRepresentation (Fin 3)) f a i j
    (fun v => (hf a v).trans ?_) V₂ s hs u hu hsing w hw hmark
  rw [he]
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore
