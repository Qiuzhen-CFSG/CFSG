module

public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.LeviProjection.MatrixGraph
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification.LeviQuotient

/-!
# Projecting a fixed Ree seed through its middle-node Levi

The proved unique Levi–radical factorization gives an unconditional retraction
of the actual fixed seed onto its actual fixed B₂ Levi. Its kernel is exactly
the root-defined radical, with normality relative to the seed.

For the remaining matrix comparison, pair a representation of the split Levi
with its composite with the exceptional field twist. If the representation
is faithful and its paired range is the explicit generated matrix graph,
its fixed restriction identifies the entire fixed Levi with the diagonal
of that graph. Faithfulness proves that each diagonal element lifts to an
actual fixed element. No descent of arbitrary surjections to fixed points
is invoked.

The final Suzuki projection below remains conditional on the faithful split
representation, its paired range calculation, and the equality of the matrix
diagonal with the Suzuki subgroup. These are genuine remaining calculations;
this module does not yet prove the unconditional Suzuki quotient assertion.

Source: Aschbacher–Smith F.1.12(I)(5), printed p.263 (PDF p.274), used in
2.3.9(7), printed p.526; GLS3 §2.3–2.4 for the fixed Levi decomposition.
-/

@[expose] public noncomputable section

namespace ReeF4.LargeLocalSeeds.SuzukiLeviProjection

open Subgroup BenderSuzuki.MatrixGroups
open LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open MaximalSubgroups.CommutingComponents.CarrierIdentification

variable {m : ℕ}

/-- The actual seed retraction onto its fixed middle-node Levi. -/
def projectionToLevi (d : LocalBlockInput m) :
    standardSeed d .suzuki →* fixedLevi d .suzuki := by
  let := seedRadical_normal d .suzuki
  exact (fixedLeviEquivSeedQuotient d .suzuki).symm.toMonoidHom.comp
    (QuotientGroup.mk' (seedRadical d .suzuki))

theorem projectionToLevi_surjective (d : LocalBlockInput m) :
    Function.Surjective (projectionToLevi d) := by
  let := seedRadical_normal d .suzuki
  exact (fixedLeviEquivSeedQuotient d .suzuki).symm.surjective.comp
    (QuotientGroup.mk'_surjective _)

theorem projectionToLevi_ker (d : LocalBlockInput m) :
    (projectionToLevi d).ker = seedRadical d .suzuki := by
  let := seedRadical_normal d .suzuki
  ext x
  change (fixedLeviEquivSeedQuotient d .suzuki).symm
    (QuotientGroup.mk' (seedRadical d .suzuki) x) = 1 ↔ x ∈ seedRadical d .suzuki
  rw [map_eq_one_iff _ (fixedLeviEquivSeedQuotient d .suzuki).symm.injective]
  exact QuotientGroup.eq_one_iff x

/-- The retraction really restricts to the identity on the fixed Levi. -/
@[simp] theorem projectionToLevi_inclusion (d : LocalBlockInput m)
    (x : fixedLevi d .suzuki) :
    projectionToLevi d (fixedLeviInclusion d .suzuki x) = x := by
  let := seedRadical_normal d .suzuki
  change (fixedLeviEquivSeedQuotient d .suzuki).symm
    (QuotientGroup.mk' (seedRadical d .suzuki) (fixedLeviInclusion d .suzuki x)) = x
  rw [← fixedLeviEquivSeedQuotient_apply]
  exact (fixedLeviEquivSeedQuotient d .suzuki).symm_apply_apply x

/-- Restrict the supplied exceptional field twist to the full split B₂ Levi. -/
def splitTwist (d : LocalBlockInput m) : splitLevi m .suzuki →* splitLevi m .suzuki where
  toFun x := ⟨d.twist x.val, (splitLevi_twist d .suzuki).le (mem_map_of_mem _ x.property)⟩
  map_one' := Subtype.ext (map_one d.twist)
  map_mul' x y := Subtype.ext (map_mul d.twist x.val y.val)

/-- The graph of a representation and its composite with the actual twist. -/
def pairedMap (d : LocalBlockInput m) (f : splitLevi m .suzuki →* MatrixGroup m) :
    splitLevi m .suzuki →* MatrixGroup m × MatrixGroup m :=
  f.prod (f.comp (splitTwist d))

/-- Forget fixedness, retaining the same actual split Levi element. -/
def forgetToSplitLevi (d : LocalBlockInput m) :
    fixedLevi d .suzuki →* splitLevi m .suzuki where
  toFun x := ⟨x.val.val, x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem forgetToSplitLevi_injective (d : LocalBlockInput m) :
    Function.Injective (forgetToSplitLevi d) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : splitLevi m .suzuki => z.val) h

@[simp] theorem splitTwist_forget (d : LocalBlockInput m) (x : fixedLevi d .suzuki) :
    splitTwist d (forgetToSplitLevi d x) = forgetToSplitLevi d x :=
  Subtype.ext x.val.property

/-- A genuinely fixed split Levi element gives an element of the fixed Levi. -/
def ofSplitFixed (d : LocalBlockInput m) (x : splitLevi m .suzuki)
    (hx : splitTwist d x = x) : fixedLevi d .suzuki :=
  ⟨⟨x.val, congrArg Subtype.val hx⟩, x.property⟩

@[simp] theorem forget_ofSplitFixed (d : LocalBlockInput m)
    (x : splitLevi m .suzuki) (hx : splitTwist d x = x) :
    forgetToSplitLevi d (ofSplitFixed d x hx) = x := rfl

/-- A split representation with the prescribed graph restricts to the matrix diagonal. -/
def toPairedDiagonal (d : LocalBlockInput m) (f : splitLevi m .suzuki →* MatrixGroup m)
    (hgraph : (pairedMap d f).range = pairedSubgroup m) :
    fixedLevi d .suzuki →* pairedDiagonal m where
  toFun x := ⟨f (forgetToSplitLevi d x), by
    change (f (forgetToSplitLevi d x), f (forgetToSplitLevi d x)) ∈ pairedSubgroup m
    rw [← hgraph]
    exact ⟨forgetToSplitLevi d x,
      Prod.ext rfl (congrArg f (splitTwist_forget d x))⟩⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

theorem toPairedDiagonal_injective (d : LocalBlockInput m)
    (f : splitLevi m .suzuki →* MatrixGroup m) (hf : Function.Injective f)
    (hgraph : (pairedMap d f).range = pairedSubgroup m) :
    Function.Injective (toPairedDiagonal d f hgraph) := by
  intro x y h
  exact forgetToSplitLevi_injective d (hf (congrArg Subtype.val h))

/-- Faithfulness forces every lift of a diagonal matrix to be fixed by the twist. -/
theorem toPairedDiagonal_surjective (d : LocalBlockInput m)
    (f : splitLevi m .suzuki →* MatrixGroup m) (hf : Function.Injective f)
    (hgraph : (pairedMap d f).range = pairedSubgroup m) :
    Function.Surjective (toPairedDiagonal d f hgraph) := by
  rintro ⟨a, ha⟩
  change (a, a) ∈ pairedSubgroup m at ha
  rw [← hgraph] at ha
  obtain ⟨x, hx⟩ := ha
  have h1 : f x = a := congrArg Prod.fst hx
  have h2 : f (splitTwist d x) = a := congrArg Prod.snd hx
  have hfixed : splitTwist d x = x := hf (h2.trans h1.symm)
  refine ⟨ofSplitFixed d x hfixed, ?_⟩
  apply Subtype.ext
  exact h1

/-- A faithful split comparison identifies the entire fixed Levi with the diagonal. -/
def fixedLeviEquivPairedDiagonal (d : LocalBlockInput m)
    (f : splitLevi m .suzuki →* MatrixGroup m) (hf : Function.Injective f)
    (hgraph : (pairedMap d f).range = pairedSubgroup m) :
    fixedLevi d .suzuki ≃* pairedDiagonal m :=
  MulEquiv.ofBijective (toPairedDiagonal d f hgraph)
    ⟨toPairedDiagonal_injective d f hf hgraph,
      toPairedDiagonal_surjective d f hf hgraph⟩

/-- Conditional matrix identification, retaining the two independent calculations. -/
def fixedLeviEquivOfMatrixGraph (d : LocalBlockInput m)
    (f : splitLevi m .suzuki →* MatrixGroup m) (hf : Function.Injective f)
    (hgraph : (pairedMap d f).range = pairedSubgroup m)
    (hdiag : pairedDiagonal m = SuzukiMatrixSubgroup m) :
    fixedLevi d .suzuki ≃* SuzukiMatrixGroup m :=
  (fixedLeviEquivPairedDiagonal d f hf hgraph).trans (MulEquiv.subgroupCongr hdiag)

/-- Compose the actual Levi retraction with the conditional matrix identification. -/
def projectionOfMatrixGraph (d : LocalBlockInput m)
    (f : splitLevi m .suzuki →* MatrixGroup m) (hf : Function.Injective f)
    (hgraph : (pairedMap d f).range = pairedSubgroup m)
    (hdiag : pairedDiagonal m = SuzukiMatrixSubgroup m) :
    standardSeed d .suzuki →* SuzukiMatrixGroup m :=
  (fixedLeviEquivOfMatrixGraph d f hf hgraph hdiag).toMonoidHom.comp (projectionToLevi d)

theorem projectionOfMatrixGraph_surjective (d : LocalBlockInput m)
    (f : splitLevi m .suzuki →* MatrixGroup m) (hf : Function.Injective f)
    (hgraph : (pairedMap d f).range = pairedSubgroup m)
    (hdiag : pairedDiagonal m = SuzukiMatrixSubgroup m) :
    Function.Surjective (projectionOfMatrixGraph d f hf hgraph hdiag) :=
  (fixedLeviEquivOfMatrixGraph d f hf hgraph hdiag).surjective.comp
    (projectionToLevi_surjective d)

theorem projectionOfMatrixGraph_ker (d : LocalBlockInput m)
    (f : splitLevi m .suzuki →* MatrixGroup m) (hf : Function.Injective f)
    (hgraph : (pairedMap d f).range = pairedSubgroup m)
    (hdiag : pairedDiagonal m = SuzukiMatrixSubgroup m) :
    (projectionOfMatrixGraph d f hf hgraph hdiag).ker = seedRadical d .suzuki := by
  rw [← projectionToLevi_ker d]
  ext x
  change fixedLeviEquivOfMatrixGraph d f hf hgraph hdiag (projectionToLevi d x) = 1 ↔
    projectionToLevi d x = 1
  exact map_eq_one_iff _ (fixedLeviEquivOfMatrixGraph d f hf hgraph hdiag).injective

end ReeF4.LargeLocalSeeds.SuzukiLeviProjection
