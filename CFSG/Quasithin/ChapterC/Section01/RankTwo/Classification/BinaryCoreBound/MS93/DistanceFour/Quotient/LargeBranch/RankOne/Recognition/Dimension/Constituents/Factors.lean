module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Interface
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Factors.OneFactor
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Factors.Generation

/-!
# The two natural constituents of the supplied starred module

The source radius bound and V_alpha-star intersect B_alpha = Z_alpha give
dimension at most six. The fixed space vanishes. The literal Y-fixation
estimates put the edge-star image in the first parabolic's fixed space;
odd-index averaging and conjugate generation give full commutator generation.
The existing binary SL3 irreducible catalogue then gives a natural head
whose kernel is fixed or natural. Transitivity on a single natural factor
would make V_alpha-star elementary abelian and V_alpha abelian, so the
fixed-kernel case is impossible.

The result supplies actual equivariant coordinates on a subrepresentation
and its literal quotient. The two intersection-case bounds in Estimates
are unnecessary for this intermediate conclusion, which permits either
natural orientation. No FF witness, split extension, canonical seed, or
starred index is assumed. Constructing natural rank-one copies is separate.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.12)(5), last paragraph of printed p.911 continuing onto p.912,
using (4.6.9)--(4.6.10) on p.908 and (4.6.12)(1)--(2) on p.910.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
open AbelianCore.QuotientRecognition.ExtensionControl
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The source estimates force two actual natural SL3(2) constituents on the
supplied starred subspace, with the literal quotient action. The stronger
averaging route does not require the escape or intersection-case bounds. -/
theorem twoNaturalFactors_of_estimates (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hs : ¬ s.SmallIntersection)
    (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (_hf : Seed.Compatible f s)
    (_hescape : ¬ d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle)
    (hest : Estimates d f s) :
    Nonempty (TwoNaturalFactors (geometry := geometry) d) := by
  have hfull := star_full_of_estimates common radius hb s hbc d f hest
  have hnot := star_not_naturalOrDual common radius hb s hs d
  let ρ := (starRepresentation (geometry := geometry) d).toRepresentation
  rcases subsingleton_or_nontrivial ((starRepresentation (geometry := geometry) d).toSubmodule) with hsub | hnt
  · let : Subsingleton ((starRepresentation (geometry := geometry) d).toSubmodule) := hsub
    have hi := star_faithful common radius hb d s hs
    let : Subsingleton SL := ⟨fun g k => hi (by apply LinearMap.ext; intro v; exact Subsingleton.elim _ _)⟩
    have hc : Nat.card SL = 1 := Nat.card_unique
    rw [Matrix.PSL3Two.card_SL] at hc
    contradiction
  · let : Nontrivial ((starRepresentation (geometry := geometry) d).toSubmodule) := hnt
    obtain ⟨N, hupper, hlower⟩ := exists_natural_head ρ
      (star_finrank_le_six common radius d f s hest) hfull
    rcases hlower with hfixed | hnatural
    · have hN : N.toSubmodule = ⊥ := hfixed.trans (star_fixed_eq_bot common radius d)
      let q : ρ.IntertwiningMap N.quotientRepresentation := {
        toLinearMap := N.toSubmodule.mkQ
        isIntertwining' _ := rfl }
      have hq : Function.Bijective q := by
        refine ⟨?_, N.toSubmodule.mkQ_surjective⟩
        apply LinearMap.ker_eq_bot.mp
        change LinearMap.ker N.toSubmodule.mkQ = ⊥
        rw [Submodule.ker_mkQ, hN]
      let e := q.ofBijective hq
      exfalso
      apply hnot
      rcases hupper with hu | hu
      · obtain ⟨u⟩ := hu
        exact Or.inl ⟨e.trans u⟩
      · obtain ⟨u⟩ := hu
        exact Or.inr ⟨e.trans u⟩
    · exact ⟨⟨N, hnatural, hupper⟩⟩
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
