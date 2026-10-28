module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.TerminalSource.PairMarking
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.ThreeDimensional
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.TerminalSource.HexacodeMarking.Geometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.TerminalSource.HexacodeMarking.FullWeightExclusion
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.TerminalSource.HexacodeMarking.TwoCoreLifts
public import Theory.Representation.HexacodeAction.PairGeometry

/-!
# Assembly of the hexacode parabolic marking

For a faithful actor containing the even hexacode cover, an F₄-point whose
stabilizer has intrinsic two-core of order four is a double-zero coordinate
pair plane: the full-weight orbit is excluded by its A₅ stabilizer quotient
with odd kernel. The actual two-core then supplies two double-transposition
lifts. Relabeling the coordinate action and its equivariant pair-coset map
places these lifts at the standard generators and constructs the marking.

This proves the intrinsic geometric bridge for the alternative-section
argument for Aschbacher–Smith 13.8.21(2), printed p.956 (PDF p.973), combined
manuscript of 1 March 2004. The source-theorem assembly must identify its
actual actor and parabolic with this embedded hexacode point stabilizer.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.TerminalSource.HexacodeMarking
open Atlas.Codes
open Representation.Hexacode
open BinaryPermutation.SixPairsQuadratic (Pair pairPerm pairHom first second)

variable {A : Type*} [Group A]

/-- Conditional assembly: once the intrinsic two-core supplies its two marked
lifts, the geometric orbit map constructs every field of `Pairs.Marking`.
The exclusion of full-weight points and construction of the lifts are separate
obligations; this theorem does not claim to discharge them. -/
theorem nonempty_marking_of_pair_lifts (e : A →* HexAutomorphisms)
    (heven : hexSign.ker ≤ e.range) (D : Submodule F hexacode)
    (s : Pair) (hs : D.restrictScalars (ZMod 2) = zeroPairPlane s)
    (r : Equiv.Perm (Fin 6)) (a b : A)
    (ha : a ∈ (pointStabilizer e D).pCoreIn 2)
    (hb : b ∈ (pointStabilizer e D).pCoreIn 2)
    (hfirst : r * coordinate e a * r⁻¹ = first)
    (hsecond : r * coordinate e b * r⁻¹ = second) :
    Nonempty (Pairs.Marking (pointStabilizer e D)) := by
  let c := cosetsOfZeroPair e heven D s hs
  refine ⟨{
    coordinate := (MulAut.conj r).toMonoidHom.comp (coordinate e)
    coversAlternating := conjugate_coversAlternating _ (coordinate_coversAlternating e heven) r
    cosets := c.trans (pairPerm r)
    equivariant := ?_
    firstLift := a
    secondLift := b
    first_mem := ha
    second_mem := hb
    coordinate_first := hfirst
    coordinate_second := hsecond }⟩
  intro g q
  change pairPerm r (c (g • q)) = pairPerm (r * coordinate e g * r⁻¹) (pairPerm r (c q))
  rw [show c (g • q) = pairPerm (coordinate e g) (c q) from
    cosetsOfZeroPair_equivariant e heven D s hs g q]
  change pairHom r (pairHom (coordinate e g) (c q)) =
    pairHom (r * coordinate e g * r⁻¹) (pairHom r (c q))
  rw [map_mul, map_mul, map_inv]
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply]

/-- The genuine stabilizer of an F₄-point has the fifteen-pair marking when
its intrinsic two-core has order four. Both the pair selection and the two
marked lifts are constructed from these hypotheses. -/
theorem nonempty_marking_of_twoCore_card_eq_four [Finite A]
    (e : A →* HexAutomorphisms) (he : Function.Injective e)
    (heven : hexSign.ker ≤ e.range) (D : Submodule F hexacode)
    (hD : Module.finrank F D = 1)
    (hfour : Nat.card ((pointStabilizer e D).pCoreIn 2) = 4) :
    Nonempty (Pairs.Marking (pointStabilizer e D)) := by
  obtain ⟨s, hs⟩ := (fieldPoint_full_or_pair D hD).resolve_left
    (not_fullWeight_of_twoCore_card_eq_four e he heven D hfour)
  obtain ⟨r, a, b, ha, hb, hfirst, hsecond⟩ :=
    exists_pair_twoCore_lifts e he heven D s hs hfour
  exact nonempty_marking_of_pair_lifts e heven D s hs r a b ha hb hfirst hsecond

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.TerminalSource.HexacodeMarking
