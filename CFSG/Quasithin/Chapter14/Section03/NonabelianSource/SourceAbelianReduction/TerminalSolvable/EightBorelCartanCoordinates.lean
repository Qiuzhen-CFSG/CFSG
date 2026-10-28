module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelCartan
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityTwo.CartanCoordinates

/-!
# Native endpoint coordinates on the literal eight-field component

Apply the native Bruhat and coprime fixed-coset calculations to the same
Cartan-aligned pair extracted from ComponentLift and EightImageRow. Its arms
preimage has one three-coordinate long-root correction, and its central
preimage has one leading binary scalar and a three-coordinate correction.
Both retain a native torus factor. The product still has order six in the
actual completion and the original G, through the literal inclusion.

This reduces the outstanding matching native relation to explicit root words.
Recognition and the Borel contradiction remain open. The genuine earlier
MarkedTriality premise retains both original commuting squares.
Source: Aschbacher--Smith F.4.15--17 and14.3.6,15, pp.281--283,991,994.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Subgroup Theory.GroupTheory
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.ConcreteBruhat _root_.Triality.Standard.BinaryTorusEndpoints
local notation "P" => binaryParameters 1 Nat.zero_lt_one
variable {G : Type*} [Group G] [Finite G]
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    {F : InvariantFlag T (rankTwoSeed T M) 2} {g : G} {K : Subgroup G}
include hG hempty hM hu hmany hcard e

/-- Exact root coordinates for the same actual order-six pair on the original
component, retaining its native and ambient markings and the original torus. -/
theorem source_eight_marked_endpoint_coordinates
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    let c := EightLargeParabolic.markedCompletion r
    let Q := (ChapterF.SourceCompletion.TrialityTwo.Completion.borelTorus.map c.middle).map
      ((K ⊔ (T : Subgroup G)) ⊔ EightLargeParabolic.secondParabolic T M Mc
        (K ⊔ (T : Subgroup G))).subtype
    Nat.card Q = 7 ∧
    ∃ a : Fin 3 → fixedField P, ∃ b : fixedField P,
      ∃ d : Fin 3 → fixedField P, ∃ z w : torus P,
      let s := endpointWord .arms a 0 z
      let t := endpointWord .central (Pi.single 0 b) d w
      s^2=1 ∧ t^2=1 ∧ c.left s∉c.middle.range ∧ c.right t∉c.middle.range ∧
        (c.left s*c.right t)^6=1 ∧ orderOf (c.left s*c.right t)=6 ∧
        ((c.left s : G)*(c.right t : G))^6=1 ∧
        orderOf ((c.left s : G)*(c.right t : G))=6 ∧
        (c.left s : G) ∈ normalizer (Q : Set G) ∧
        (c.right t : G) ∈ normalizer (Q : Set G) ∧
        ChapterF.SourceCompletion.TrialityTwo.modelCompletion.left s ∈
          normalizer (torus P : Set (Carrier P)) ∧
        ChapterF.SourceCompletion.TrialityTwo.modelCompletion.right t ∈
          normalizer (torus P : Set (Carrier P)) := by
  obtain ⟨hQ,s,t,hs,ht,hsout,htout,hpow,ho,hamb,hoa,hsQ,htQ,hsN,htN⟩ :=
    source_eight_marked_torus_endpoint_involutions hG T hempty hM hu hmany hcard e hK h8 r
  obtain ⟨a,b,d,z,w,he,hf⟩ :=
    ChapterF.SourceCompletion.TrialityTwo.Completion.torus_endpoint_coordinates
      (EightLargeParabolic.markedCompletion r) s t hsout htout hsN htN
  refine ⟨hQ,a,b,d,z,w,?_⟩
  dsimp only
  rw [←he,←hf]
  exact ⟨hs,ht,hsout,htout,hpow,ho,hamb,hoa,hsQ,htQ,hsN,htN⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
