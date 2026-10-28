module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelCartanCoordinates
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityTwo.CartanInvolutions

/-!
# Four binary reflection coordinates on the original eight-field component

The actual ComponentLift and EightImageRow supply a Cartan-aligned order-six
pair. The native involution equations and one common torus conjugation reduce
its seven binary coordinates and two torus parameters to four binary scalars.
Both endpoint maps are unchanged. The relation and exact order persist in the
actual completion and in G through the literal generated-subgroup inclusion;
the normalizer statements retain the same marked order-seven subgroup.

The matching native sixth-power equation, ambient recognition and original
Borel contradiction remain open. The genuine earlier MarkedTriality premise
is explicit, with its original inclusion maps and commuting squares.
Source: Aschbacher--Smith F.4.15--17 and14.3.6,15, pp.281--283,991,994
(`refs/quasithin.pdf`).
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

/-- The actual reflection pair, on the literal component and unchanged endpoint
markings, now has only four binary parameters and no torus parameters. -/
theorem source_eight_marked_four_coordinate_involutions
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    let c := EightLargeParabolic.markedCompletion r
    let Q := (ChapterF.SourceCompletion.TrialityTwo.Completion.borelTorus.map c.middle).map
      ((K ⊔ (T : Subgroup G)) ⊔ EightLargeParabolic.secondParabolic T M Mc
        (K ⊔ (T : Subgroup G))).subtype
    Nat.card Q = 7 ∧
    ∃ p q b j : fixedField P,
      let s := endpointWord .arms ![p,p,q] 0 1
      let t := endpointWord .central (Pi.single 0 b) ![b,j,(1+b)*j] 1
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
  obtain ⟨hQ,a,b,d,z,w,hs,ht,hsout,htout,hpow,ho,_⟩ :=
    source_eight_marked_endpoint_coordinates hG T hempty hM hu hmany hcard e hK h8 r
  let c := EightLargeParabolic.markedCompletion r
  obtain ⟨p,q,b,j,hs,ht,hsout,htout,hpow,ho⟩ :=
    ChapterF.SourceCompletion.TrialityTwo.Completion.reduce_involution_coordinates c a b d z w hs ht hsout htout hpow ho
  refine ⟨hQ,p,q,b,j,hs,ht,hsout,htout,hpow,ho,congrArg Subtype.val hpow,?_,?_,?_,?_,?_⟩
  · exact (Subgroup.orderOf_coe _).trans ho
  · exact le_normalizer_map _ ⟨_,ChapterF.SourceCompletion.TrialityTwo.Completion.left_coordinate_normalizes c _ _ _,rfl⟩
  · exact le_normalizer_map _ ⟨_,ChapterF.SourceCompletion.TrialityTwo.Completion.right_coordinate_normalizes c _ _ _,rfl⟩
  · exact endpointWord_normalizes .arms _ _ _
  · exact endpointWord_normalizes .central _ _ _

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
