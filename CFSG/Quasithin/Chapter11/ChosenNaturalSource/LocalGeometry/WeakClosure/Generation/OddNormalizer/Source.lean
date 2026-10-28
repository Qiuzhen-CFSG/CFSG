module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Normalizer.Recognition
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.CompleteCover
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OrdinaryCoverAssembly
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.NormalizerCoverAssembly
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.PureSixtyFour
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.MovedNaturalCenter
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.MovedNaturalNormalizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.MovedNaturalOrbit
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.MovedJankoEvenIndex
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.MovedJankoPlacements
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.MovedJankoCentralizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.MovedNormalizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OuterOddG2
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OuterSymplecticSix
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OuterRemaining
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OuterJankoThree
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.MovedRudvalis
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OuterUnitaryFive
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OuterSymplectic
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OddFour
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OuterUnitaryFour
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OddG2
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.PlacedModels
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.FieldFourModule
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.MovedCases
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.FinalOrdinary
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.SelectedNormal

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.PushingUpReduction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.ModelReduction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.ResidualCases
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Hall

/-!
# The two remaining nonbinary odd-normalizer source configurations

An outside elementary odd normalizer yields either the actual C.2.8
pushing-up configuration or a component of N(A) moved by the original V.
All setup, odd-core and exceptional-quotient premises are discharged in
the imported modules. The constrained pushing-up branch is now excluded
using the actual full SL₃(4) quotient and its binary degree obstruction.
The ordinary branch retains only J₄ and Ru central quotients and forces
the original full quotient to be SL₃(4), retaining its cubic center.
Moved components with Theorem C quotients are normal, contain the original
V and odd-actor residual, and have centralizer equal to the ambient odd core.
The moved C-model branch also reduces to J₄ and Ru and forces the original
full SL₃(4) quotient. In both field-four branches the original central fixed
subspace vanishes and |V| = 64. Both branches retain the product-order obstruction
from the original module and full covering quotient. The final reduction applies this to the literal
elementary Hall kernel, retaining AT=TA and residual uniqueness.

The action refinement treats every B-model: inner action places the original
module and full residual and applies the full B-catalogue sieve. This excludes
all additional characteristic-two rows, including PSU₄(2ⁿ) and PSU₅(4), and
excludes all odd models by their actual elementary ranks. Every placed
B-component therefore has J₄ or Ru central quotient and the original full
SL₃(4) actor, with C_V(L)=1 and |V|=64. An outer action instead supplies
the original simple central quotient as an actual section of Out(K), outside all C, alternating and odd PSL₂ models.

The Sylow Frattini order bounds and the unitary-five quotient pair now force
SL₃(4) even in the outer-action branch. Thus every failure has C_V(L)=1 and
|V|=64 for the original V. Normalizer control and the actual Hall conclusion
are proved for all larger fields and every nonbinary symplectic or G₂ row.

The Rudvalis cubic-centralizer calculation also excludes Ru in the moved
configuration. Thus an inner moved action now has J₄ central quotient;
the ordinary pushing-up configuration retains its separate J₄/Ru alternatives.
The J₃ outer section is excluded through its actual Sylow Frattini action,
so J₃ is excluded on the same moved component in both actions.

Odd ternary linear and unitary rows now have Sylow Frattini quotient at most
16, and a native order-eight McL word bounds its quotient by 32. Both therefore
exclude the required PSL₃(4) outer section. The remaining outer models are
Sp₆(2), odd PSp₄ and G₂, and the specified Fermat-linear and Mersenne-unitary
four-dimensional rows. Their actual model identifications are retained.

The explicit binary symplectic matrices now bound its Sylow Frattini quotient
by 32. This excludes Sp₆(2) in both actions, leaving only the four
odd-characteristic outer rows, with the original component identifications.

The rank-three degree-four argument gives the same Frattini bound for the
remaining odd classical rows and odd-prime G₂. Thus every actual outer
section is excluded. The final endpoint places the original residual and V
inside a normal component with J₄ central quotient and centralizer equal
to the ambient odd core. It applies to the literal Hall kernel.

The actual moved residual now retains its full projected normalizer, equal to
its original component intersection with N_G(L). Every nontrivial two-subgroup
normalized by that residual has its full normalizer inside the residual
normalizer. The native two-class involution-centralizer calculation therefore
makes the residual centralizer odd, excluding every involution-centralizer
placement. These conclusions are applied to the same literal Hall kernel.

The original module has a nonzero elementary, fully moved image in that
residual's two-core. Two-local normalizer control identifies O₂(N(X)) as a
radical with full normalizer N(X), and makes N(X) a maximal two-local.
The full cover and odd centralizer exclude all four specified native local
placements. The checked full-Sylow catalogue further proves that this exact
N(X) has even index in J₄: every full-Sylow local would supply an excluded
Mathieu placement or a nonzero small subgroup in the residual centralizer.
The remaining even-index placement is unproved; no assertion classifying
arbitrary J₄ subgroups is substituted for it.

The unchanged V injects into the same component central quotient. Its literal
image has order 64, and the same residual conjugates any two nonidentity
points. Thus all 63 nonidentity points lie in a single native J₄ involution
class. This natural-orbit geometry is retained in the Source and Hall witnesses.

The original module is now exactly Ω₁(Z(O₂(N(X)))). The proof uses the
full cubic center to split any extra central elementary summand and the
small-action bound to place it in the residual's odd centralizer. The radical
is self-centralizing, so an ambient Sylow-center involution lies in this exact
module. It is in native class 2A, and residual transitivity excludes the entire
2B-pure alternative. The remaining local is therefore the full even-index
normalizer of this particular 2A-pure elementary radical center of order64.
The native counterexample in PureSixtyFour constructs a 2A-pure elementary
subgroup of order64 inside the Mathieu kernel. Thus purity and order alone
do not exclude this case; the remaining argument must use the original full
covering action and radical-normalizer geometry. This counterexample does
not instantiate those additional source constraints.

The final conditional endpoint applies the uniform native elementary-normalizer
cover to this original V image. The full normalizer equality eliminates the
moved-inner disjunct, and the shared ordinary full-W theorem eliminates the
remaining pushing-up witness. This proves OddKernelNormalizer and faithfulness
of the literal Hall actor conditional on those two independent inputs.
The cover includes the actual embedded third local and its L₅(2) quotient.
The shared ordinary proof now supplies that second input under the same
uniform cover. The final elementary-cover endpoints therefore retain only
the native cover and its embedded quotient, with full W still preserved.
The native-four-local endpoints below now instantiate that quotient with the
proved full normalizer of the native elementary F. Its intrinsic SL₅(2)
quotient followed by the canonical PSL₅(2) projection removes the quotient
premise, leaving just the uniform cover for the fixed four native locals.

Unconditional field-four normalizer control remains open. The native cover
belongs to qt-model-j4-elementary-normalizer-cover, its intrinsic symmetry
to qt-model-j4-large-center-radicals, and the ordinary full-W theorem to
qt-d-1222-natural-point-fixed-summand. Their final discharge stays with
qt-d-1222-natural-odd-kernel-normalizer; the previous unconditional APIs
retain their statements and no conclusion is added to the source hypotheses.
Final 11.2.1 assembly remains with qt-d-1222-natural-weak-closure-source.

Source: Aschbacher--Smith, 4.4.3--12, pp.619--623, and 11.2.1, pp.766--767.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- The two remaining configurations in the original 4.4.3 argument.
These are outputs of the reduction, not assumptions of normalizer control. -/
def SourceCase (L V A : Subgroup G) : Prop :=
  PushingUpCase L V A ∨
    (∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
      (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) ∧
      V.subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))))

/-- An outside elementary odd normalizer supplies an actual pushing-up
configuration or an actual component moved by the unchanged V. -/
theorem outside_source_case {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    SourceCase L V A := by
  by_cases hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))
  · exact Or.inr (component_of_core_eq_bot D S hp ho A hne hAe hA
      (oddNormalizer_reduction_of_cover_uniqueness D A hu hout).2)
  · exact Or.inl (pushingUp_configuration D S hA (odd_card_of_elementary hp ho A hAe) hu)

/-- Failure of the exact requested specialization yields these source cases.
No normalizer conclusion or residual uniqueness is used as an input. -/
theorem failure_source_case
    (hnot : ¬ OddKernelNormalizer (T := T) (L := L) (V := V)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧ SourceCase L V A := by
  unfold OddKernelNormalizer at hnot
  push Not at hnot
  obtain ⟨p,hp,ho,A,hne,he,hA,hperm,hout⟩ := hnot
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,outside_source_case D S hp ho A hne he hA hout⟩

open ChapterE ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan

/-- The original 11.2.1 Hall kernel supplies the same source configurations,
with its actual elementary actor, ambient normalizer and setwise product. -/
theorem hall_kernel_source_case {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H)
    (hk : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧ SourceCase L V A := by
  obtain ⟨p,A,hp,ho,hne,he,hA,hperm,hout⟩ := hall_kernel_escape D S hH hlarge hP d hm hk
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,outside_source_case D S hp ho A hne he hA hout⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer


public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The remaining source cases after excluding contained generalized Fitting.
The pushing-up alternative now includes an actual escaping C-component and,
in its constrained branch, the literal C.2.7 input and star-model marking. -/
def ComponentSourceCase (L V A : Subgroup G) : Prop :=
  PushingUpComponentCase L V A ∨
    (∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
      (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) ∧
      V.subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))))

include D S
/-- Every actual outside odd normalizer gives a component in one of the two
source ambient groups. No contained-Fitting or component-selection input remains. -/
theorem outside_component_source_case {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    ComponentSourceCase L V A := by
  rcases outside_source_case D S hp ho A hne hAe hA hout with hpush | hcomp
  · exact Or.inl (pushingUp_component_case D S hpush)
  · exact Or.inr hcomp

open ChapterE ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan

/-- The exact 11.2.1 Hall kernel reaches the escaping-component analysis.
Exclusion of these genuine components, and hence final normalizer control,
remains with qt-d-1222-natural-odd-kernel-normalizer; final generation assembly
remains with qt-d-1222-natural-weak-closure-source. -/
theorem hall_kernel_component_source_case {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H)
    (hk : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧ ComponentSourceCase L V A := by
  obtain ⟨p,A,hp,ho,hne,he,hA,hperm,hout⟩ := hall_kernel_escape D S hH hlarge hP d hm hk
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_component_source_case D S hp ho A hne he hA hout⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The remaining cases after the nonbinary constrained-model exclusions.
The pushing-up component is normal in H; it is ordinary or has literal
star image SL₅(2). The full covering quotient and original module remain. -/
def ReducedSourceCase (L V A : Subgroup G) : Prop :=
  PushingUpReducedCase L V A ∨
    (∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
      (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) ∧
      V.subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))))

include D S
/-- Every outside odd normalizer reaches the remaining ordinary, binary-five,
or moved-normalizer-component analysis. -/
theorem outside_reduced_source_case {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    ReducedSourceCase L V A := by
  rcases outside_source_case D S hp ho A hne hAe hA hout with hpush | hcomp
  · exact Or.inl (pushingUp_reduced_case D S (pushingUp_component_case D S hpush))
  · exact Or.inr hcomp

/-- Failure of the exact source specialization reaches the reduced alternatives. -/
theorem failure_reduced_source_case
    (hnot : ¬ OddKernelNormalizer (T := T) (L := L) (V := V)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧ ReducedSourceCase L V A := by
  unfold OddKernelNormalizer at hnot
  push Not at hnot
  obtain ⟨p,hp,ho,A,hne,he,hA,hperm,hout⟩ := hnot
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_reduced_source_case D S hp ho A hne he hA hout⟩

open ChapterE ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan

/-- The exact 11.2.1 Hall kernel reaches the reduced component alternatives.
Exclusion of these genuine components, and hence final normalizer control,
remains with qt-d-1222-natural-odd-kernel-normalizer; final generation assembly
remains with qt-d-1222-natural-weak-closure-source. -/
theorem hall_kernel_reduced_source_case {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H)
    (hk : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧ ReducedSourceCase L V A := by
  obtain ⟨p,A,hp,ho,hne,he,hA,hperm,hout⟩ := hall_kernel_escape D S hH hlarge hP d hm hk
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_reduced_source_case D S hp ho A hne he hA hout⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The remaining actual models after both nonbinary component sieves.
The ordinary component has Ree, Tits or sporadic central quotient. In the
constrained case its star is SL₅(2) and the original full quotient is SL₃(4). -/
def ClassifiedSourceCase (L V A : Subgroup G) : Prop :=
  PushingUpClassifiedCase L V A ∨
    (∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
      (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) ∧
      V.subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))))

include D S
/-- Every outside odd normalizer reaches the remaining exceptional ordinary,
field-four constrained or moved-normalizer-component analysis. -/
theorem outside_classified_source_case {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    ClassifiedSourceCase L V A := by
  rcases outside_reduced_source_case D S hp ho A hne hAe hA hout with hpush | hcomp
  · exact Or.inl (pushingUp_classified_case D S hpush)
  · exact Or.inr hcomp

/-- Failure of the exact source specialization reaches the surviving model alternatives. -/
theorem failure_classified_source_case
    (hnot : ¬ OddKernelNormalizer (T := T) (L := L) (V := V)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧ ClassifiedSourceCase L V A := by
  unfold OddKernelNormalizer at hnot
  push Not at hnot
  obtain ⟨p,hp,ho,A,hne,he,hA,hperm,hout⟩ := hnot
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_classified_source_case D S hp ho A hne he hA hout⟩

open ChapterE ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan

/-- The exact 11.2.1 Hall kernel reaches the surviving actual model alternatives.
Exclusion of these genuine components, and hence final normalizer control,
remains with qt-d-1222-natural-odd-kernel-normalizer; final generation assembly
remains with qt-d-1222-natural-weak-closure-source. -/
theorem hall_kernel_classified_source_case {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H)
    (hk : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧ ClassifiedSourceCase L V A := by
  obtain ⟨p,A,hp,ho,hne,he,hA,hperm,hout⟩ := hall_kernel_escape D S hH hlarge hP d hm hk
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_classified_source_case D S hp ho A hne he hA hout⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The surviving five ordinary sporadic rows, or a moved component in the
literal N(A). The latter retains the proved uniqueness of the original
covering residual, needed for its subsequent component-placement argument. -/
def RemainingSourceCase (L V A : Subgroup G) : Prop :=
  PushingUpRemainingCase L V A ∨
    (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
      ∃ K : Subgroup (normalizer (A : Set G)),
        IsComponent (normalizer (A : Set G)) K ∧
        ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
        ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
        pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
        (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
          normalizer (K : Set (normalizer (A : Set G))) ∧
        V.subgroupOf (normalizer (A : Set G)) ≤
          normalizer (K : Set (normalizer (A : Set G))))

include D S
/-- No constrained, Ree, Tits or small sporadic pushing-up row survives.
The actual moved-component branch retains residual uniqueness. -/
theorem outside_remaining_source_case {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    RemainingSourceCase L V A := by
  by_cases hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))
  · exact Or.inr ⟨hu,component_of_core_eq_bot D S hp ho A hne hAe hA
      (oddNormalizer_reduction_of_cover_uniqueness D A hu hout).2⟩
  · exact Or.inl (pushingUp_remaining_case D S (pushingUp_reduced_case D S
      (pushingUp_component_case D S
        (pushingUp_configuration D S hA (odd_card_of_elementary hp ho A hAe) hu))))

/-- Failure of the exact requested specialization supplies only the surviving
source cases, without an assumed normalizer conclusion. -/
theorem failure_remaining_source_case
    (hnot : ¬ OddKernelNormalizer (T := T) (L := L) (V := V)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧ RemainingSourceCase L V A := by
  unfold OddKernelNormalizer at hnot
  push Not at hnot
  obtain ⟨p,hp,ho,A,hne,he,hA,hperm,hout⟩ := hnot
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_remaining_source_case D S hp ho A hne he hA hout⟩

open ChapterE ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan

/-- The actual 11.2.1 Hall kernel reaches only these remaining configurations.
Their exclusion stays with qt-d-1222-natural-odd-kernel-normalizer; final
11.2.1 assembly stays with qt-d-1222-natural-weak-closure-source. -/
theorem hall_kernel_remaining_source_case {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H)
    (hk : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧ RemainingSourceCase L V A := by
  obtain ⟨p,A,hp,ho,hne,he,hA,hperm,hout⟩ := hall_kernel_escape D S hH hlarge hP d hm hk
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_remaining_source_case D S hp ho A hne he hA hout⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Only the field-four J₄/Ru pushing-up rows remain. In the literal odd
normalizer, every selected C-model component is placed normally, together
with the original V and covering residual. B-only models remain explicit. -/
def RefinedSourceCase (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (A : Subgroup G) : Prop :=
  PushingUpFieldFourCase D S A ∨
    (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
      ∃ K : Subgroup (normalizer (A : Set G)),
        IsComponent (normalizer (A : Set G)) K ∧
        ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
        ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
        pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
        (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
          normalizer (K : Set (normalizer (A : Set G))) ∧
        V.subgroupOf (normalizer (A : Set G)) ≤
          normalizer (K : Set (normalizer (A : Set G))) ∧
        (¬ ChapterA.Section02.IsTheoremCModel (K ⧸ center K) ∨
          (K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
            oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
            centralizer (K : Set (normalizer (A : Set G))) =
              pPrimeCore 2 (normalizer (A : Set G)) ∧
            Nat.card D.chosenCentralQuotient * Nat.card (L ⧸ pCore 2 L) ∣
              Nat.card (K ⧸ center K) ∧ 2 ^ 12 ∣ Nat.card (K ⧸ center K))))

include D S
/-- The actual odd actor reaches the two field-four rows or the improved
component-placement alternative, without any new source premise. -/
theorem outside_refined_source_case {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    RefinedSourceCase D S A := by
  rcases outside_remaining_source_case D S hp ho A hne hAe hA hout with hpush | hmove
  · exact Or.inl (pushingUp_field_four_case D S hpush)
  · obtain ⟨hu,K,hK,hm,houtK,hcore,hmodel,hFK,hVK⟩ := hmove
    refine Or.inr ⟨hu,K,hK,hm,houtK,hcore,hmodel,hFK,hVK,?_⟩
    by_cases hC : ChapterA.Section02.IsTheoremCModel (K ⧸ center K)
    · have hoA := odd_card_of_elementary hp ho A hAe
      obtain ⟨hn,hv,hf,hz⟩ := moved_component_normal_of_theoremC D S hA hoA hu hout K hK houtK hC
      exact Or.inr ⟨hn,hv,hf,hz,placed_residual_product_card_dvd D S hA hoA K hf,
        moved_component_two_power_dvd D S hA hoA hu hout K hK houtK hC⟩
    · exact Or.inl hC

/-- Failure of the original normalizer containment supplies only the refined cases. -/
theorem failure_refined_source_case
    (hnot : ¬ OddKernelNormalizer (T := T) (L := L) (V := V)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧ RefinedSourceCase D S A := by
  unfold OddKernelNormalizer at hnot
  push Not at hnot
  obtain ⟨p,hp,ho,A,hne,he,hA,hperm,hout⟩ := hnot
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_refined_source_case D S hp ho A hne he hA hout⟩

open ChapterE ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan

/-- The literal Hall kernel in 11.2.1 reaches the refined cases. Their final
exclusion remains with qt-d-1222-natural-odd-kernel-normalizer; generation
assembly remains with qt-d-1222-natural-weak-closure-source. -/
theorem hall_kernel_refined_source_case {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H)
    (hk : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧ RefinedSourceCase D S A := by
  obtain ⟨p,A,hp,ho,hne,he,hA,hperm,hout⟩ := hall_kernel_escape D S hH hlarge hP d hm hk
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_refined_source_case D S hp ho A hne he hA hout⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The original source alternatives after the complete moved C-model inspection.
Both C-model branches retain only actual J₄/Ru quotients and full SL₃(4).
The genuinely additional B-model rows remain separate obligations. -/
def LocalizedSourceCase (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (A : Subgroup G) : Prop :=
  (PushingUpFieldFourCase D S A ∧ V ⊓ centralizer (L : Set G) = ⊥ ∧ Nat.card V = 64) ∨
    (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
      ∃ K : Subgroup (normalizer (A : Set G)),
        IsComponent (normalizer (A : Set G)) K ∧
        ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
        ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
        pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
        (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
          normalizer (K : Set (normalizer (A : Set G))) ∧
        V.subgroupOf (normalizer (A : Set G)) ≤
          normalizer (K : Set (normalizer (A : Set G))) ∧
        (¬ ChapterA.Section02.IsTheoremCModel (K ⧸ center K) ∨
          (K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
            oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
            centralizer (K : Set (normalizer (A : Set G))) =
              pPrimeCore 2 (normalizer (A : Set G)) ∧
            (Nonempty (K ⧸ center K ≃* Janko4.Model) ∨
              Nonempty (K ⧸ center K ≃* Rudvalis.Model)) ∧
            S.field.degree = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) ∧
            Nat.card (center (L ⧸ pCore 2 L)) = 3 ∧
            V ⊓ centralizer (L : Set G) = ⊥ ∧ Nat.card V = 64)))

include D S
/-- Every actual outside actor reaches the two field-four configurations or a
B-only moved row; the entire shared C-model inspection is discharged. -/
theorem outside_localized_source_case {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    LocalizedSourceCase D S A := by
  rcases outside_remaining_source_case D S hp ho A hne hAe hA hout with hpush | hmove
  · have h := pushingUp_field_four_case D S hpush
    exact Or.inl ⟨h,h.original_module D S⟩
  · obtain ⟨hu,K,hK,hm,houtK,hcore,hmodel,hFK,hVK⟩ := hmove
    refine Or.inr ⟨hu,K,hK,hm,houtK,hcore,hmodel,hFK,hVK,?_⟩
    by_cases hC : ChapterA.Section02.IsTheoremCModel (K ⧸ center K)
    · obtain ⟨hn,hv,hf,hz,hm,hdegree,⟨e⟩,hc⟩ := moved_component_last_models D S hA
        (odd_card_of_elementary hp ho A hAe) hu hout K hK houtK hC
      exact Or.inr ⟨hn,hv,hf,hz,hm,hdegree,⟨e⟩,hc,
        original_module_card_of_field_four D S hdegree e⟩
    · exact Or.inl hC

/-- Failure of the unchanged normalizer statement yields the localized source cases. -/
theorem failure_localized_source_case
    (hnot : ¬ OddKernelNormalizer (T := T) (L := L) (V := V)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧ LocalizedSourceCase D S A := by
  unfold OddKernelNormalizer at hnot
  push Not at hnot
  obtain ⟨p,hp,ho,A,hne,he,hA,hperm,hout⟩ := hnot
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_localized_source_case D S hp ho A hne he hA hout⟩

open ChapterE ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan
/-- The literal Hall kernel reaches the localized alternatives with its original
V and AT=TA. Their exclusion remains with this owner; final 11.2.1 assembly
remains with qt-d-1222-natural-weak-closure-source. -/
theorem hall_kernel_localized_source_case {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H)
    (hk : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧ LocalizedSourceCase D S A := by
  obtain ⟨p,A,hp,ho,hne,he,hA,hperm,hout⟩ := hall_kernel_escape D S hH hlarge hP d hm hk
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_localized_source_case D S hp ho A hne he hA hout⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The literal component action, after excluding the completed outer rows
and applying the full B-model sieve whenever that action is inner. -/
def MovedActionCase (D : ChosenModule T L V) (A : Subgroup G)
    (K : Subgroup (normalizer (A : Set G))) : Prop :=
  ((∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* coreCentralQuotient L,
      Function.Surjective f) ∧
    ¬ ChapterA.Section02.IsTheoremCModel (K ⧸ center K) ∧
    (∀ n : ℕ, ¬ Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin n))) ∧
    (∀ q : ℕ, Odd q → ¬ ClassicalGroup.IsPSL (K ⧸ center K) 2 q)) ∨
  (K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) = pPrimeCore 2 (normalizer (A : Set G)) ∧
    NaturalCoverImage D (K ⧸ center K) ∧
    6 ≤ primeRank 2 (K ⧸ center K) ∧ 2 ^ 12 ∣ Nat.card (K ⧸ center K) ∧
    RemainingPlacedModels (K ⧸ center K))

include D S in
/-- Refine the same selected component without a model-exclusion or inner-action premise. -/
theorem moved_action_case {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K)) : MovedActionCase D A K := by
  rcases moved_component_inner_or_outer_section D S hA hodd K hK with hi | ho
  · obtain ⟨hn,hv,hf,hc,himage,hr,hd⟩ :=
      moved_component_placement_of_inner D S hA hodd hu hout K hK houtK hi
    exact Or.inr ⟨hn,hv,hf,hc,himage,hr,hd,himage.theoremB_models D S hm⟩
  · exact Or.inl ⟨ho,moved_outer_section_exclusions D S K hK ho⟩

/-- Retain every earlier localized conclusion and refine the same moved-component
witness by its actual outer action. -/
def ActionSourceCase (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (A : Subgroup G) : Prop :=
  LocalizedSourceCase D S A ∧
    ((PushingUpFieldFourCase D S A ∧ V ⊓ centralizer (L : Set G) = ⊥ ∧ Nat.card V = 64) ∨
      (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
        ∃ K : Subgroup (normalizer (A : Set G)),
          IsComponent (normalizer (A : Set G)) K ∧
          ⁅K,V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
          ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
          pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
          MovedActionCase D A K))

/-- An outside normalizer satisfies the full actual-action refinement. -/
theorem outside_action_source_case {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) : ActionSourceCase D S A := by
  have hcase := outside_localized_source_case D S hp ho A hne hAe hA hout
  refine ⟨hcase,?_⟩
  rcases hcase with hpush | ⟨hu,K,hK,hm,houtK,hcore,hmodel,_⟩
  · exact Or.inl hpush
  · exact Or.inr ⟨hu,K,hK,hm,houtK,hcore,hmodel,
      moved_action_case D S hA (odd_card_of_elementary hp ho A hAe) hu hout K hK houtK hmodel⟩

/-- Failure of the unchanged target retains AT=TA and reaches the full action sieve. -/
theorem failure_action_source_case
    (hnot : ¬ OddKernelNormalizer (T := T) (L := L) (V := V)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧ ActionSourceCase D S A := by
  unfold OddKernelNormalizer at hnot
  push Not at hnot
  obtain ⟨p,hp,ho,A,hne,he,hA,hperm,hout⟩ := hnot
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_action_source_case D S hp ho A hne he hA hout⟩

open ChapterE ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan
/-- Apply the entire action sieve to the literal Hall kernel. All new local
premises are discharged; the surviving configurations remain to be excluded. -/
theorem hall_kernel_action_source_case {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H)
    (hk : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧ ActionSourceCase D S A := by
  obtain ⟨p,A,hp,ho,hne,he,hA,hperm,hout⟩ := hall_kernel_escape D S hH hlarge hP d hm hk
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_action_source_case D S hp ho A hne he hA hout⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The same full component cover after excluding all binary unitary-four
  actions and the odd G₂ placed image. -/
def RemainingMovedActionCase (D : ChosenModule T L V) (A : Subgroup G)
    (K : Subgroup (normalizer (A : Set G))) : Prop :=
  MovedActionCase D A K ∧
    (∀ n : ℕ, 1 ≤ n → ¬ ClassicalGroup.IsPSU (K ⧸ center K) 4 (2 ^ n)) ∧
    ((∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* coreCentralQuotient L,
      Function.Surjective f) ∨ RemainingPlacedModelsWithoutG2 (K ⧸ center K))

include D S in
/-- Discharge the new exclusions on the actual selected component. -/
theorem remaining_moved_action_case {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K)) :
    RemainingMovedActionCase D A K := by
  have hc := moved_action_case D S hA hodd hu hout K hK houtK hm
  refine ⟨hc,fun n hn => moved_component_not_binary_unitary_four
    D S hA hodd hu hout K hK houtK hn,?_⟩
  rcases hc with ⟨ho,_⟩ | ⟨_,_,_,_,hi,_⟩
  · exact Or.inl ho
  · exact Or.inr (hi.theoremB_models_without_g2 D S hm)

/-- The outside alternatives retain the original field-four module equalities
  and refine the very same moved component. -/
def RemainingActionSourceCase (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (A : Subgroup G) : Prop :=
  ActionSourceCase D S A ∧
    ((PushingUpFieldFourCase D S A ∧ V ⊓ centralizer (L : Set G) = ⊥ ∧ Nat.card V = 64) ∨
      (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
        ∃ K : Subgroup (normalizer (A : Set G)),
          IsComponent (normalizer (A : Set G)) K ∧
          ⁅K,V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
          ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
          pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
          RemainingMovedActionCase D A K))

include D S
/-- Apply both completed model exclusions to an outside odd actor. -/
theorem outside_remaining_action_source_case {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    RemainingActionSourceCase D S A := by
  have hc := outside_action_source_case D S hp ho A hne hAe hA hout
  refine ⟨hc,?_⟩
  rcases hc.2 with hpush | ⟨hu,K,hK,hm,houtK,hcore,hmodel,_⟩
  · exact Or.inl hpush
  · exact Or.inr ⟨hu,K,hK,hm,houtK,hcore,hmodel,
      remaining_moved_action_case D S hA (odd_card_of_elementary hp ho A hAe)
        hu hout K hK houtK hmodel⟩

/-- Failure of the unchanged odd-normalizer target retains AT=TA and the
  original module in the strengthened alternatives. -/
theorem failure_remaining_action_source_case
    (hnot : ¬ OddKernelNormalizer (T := T) (L := L) (V := V)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧ RemainingActionSourceCase D S A := by
  unfold OddKernelNormalizer at hnot
  push Not at hnot
  obtain ⟨p,hp,ho,A,hne,he,hA,hperm,hout⟩ := hnot
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_remaining_action_source_case D S hp ho A hne he hA hout⟩

open ChapterE ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan
/-- The literal Hall-kernel application, with no new model or action premise.
  The remaining exclusions and final OddKernelNormalizer theorem stay with
  this task; 11.2.1 assembly stays with qt-d-1222-natural-weak-closure-source. -/
theorem hall_kernel_remaining_action_source_case {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H)
    (hk : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧ RemainingActionSourceCase D S A := by
  obtain ⟨p,A,hp,ho,hne,he,hA,hperm,hout⟩ := hall_kernel_escape D S hH hlarge hP d hm hk
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_remaining_action_source_case D S hp ho A hne he hA hout⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Every placed B-component has one of the two remaining sporadic central
quotients and the original full field-four actor. The other branch retains
an actual section of the outer automorphism group of the full component cover. -/
def SporadicMovedActionCase (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (A : Subgroup G) (K : Subgroup (normalizer (A : Set G))) : Prop :=
  RemainingMovedActionCase D A K ∧
    ((∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* coreCentralQuotient L,
        Function.Surjective f) ∨
      (K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
        oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
        centralizer (K : Set (normalizer (A : Set G))) = pPrimeCore 2 (normalizer (A : Set G)) ∧
        NaturalCoverImage D (K ⧸ center K) ∧
        (Nonempty (K ⧸ center K ≃* Janko4.Model) ∨
          Nonempty (K ⧸ center K ≃* Rudvalis.Model)) ∧
        S.field.degree = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) ∧
        Nat.card (center (L ⧸ pCore 2 L)) = 3 ∧
        V ⊓ centralizer (L : Set G) = ⊥ ∧ Nat.card V = 64))

include D S in
/-- Apply the completed placed B-catalogue inspection to the same original
component, without an extra placement or model-exclusion premise. -/
theorem sporadic_moved_action_case {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K)) :
    SporadicMovedActionCase D S A K := by
  have hc := remaining_moved_action_case D S hA hodd hu hout K hK houtK hm
  refine ⟨hc,?_⟩
  rcases hc.1 with ⟨ho,_⟩ | ⟨hn,hv,hf,hz,hi,_⟩
  · exact Or.inl ho
  · have hs := hi.theoremB_models_sporadic D S hm
    have hd := hi.product_card_dvd D
    have hfield : S.field.degree = 2 ∧
        Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) ∧
        Nat.card (center (L ⧸ pCore 2 L)) = 3 := by
      rcases hs with he | he
      · rw [Nat.card_congr he.some.toEquiv,Janko4.Cardinality.model_card] at hd
        exact field_four_of_product_order_dvd D S _ (Or.inr rfl) hd
      · rw [Nat.card_congr he.some.toEquiv,Rudvalis.model_card] at hd
        exact field_four_of_product_order_dvd D S _ (Or.inl rfl) hd
    exact Or.inr ⟨hn,hv,hf,hz,hi,hs,hfield.1,hfield.2.1,hfield.2.2,
      original_module_card_of_field_four D S hfield.1 hfield.2.1.some⟩

/-- All placed components are now sporadic. Both field-four configurations
retain C_V(L)=1 and |V|=64 for the original V; the actual outer sections remain. -/
def SporadicActionSourceCase (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (A : Subgroup G) : Prop :=
  RemainingActionSourceCase D S A ∧
    ((PushingUpFieldFourCase D S A ∧ V ⊓ centralizer (L : Set G) = ⊥ ∧ Nat.card V = 64) ∨
      (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
        ∃ K : Subgroup (normalizer (A : Set G)),
          IsComponent (normalizer (A : Set G)) K ∧
          ⁅K,V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
          ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
          pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
          SporadicMovedActionCase D S A K))

include D S
/-- Failure of containment leaves only the sporadic placed rows or a genuine
outer section on the original component cover. -/
theorem outside_sporadic_action_source_case {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    SporadicActionSourceCase D S A := by
  have hc := outside_remaining_action_source_case D S hp ho A hne hAe hA hout
  refine ⟨hc,?_⟩
  rcases hc.2 with hpush | ⟨hu,K,hK,hm,houtK,hcore,hmodel,_⟩
  · exact Or.inl hpush
  · exact Or.inr ⟨hu,K,hK,hm,houtK,hcore,hmodel,
      sporadic_moved_action_case D S hA (odd_card_of_elementary hp ho A hAe)
        hu hout K hK houtK hmodel⟩

/-- The unchanged normalizer target retains AT=TA in the remaining alternatives. -/
theorem failure_sporadic_action_source_case
    (hnot : ¬ OddKernelNormalizer (T := T) (L := L) (V := V)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧ SporadicActionSourceCase D S A := by
  unfold OddKernelNormalizer at hnot
  push Not at hnot
  obtain ⟨p,hp,ho,A,hne,he,hA,hperm,hout⟩ := hnot
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_sporadic_action_source_case D S hp ho A hne he hA hout⟩

open ChapterE ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan
/-- The literal Hall kernel reaches the completed placed B-model sieve.
J₄/Ru local exclusions and the genuine outer sections stay with this task;
final 11.2.1 assembly stays with qt-d-1222-natural-weak-closure-source. -/
theorem hall_kernel_sporadic_action_source_case {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H)
    (hk : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧ SporadicActionSourceCase D S A := by
  obtain ⟨p,A,hp,ho,hne,he,hA,hperm,hout⟩ := hall_kernel_escape D S hH hlarge hP d hm hk
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_sporadic_action_source_case D S hp ho A hne he hA hout⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- Every escaping original odd actor forces the full SL₃(4) cover and the
order 64 original module, including in the genuine outer-action branch. -/
theorem outside_linear_field_four {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    S.field.degree = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) ∧
      Nat.card (center (L ⧸ pCore 2 L)) = 3 ∧
      V ⊓ centralizer (L : Set G) = ⊥ ∧ Nat.card V = 64 := by
  have hc := outside_sporadic_action_source_case D S hp ho A hne hAe hA hout
  have hfield : S.field.degree = 2 ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) := by
    rcases hc.2 with ⟨hpush,_,_⟩ | ⟨_,K,hK,_,_,_,hm,hs⟩
    · obtain ⟨J,H,W,hpush,hH,hJH,hstrict,hVJ,hC,hcover,hN,hVB,he,hno,hsize,hVW,
        hf,⟨e⟩,hz,hK⟩ := hpush
      exact ⟨hf,⟨e⟩⟩
    · rcases hs.2 with houter | ⟨_,_,_,_,_,_,hf,he,_⟩
      · exact moved_outer_linear_field_four D S K hK hm houter
      · exact ⟨hf,he⟩
  obtain ⟨hf,he⟩ := hfield
  obtain ⟨e⟩ := he
  refine ⟨hf,⟨e⟩,?_,original_module_card_of_field_four D S hf e⟩
  rw [Nat.card_congr (centerCongr e).toEquiv,Atlas.ExceptionalSupport.card_sl_center]
  norm_num [S.field.card_eq,hf]

/-- The complete requested normalizer control for every field larger than four. -/
theorem oddKernelNormalizer_of_field_ne_four (hf : S.field.degree ≠ 2) :
    OddKernelNormalizer (T := T) (L := L) (V := V) := by
  intro p hp ho A hne hAe hA _
  by_contra hout
  exact hf (outside_linear_field_four D S hp ho A hne hAe hA hout).1

/-- The complete requested normalizer control for every nonbinary G₂ row. -/
theorem oddKernelNormalizer_of_g2
    (e : (L ⧸ pCore 2 L) ≃* Atlas.G2.Model S.field.Carrier) :
    OddKernelNormalizer (T := T) (L := L) (V := V) := by
  intro p hp ho A hne hAe hA _
  by_contra hout
  obtain ⟨hf,he,_⟩ := outside_linear_field_four D S hp ho A hne hAe hA hout
  obtain ⟨a⟩ := he
  have hc := Nat.card_congr (e.symm.trans a).toEquiv
  rw [Atlas.G2.card_Model,linear_three_order] at hc
  norm_num [S.field.card_eq,hf] at hc

/-- The complete requested normalizer control for every nonbinary symplectic row. -/
theorem oddKernelNormalizer_of_sp4
    (e : (L ⧸ pCore 2 L) ≃* Theory.SpecificGroups.SymplecticFour.Sp S.field.Carrier) :
    OddKernelNormalizer (T := T) (L := L) (V := V) := by
  intro p hp ho A hne hAe hA _
  by_contra hout
  obtain ⟨hf,he,_⟩ := outside_linear_field_four D S hp ho A hne hAe hA hout
  obtain ⟨a⟩ := he
  have hc := Nat.card_congr (e.symm.trans a).toEquiv
  rw [Theory.SpecificGroups.SymplecticFour.card_sp,linear_three_order] at hc
  norm_num [S.field.card_eq,hf] at hc

open ChapterE ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan
/-- Larger fields discharge the literal Hall kernel's normalizer premise. -/
theorem hall_faithful_of_field_ne_four (hf : S.field.degree ≠ 2)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H) :
    d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) = ⊥ :=
  hall_faithful D S (oddKernelNormalizer_of_field_ne_four D S hf) hH hlarge hP d hm

/-- The G₂ result discharges the same Hall kernel in every nonbinary field. -/
theorem hall_faithful_of_g2
    (e : (L ⧸ pCore 2 L) ≃* Atlas.G2.Model S.field.Carrier)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H) :
    d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) = ⊥ :=
  hall_faithful D S (oddKernelNormalizer_of_g2 D S e) hH hlarge hP d hm

/-- The symplectic result discharges the same Hall kernel in every nonbinary field. -/
theorem hall_faithful_of_sp4
    (e : (L ⧸ pCore 2 L) ≃* Theory.SpecificGroups.SymplecticFour.Sp S.field.Carrier)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H) :
    d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) = ⊥ :=
  hall_faithful D S (oddKernelNormalizer_of_sp4 D S e) hH hlarge hP d hm

/-- A nontrivial literal Hall kernel forces linear field four, the full cubic
cover, and both equalities for the original V. The remaining sporadic and
outer configurations are retained by `hall_kernel_sporadic_action_source_case`. -/
theorem hall_kernel_linear_field_four {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H)
    (hk : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) ≠ ⊥) :
    S.field.degree = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) ∧
      Nat.card (center (L ⧸ pCore 2 L)) = 3 ∧
      V ⊓ centralizer (L : Set G) = ⊥ ∧ Nat.card V = 64 := by
  obtain ⟨p,A,hp,ho,hne,he,hA,_,hout⟩ := hall_kernel_escape D S hH hlarge hP d hm hk
  exact outside_linear_field_four D S hp ho A hne he hA hout

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Retain the complete earlier alternative and exclude PSU₅(4) on the same
selected moved component, including its genuine outer-action branch. -/
def UnitaryFiveFreeActionSourceCase (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (A : Subgroup G) : Prop :=
  SporadicActionSourceCase D S A ∧
    ((PushingUpFieldFourCase D S A ∧ V ⊓ centralizer (L : Set G) = ⊥ ∧ Nat.card V = 64) ∨
      (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
        ∃ K : Subgroup (normalizer (A : Set G)),
          IsComponent (normalizer (A : Set G)) K ∧
          ⁅K,V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
          ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
          pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
          SporadicMovedActionCase D S A K ∧ ¬ ClassicalGroup.IsPSU (K ⧸ center K) 5 4))

include D S
/-- Discharge both unitary-five actions on the original source witness. -/
theorem outside_unitary_five_free_action_source_case {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    UnitaryFiveFreeActionSourceCase D S A := by
  have hc := outside_sporadic_action_source_case D S hp ho A hne hAe hA hout
  refine ⟨hc,?_⟩
  rcases hc.2 with hpush | ⟨hu,K,hK,hm,houtK,hcore,hmodel,haction⟩
  · exact Or.inl hpush
  · exact Or.inr ⟨hu,K,hK,hm,houtK,hcore,hmodel,haction,
      moved_component_not_unitary_five_four D S hA (odd_card_of_elementary hp ho A hAe)
        hu hout K hK houtK⟩

/-- The original normalizer target reaches the stronger alternatives with AT=TA. -/
theorem failure_unitary_five_free_action_source_case
    (hnot : ¬ OddKernelNormalizer (T := T) (L := L) (V := V)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      UnitaryFiveFreeActionSourceCase D S A := by
  unfold OddKernelNormalizer at hnot
  push Not at hnot
  obtain ⟨p,hp,ho,A,hne,he,hA,hperm,hout⟩ := hnot
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_unitary_five_free_action_source_case D S hp ho A hne he hA hout⟩

open ChapterE ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan
/-- The literal Hall kernel inherits the complete PSU₅(4) exclusion. All other
remaining outer and J₄/Ru exclusions stay with this owner; final 11.2.1 assembly
stays with qt-d-1222-natural-weak-closure-source. -/
theorem hall_kernel_unitary_five_free_action_source_case {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H)
    (hk : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      UnitaryFiveFreeActionSourceCase D S A := by
  obtain ⟨p,A,hp,ho,hne,he,hA,hperm,hout⟩ := hall_kernel_escape D S hH hlarge hP d hm hk
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_unitary_five_free_action_source_case D S hp ho A hne he hA hout⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The original component witness, with Ru and J₃ excluded in both actions and
J₄ the sole placed quotient. All earlier full-cover and original-module
conclusions, including the PSU₅(4) exclusion, are retained. -/
def JankoActionSourceCase (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (A : Subgroup G) : Prop :=
  UnitaryFiveFreeActionSourceCase D S A ∧
    ((PushingUpFieldFourCase D S A ∧ V ⊓ centralizer (L : Set G) = ⊥ ∧ Nat.card V = 64) ∨
      (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
        ∃ K : Subgroup (normalizer (A : Set G)),
          IsComponent (normalizer (A : Set G)) K ∧
          ⁅K,V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
          ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
          pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
          SporadicMovedActionCase D S A K ∧
          ¬ ClassicalGroup.IsPSU (K ⧸ center K) 5 4 ∧
          ¬ Nonempty ((K ⧸ center K) ≃* Rudvalis.Model) ∧
          ¬ Nonempty ((K ⧸ center K) ≃* Sporadic.Janko3.Model) ∧
          ((∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* coreCentralQuotient L,
              Function.Surjective f) ∨ Nonempty ((K ⧸ center K) ≃* Janko4.Model))))

include D S
/-- The Rudvalis cubic-centralizer and J₃ outer-section obstructions apply
to the same actual moved component selected by the source argument. -/
theorem outside_janko_action_source_case {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    JankoActionSourceCase D S A := by
  have hc := outside_unitary_five_free_action_source_case D S hp ho A hne hAe hA hout
  refine ⟨hc,?_⟩
  rcases hc.2 with hpush | ⟨hu,K,hK,hm,houtK,hcore,hmodel,haction,hunitary⟩
  · exact Or.inl hpush
  · have hr : ¬ Nonempty ((K ⧸ center K) ≃* Rudvalis.Model) := fun ⟨e⟩ =>
      moved_component_not_rudvalis D S hA (odd_card_of_elementary hp ho A hAe)
        hu hout K hK houtK e
    have hj : ¬ Nonempty ((K ⧸ center K) ≃* Sporadic.Janko3.Model) := fun ⟨e⟩ =>
      moved_component_not_janko_three D S hA (odd_card_of_elementary hp ho A hAe)
        hu hout K hK houtK e
    refine Or.inr ⟨hu,K,hK,hm,houtK,hcore,hmodel,haction,hunitary,hr,hj,?_⟩
    rcases haction.2 with houter | ⟨_,_,_,_,hi,_⟩
    · exact Or.inl houter
    · exact Or.inr (hi.theoremB_models_jankoFour D S hmodel)

/-- The unchanged odd-normalizer target reaches the refined source witness,
retaining the original elementary actor and AT=TA. -/
theorem failure_janko_action_source_case
    (hnot : ¬ OddKernelNormalizer (T := T) (L := L) (V := V)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      JankoActionSourceCase D S A := by
  unfold OddKernelNormalizer at hnot
  push Not at hnot
  obtain ⟨p,hp,ho,A,hne,he,hA,hperm,hout⟩ := hnot
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_janko_action_source_case D S hp ho A hne he hA hout⟩

open ChapterE ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan
/-- The literal Hall kernel has no moved Ru or J₃ component; an inner action now
forces J₄. Its remaining field-four outer and moved-J₄ exclusions stay with
this owner. The ordinary C.2.8 exclusion belongs to the fixed-summand owner;
final 11.2.1 assembly belongs to qt-d-1222-natural-weak-closure-source. -/
theorem hall_kernel_janko_action_source_case {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H)
    (hk : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      JankoActionSourceCase D S A := by
  obtain ⟨p,A,hp,ho,hne,he,hA,hperm,hout⟩ := hall_kernel_escape D S hH hlarge hP d hm hk
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_janko_action_source_case D S hp ho A hne he hA hout⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The unchanged source witness with its remaining outer rows made explicit.
The output retains the original full SL₃(4) cover, cubic center, module of
order 64, residual placement and all earlier model exclusions. -/
def RemainingComponentSourceCase (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (A : Subgroup G) : Prop :=
  JankoActionSourceCase D S A ∧
    (S.field.degree = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) ∧
      Nat.card (center (L ⧸ pCore 2 L)) = 3 ∧
      V ⊓ centralizer (L : Set G) = ⊥ ∧ Nat.card V = 64) ∧
    ((PushingUpFieldFourCase D S A ∧ V ⊓ centralizer (L : Set G) = ⊥ ∧ Nat.card V = 64) ∨
      (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
        ∃ K : Subgroup (normalizer (A : Set G)),
          IsComponent (normalizer (A : Set G)) K ∧
          ⁅K,V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
          ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
          pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
          SporadicMovedActionCase D S A K ∧
          (((∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* coreCentralQuotient L,
              Function.Surjective f) ∧ RemainingOuterModel (K ⧸ center K)) ∨
            Nonempty ((K ⧸ center K) ≃* Janko4.Model))))

include D S
/-- Odd ternary and McL exclusions apply to the same source-selected component.
No extra model or local-normalizer premise is introduced. -/
theorem outside_remaining_component_source_case {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    RemainingComponentSourceCase D S A := by
  have hc := outside_janko_action_source_case D S hp ho A hne hAe hA hout
  refine ⟨hc,outside_linear_field_four D S hp ho A hne hAe hA hout,?_⟩
  rcases hc.2 with hpush | ⟨hu,K,hK,hm,houtK,hcore,hmodel,haction,_,_,_,hbranch⟩
  · exact Or.inl hpush
  · refine Or.inr ⟨hu,K,hK,hm,houtK,hcore,hmodel,haction,?_⟩
    rcases hbranch with houter | hj
    · exact Or.inl ⟨houter,moved_outer_remaining_models D S K hK hmodel houter⟩
    · exact Or.inr hj

/-- Failure of the original normalizer conclusion retains AT=TA and the
complete source witness, with only the five listed outer rows remaining. -/
theorem failure_remaining_component_source_case
    (hnot : ¬ OddKernelNormalizer (T := T) (L := L) (V := V)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      RemainingComponentSourceCase D S A := by
  unfold OddKernelNormalizer at hnot
  push Not at hnot
  obtain ⟨p,hp,ho,A,hne,he,hA,hperm,hout⟩ := hnot
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_remaining_component_source_case D S hp ho A hne he hA hout⟩

open ChapterE ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan
/-- The literal Hall kernel supplies the same reduced component alternatives.
The remaining exclusions stay with this owner, ordinary C.2.8 stays with the
fixed-summand owner, and final 11.2.1 stays with the weak-closure source owner. -/
theorem hall_kernel_remaining_component_source_case {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H)
    (hk : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      RemainingComponentSourceCase D S A := by
  obtain ⟨p,A,hp,ho,hne,he,hA,hperm,hout⟩ := hall_kernel_escape D S hH hlarge hP d hm hk
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_remaining_component_source_case D S hp ho A hne he hA hout⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer


public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The unchanged source witness after the binary symplectic six-space exclusion.
The output retains the original full SL₃(4) cover, cubic center, module of
order 64, residual placement and all earlier model exclusions. -/
def OddComponentSourceCase (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (A : Subgroup G) : Prop :=
  RemainingComponentSourceCase D S A ∧
    (S.field.degree = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) ∧
      Nat.card (center (L ⧸ pCore 2 L)) = 3 ∧
      V ⊓ centralizer (L : Set G) = ⊥ ∧ Nat.card V = 64) ∧
    ((PushingUpFieldFourCase D S A ∧ V ⊓ centralizer (L : Set G) = ⊥ ∧ Nat.card V = 64) ∨
      (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
        ∃ K : Subgroup (normalizer (A : Set G)),
          IsComponent (normalizer (A : Set G)) K ∧
          ⁅K,V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
          ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
          pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
          SporadicMovedActionCase D S A K ∧
          (((∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* coreCentralQuotient L,
              Function.Surjective f) ∧ RemainingOddPlacedModels (K ⧸ center K)) ∨
            Nonempty ((K ⧸ center K) ≃* Janko4.Model))))

include D S
/-- The binary symplectic exclusion applies to the same source-selected component.
No extra model or local-normalizer premise is introduced. -/
theorem outside_odd_component_source_case {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    OddComponentSourceCase D S A := by
  have hc := outside_remaining_component_source_case D S hp ho A hne hAe hA hout
  refine ⟨hc,outside_linear_field_four D S hp ho A hne hAe hA hout,?_⟩
  rcases hc.2.2 with hpush | ⟨hu,K,hK,hm,houtK,hcore,hmodel,haction,hbranch⟩
  · exact Or.inl hpush
  · refine Or.inr ⟨hu,K,hK,hm,houtK,hcore,hmodel,haction,?_⟩
    rcases hbranch with ⟨houter,_⟩ | hj
    · exact Or.inl ⟨houter,moved_outer_odd_models D S K hK hmodel houter⟩
    · exact Or.inr hj

/-- Failure of the original normalizer conclusion retains AT=TA and the
complete source witness, with only the four odd-characteristic outer rows remaining. -/
theorem failure_odd_component_source_case
    (hnot : ¬ OddKernelNormalizer (T := T) (L := L) (V := V)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      OddComponentSourceCase D S A := by
  unfold OddKernelNormalizer at hnot
  push Not at hnot
  obtain ⟨p,hp,ho,A,hne,he,hA,hperm,hout⟩ := hnot
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_odd_component_source_case D S hp ho A hne he hA hout⟩

open ChapterE ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan
/-- The literal Hall kernel supplies the same odd outer component alternatives.
The remaining exclusions stay with this owner, ordinary C.2.8 stays with the
fixed-summand owner, and final 11.2.1 stays with the weak-closure source owner. -/
theorem hall_kernel_odd_component_source_case {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H)
    (hk : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      OddComponentSourceCase D S A := by
  obtain ⟨p,A,hp,ho,hne,he,hA,hperm,hout⟩ := hall_kernel_escape D S hH hlarge hP d hm hk
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_odd_component_source_case D S hp ho A hne he hA hout⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer


public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The original source witness after excluding every outer component action.
The output retains the original full SL₃(4) cover, cubic center, module of
order 64, residual placement and all earlier model exclusions. -/
def InnerComponentSourceCase (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (A : Subgroup G) : Prop :=
  OddComponentSourceCase D S A ∧
    (S.field.degree = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) ∧
      Nat.card (center (L ⧸ pCore 2 L)) = 3 ∧
      V ⊓ centralizer (L : Set G) = ⊥ ∧ Nat.card V = 64) ∧
    ((PushingUpFieldFourCase D S A ∧ V ⊓ centralizer (L : Set G) = ⊥ ∧ Nat.card V = 64) ∨
      (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
        ∃ K : Subgroup (normalizer (A : Set G)),
          IsComponent (normalizer (A : Set G)) K ∧
          ⁅K,V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
          ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
          pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
          SporadicMovedActionCase D S A K ∧
          K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
          oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
          centralizer (K : Set (normalizer (A : Set G))) = pPrimeCore 2 (normalizer (A : Set G)) ∧
          NaturalCoverImage D (K ⧸ center K) ∧
          Nonempty ((K ⧸ center K) ≃* Janko4.Model)))

include D S
/-- All outer exclusions place the original residual and module in the same actual component.
No extra model or local-normalizer premise is introduced. -/
theorem outside_inner_component_source_case {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    InnerComponentSourceCase D S A := by
  have hc := outside_odd_component_source_case D S hp ho A hne hAe hA hout
  refine ⟨hc,outside_linear_field_four D S hp ho A hne hAe hA hout,?_⟩
  rcases hc.2.2 with hpush | ⟨hu,K,hK,hm,houtK,hcore,hmodel,haction,_⟩
  · exact Or.inl hpush
  · refine Or.inr ⟨hu,K,hK,hm,houtK,hcore,hmodel,haction,?_⟩
    have hi := moved_component_inner_action D S hA (odd_card_of_elementary hp ho A hAe) K hK hmodel
    obtain ⟨hKn,hVK,hFK,hc,him,_,_⟩ := moved_component_placement_of_inner D S hA
      (odd_card_of_elementary hp ho A hAe) hu hout K hK houtK hi
    exact ⟨hKn,hVK,hFK,hc,him,him.theoremB_models_jankoFour D S hmodel⟩

/-- Failure of the original normalizer conclusion retains AT=TA and the
complete source witness, retaining only ordinary C.2.8 and a moved inner J₄ component. -/
theorem failure_inner_component_source_case
    (hnot : ¬ OddKernelNormalizer (T := T) (L := L) (V := V)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      InnerComponentSourceCase D S A := by
  unfold OddKernelNormalizer at hnot
  push Not at hnot
  obtain ⟨p,hp,ho,A,hne,he,hA,hperm,hout⟩ := hnot
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_inner_component_source_case D S hp ho A hne he hA hout⟩

open ChapterE ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan
/-- The literal Hall kernel has only the ordinary or moved-inner J₄ alternatives.
The remaining exclusions stay with this owner, ordinary C.2.8 stays with the
fixed-summand owner, and final 11.2.1 stays with the weak-closure source owner. -/
theorem hall_kernel_inner_component_source_case {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H)
    (hk : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      InnerComponentSourceCase D S A := by
  obtain ⟨p,A,hp,ho,hne,he,hA,hperm,hout⟩ := hall_kernel_escape D S hH hlarge hP d hm hk
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_inner_component_source_case D S hp ho A hne he hA hout⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The surviving moved branch retains its original component and exact residual
projection, with full normalizer control and no even residual centralizer. -/
def LocalInnerComponentSourceCase (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (A : Subgroup G) : Prop :=
  InnerComponentSourceCase D S A ∧
    (PushingUpFieldFourCase D S A ∨
      (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
        ∃ K : Subgroup (normalizer (A : Set G)),
          IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧ pCore 2 K = ⊥ ∧
          ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
          V ≤ K.map (normalizer (A : Set G)).subtype ∧
          oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
          centralizer (K : Set (normalizer (A : Set G))) = pPrimeCore 2 (normalizer (A : Set G)) ∧
          Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
          let X := (movedComponentSubgroup A (oddActorResidual L A) K).map
            (QuotientGroup.mk' (center K))
          Group.IsPerfect X ∧ Nonempty ((X ⧸ pCore 2 X) ≃* (L ⧸ pCore 2 L)) ∧
          normalizer (X : Set (K ⧸ center K)) =
            (movedComponentSubgroup A (normalizer (L : Set G)) K).map
              (QuotientGroup.mk' (center K)) ∧
          (∀ B : Subgroup (K ⧸ center K), IsPGroup 2 B → B ≠ ⊥ →
            X ≤ normalizer (B : Set (K ⧸ center K)) →
            normalizer (B : Set (K ⧸ center K)) ≤ normalizer (X : Set (K ⧸ center K))) ∧
          Odd (Nat.card (centralizer (X : Set (K ⧸ center K))))))

include D S
/-- Source uniqueness supplies the extra local geometry on the actual moved J₄
component. The original field-four action and order-64 module remain unchanged. -/
theorem outside_local_inner_component_source_case {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    LocalInnerComponentSourceCase D S A := by
  have hs := outside_inner_component_source_case D S hp ho A hne hAe hA hout
  refine ⟨hs,?_⟩
  rcases hs.2.2 with hpush | ⟨hu,K,hK,hm,houtK,hcore,hmodel,haction,hn,hVK,hFK,hc,hi,⟨ek⟩⟩
  · exact Or.inl hpush.1
  · have hodd := odd_card_of_elementary hp ho A hAe
    obtain ⟨hf,⟨e⟩,_⟩ := hs.2.1
    obtain ⟨hperfect,hcover⟩ := moved_projected_cover D S hA hodd K hFK
    exact Or.inr ⟨hu,K,hK,hn,hcore,houtK,hVK,hFK,hc,⟨ek⟩,hperfect,hcover,
      moved_projected_residual_normalizer D S hA hodd hu K hFK,
      moved_projected_two_normalizer hu K hFK,
      moved_janko_residual_centralizer_odd D S hA hodd hu K hFK hf e ek⟩

/-- Failure retains AT=TA and the literal residual's full projected normalizer. -/
theorem failure_local_inner_component_source_case
    (hnot : ¬ OddKernelNormalizer (T := T) (L := L) (V := V)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      LocalInnerComponentSourceCase D S A := by
  unfold OddKernelNormalizer at hnot
  push Not at hnot
  obtain ⟨p,hp,ho,A,hne,he,hA,hperm,hout⟩ := hnot
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_local_inner_component_source_case D S hp ho A hne he hA hout⟩

open ChapterE ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan
/-- The literal Hall kernel supplies the same local-normalizer geometry and odd
residual centralizer. The final J₄ exclusion remains with this task. -/
theorem hall_kernel_local_inner_component_source_case {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H)
    (hk : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      LocalInnerComponentSourceCase D S A := by
  obtain ⟨p,A,hp,ho,hne,he,hA,hperm,hout⟩ := hall_kernel_escape D S hH hlarge hP d hm hk
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_local_inner_component_source_case D S hp ho A hne he hA hout⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The surviving moved branch has a literal nonzero module image and a
maximal two-local normalizer. Its radical is O₂ of that exact normalizer;
none of the four specified native local placements can contain it. -/
def RadicalInnerComponentSourceCase (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (A : Subgroup G) : Prop :=
  LocalInnerComponentSourceCase D S A ∧
    (PushingUpFieldFourCase D S A ∨
      (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
        ∃ (K : Subgroup (normalizer (A : Set G))) (ek : (K ⧸ center K) ≃* Janko4.Model),
          IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧ pCore 2 K = ⊥ ∧
          ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
          V ≤ K.map (normalizer (A : Set G)).subtype ∧
          oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
          centralizer (K : Set (normalizer (A : Set G))) = pPrimeCore 2 (normalizer (A : Set G)) ∧
          let q := QuotientGroup.mk' (center K)
          let X := (movedComponentSubgroup A (oddActorResidual L A) K).map q
          let U := (movedComponentSubgroup A V K).map q
          let P := (normalizer (X : Set (K ⧸ center K))).pCoreIn 2
          Group.IsPerfect X ∧ Nonempty ((X ⧸ pCore 2 X) ≃* (L ⧸ pCore 2 L)) ∧
          IsElementaryAbelian 2 U ∧ U ≠ ⊥ ∧ U ≤ X.pCoreIn 2 ∧ U = ⁅U,X⁆ ∧
          IsPRadical 2 P ∧ normalizer (P : Set (K ⧸ center K)) =
            normalizer (X : Set (K ⧸ center K)) ∧
          IsMaximalTwoLocal (normalizer (X : Set (K ⧸ center K))) ∧
          IsMaximalTwoLocal (normalizer (X.map ek.toMonoidHom : Set Janko4.Model)) ∧
          ¬ NativeJankoLocalContainment (normalizer (X.map ek.toMonoidHom : Set Janko4.Model))))

include D S
/-- Source uniqueness supplies the maximal two-local and its exact radical.
The four concrete placement exclusions use the full original covering quotient. -/
theorem outside_radical_inner_component_source_case {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    RadicalInnerComponentSourceCase D S A := by
  have hs := outside_local_inner_component_source_case D S hp ho A hne hAe hA hout
  refine ⟨hs,?_⟩
  rcases hs.2 with hpush | ⟨hu,K,hK,hn,hcore,houtK,hVK,hFK,hc,⟨ek⟩,hperfect,hcover,_⟩
  · exact Or.inl hpush
  · have hodd := odd_card_of_elementary hp ho A hAe
    obtain ⟨hf,⟨e⟩,_⟩ := hs.1.2.1
    obtain ⟨hU,hUne,hUc,hUm⟩ := moved_projected_module D S hA hodd K hFK
    obtain ⟨hP,hPN,hmax⟩ := moved_projected_radical D S hA hodd hu K hFK
    have hmaxJ := Theory.Quasithin.isMaximalTwoLocal_map ek hmax
    rw [map_equiv_normalizer_eq] at hmaxJ
    exact Or.inr ⟨hu,K,ek,hK,hn,hcore,houtK,hVK,hFK,hc,hperfect,hcover,
      hU,hUne,hUc,hUm,hP,hPN,hmax,hmaxJ,
      moved_janko_normalizer_avoids_native_locals D S hA hodd hu K hFK hf e ek⟩

/-- Failure retains AT=TA and the same actual maximal two-local normalizer,
with its radical and the original fully moved module image. -/
theorem failure_radical_inner_component_source_case
    (hnot : ¬ OddKernelNormalizer (T := T) (L := L) (V := V)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      RadicalInnerComponentSourceCase D S A := by
  unfold OddKernelNormalizer at hnot
  push Not at hnot
  obtain ⟨p,hp,ho,A,hne,he,hA,hperm,hout⟩ := hnot
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_radical_inner_component_source_case D S hp ho A hne he hA hout⟩

open ChapterE ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan
/-- The literal Hall kernel supplies the same radical and placement obstruction.
Exhaustive J₄ placement remains with this task; ordinary C.2.8 remains with
qt-d-1222-natural-point-fixed-summand and final 11.2.1 with the weak-closure owner. -/
theorem hall_kernel_radical_inner_component_source_case {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H)
    (hk : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      RadicalInnerComponentSourceCase D S A := by
  obtain ⟨p,A,hp,ho,hne,he,hA,hperm,hout⟩ := hall_kernel_escape D S hH hlarge hP d hm hk
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_radical_inner_component_source_case D S hp ho A hne he hA hout⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The radical source configuration, together with even index of every literal
J₄ residual normalizer under source uniqueness. In particular the same component
witness in the radical case has this property; no new placement is assumed. -/
def EvenIndexInnerComponentSourceCase (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (A : Subgroup G) : Prop :=
  RadicalInnerComponentSourceCase D S A ∧
    (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) →
      ∀ (K : Subgroup (normalizer (A : Set G))) (ek : (K ⧸ center K) ≃* Janko4.Model),
        oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype →
        let X := ((movedComponentSubgroup A (oddActorResidual L A) K).map
          (QuotientGroup.mk' (center K))).map ek.toMonoidHom
        2 ∣ (normalizer (X : Set Janko4.Model)).index)

include D S
/-- The actual source failure excludes every full-Sylow local placement of its
J₄ residual normalizer, using the full covering quotient and odd centralizer. -/
theorem outside_even_index_inner_component_source_case {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    EvenIndexInnerComponentSourceCase D S A := by
  have hs := outside_radical_inner_component_source_case D S hp ho A hne hAe hA hout
  refine ⟨hs,?_⟩
  intro hu K ek hFK
  obtain ⟨hf,⟨e⟩,_⟩ := hs.1.1.2.1
  exact moved_janko_normalizer_even_index D S hA (odd_card_of_elementary hp ho A hAe)
    hu K hFK hf e ek

/-- The exact odd-normalizer failure retains AT=TA and the even-index obstruction
on the same projected residual as its radical source case. -/
theorem failure_even_index_inner_component_source_case
    (hnot : ¬ OddKernelNormalizer (T := T) (L := L) (V := V)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      EvenIndexInnerComponentSourceCase D S A := by
  unfold OddKernelNormalizer at hnot
  push Not at hnot
  obtain ⟨p,hp,ho,A,hne,he,hA,hperm,hout⟩ := hnot
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_even_index_inner_component_source_case D S hp ho A hne he hA hout⟩

open ChapterE ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan
/-- Apply the even-index reduction to the literal elementary Hall kernel.
The remaining even-index J₄ placement stays with this task, ordinary C.2.8 with
qt-d-1222-natural-point-fixed-summand, and final 11.2.1 with the weak-closure owner. -/
theorem hall_kernel_even_index_inner_component_source_case {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H)
    (hk : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      EvenIndexInnerComponentSourceCase D S A := by
  obtain ⟨p,A,hp,ho,hne,he,hA,hperm,hout⟩ := hall_kernel_escape D S hH hlarge hP d hm hk
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_even_index_inner_component_source_case D S hp ho A hne he hA hout⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The original remaining source configuration retains the elementary 64 in
its literal J₄ central quotient, including residual transitivity and the
single ambient involution class of its nonidentity elements. -/
def NaturalOrbitInnerComponentSourceCase (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (A : Subgroup G) : Prop :=
  EvenIndexInnerComponentSourceCase D S A ∧
    ∀ (K : Subgroup (normalizer (A : Set G))) (ek : (K ⧸ center K) ≃* Janko4.Model),
      oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype →
      let q := QuotientGroup.mk' (center K)
      let X := ((movedComponentSubgroup A (oddActorResidual L A) K).map q).map ek.toMonoidHom
      let U := ((movedComponentSubgroup A V K).map q).map ek.toMonoidHom
      IsElementaryAbelian 2 U ∧ Nat.card U = 64 ∧
        (∀ u ∈ U, ∀ v ∈ U, u ≠ 1 → v ≠ 1 → ∃ x ∈ X, x * u * x⁻¹ = v) ∧
        ((∀ u ∈ U, u ≠ 1 → IsConj Janko4.a u) ∨
          (∀ u ∈ U, u ≠ 1 → IsConj ((Janko4.a * Janko4.b * Janko4.a *
            Janko4.b * Janko4.b) ^ 5) u))

include D S
/-- The actual failure supplies transitivity on the original module image,
without an additional normalizer, representation or local-placement premise. -/
theorem outside_natural_orbit_inner_component_source_case {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    NaturalOrbitInnerComponentSourceCase D S A := by
  have hs := outside_even_index_inner_component_source_case D S hp ho A hne hAe hA hout
  refine ⟨hs,?_⟩
  intro K ek hFK
  obtain ⟨hf,⟨e⟩,_⟩ := hs.1.1.1.2.1
  exact moved_janko_module_pure D S hA (odd_card_of_elementary hp ho A hAe)
    K hFK hf e ek

/-- Failure retains AT=TA, the even-index maximal two-local and the same
original elementary 64 with its actual residual conjugation orbit. -/
theorem failure_natural_orbit_inner_component_source_case
    (hnot : ¬ OddKernelNormalizer (T := T) (L := L) (V := V)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      NaturalOrbitInnerComponentSourceCase D S A := by
  unfold OddKernelNormalizer at hnot
  push Not at hnot
  obtain ⟨p,hp,ho,A,hne,he,hA,hperm,hout⟩ := hnot
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_natural_orbit_inner_component_source_case D S hp ho A hne he hA hout⟩

open ChapterE ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan
/-- Apply the original-module orbit reduction to the literal elementary Hall kernel.
The remaining even-index J₄ placement stays with this task, ordinary C.2.8 with
qt-d-1222-natural-point-fixed-summand, and final 11.2.1 with the weak-closure owner. -/
theorem hall_kernel_natural_orbit_inner_component_source_case {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H)
    (hk : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      NaturalOrbitInnerComponentSourceCase D S A := by
  obtain ⟨p,A,hp,ho,hne,he,hA,hperm,hout⟩ := hall_kernel_escape D S hH hlarge hP d hm hk
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_natural_orbit_inner_component_source_case D S hp ho A hne he hA hout⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The actual pure order-64 image has the same full normalizer as the residual
and lies in the center of that normalizer's radical. The native J₄ equality
uses the same component marking as the retained purity statement. -/
def NormalizedNaturalInnerComponentSourceCase (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) (A : Subgroup G) : Prop :=
  NaturalOrbitInnerComponentSourceCase D S A ∧
    (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) →
      ∀ (K : Subgroup (normalizer (A : Set G))) (ek : (K ⧸ center K) ≃* Janko4.Model),
        oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype →
        let q := QuotientGroup.mk' (center K)
        let X := (movedComponentSubgroup A (oddActorResidual L A) K).map q
        let U := (movedComponentSubgroup A V K).map q
        normalizer (X : Set (K ⧸ center K)) = normalizer (U : Set (K ⧸ center K)) ∧
          U ≤ centerIn ((normalizer (X : Set (K ⧸ center K))).pCoreIn 2) ∧
          normalizer (X.map ek.toMonoidHom : Set Janko4.Model) =
            normalizer (U.map ek.toMonoidHom : Set Janko4.Model))

include D S
/-- The actual failure identifies the full normalizer of the original module
and places that module in the radical center, with no new hypothesis. -/
theorem outside_normalized_natural_inner_component_source_case {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    NormalizedNaturalInnerComponentSourceCase D S A := by
  have hs := outside_natural_orbit_inner_component_source_case D S hp ho A hne hAe hA hout
  refine ⟨hs,?_⟩
  intro hu K ek hFK
  obtain ⟨hf,⟨e⟩,_⟩ := hs.1.1.1.1.2.1
  have hodd := odd_card_of_elementary hp ho A hAe
  exact ⟨moved_projected_module_normalizer D S hA hodd hu K hFK hf e ek,
    moved_projected_module_central_radical D S hA hodd hu K hFK hf e ek,
    moved_janko_module_normalizer D S hA hodd hu K hFK hf e ek⟩

/-- Failure retains AT=TA and the exact full normalizer of the original
pure elementary 64, including its containment in the radical center. -/
theorem failure_normalized_natural_inner_component_source_case
    (hnot : ¬ OddKernelNormalizer (T := T) (L := L) (V := V)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      NormalizedNaturalInnerComponentSourceCase D S A := by
  unfold OddKernelNormalizer at hnot
  push Not at hnot
  obtain ⟨p,hp,ho,A,hne,he,hA,hperm,hout⟩ := hnot
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_normalized_natural_inner_component_source_case D S hp ho A hne he hA hout⟩

open ChapterE ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan
/-- Apply the full original-module normalizer geometry to the literal Hall kernel.
Excluding this particular pure-64 normalizer stays with this task, ordinary C.2.8 with
qt-d-1222-natural-point-fixed-summand, and final 11.2.1 with the weak-closure owner. -/
theorem hall_kernel_normalized_natural_inner_component_source_case {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H)
    (hk : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      NormalizedNaturalInnerComponentSourceCase D S A := by
  obtain ⟨p,A,hp,ho,hne,he,hA,hperm,hout⟩ := hall_kernel_escape D S hH hlarge hP d hm hk
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_normalized_natural_inner_component_source_case D S hp ho A hne he hA hout⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The original natural module is the whole elementary center of the
radical of its full normalizer. Its 63 nonidentity vectors are all in the
first native J₄ involution class under the unchanged component marking. -/
def CentralNaturalInnerComponentSourceCase (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) (A : Subgroup G) : Prop :=
  NormalizedNaturalInnerComponentSourceCase D S A ∧
    (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) →
      ∀ (K : Subgroup (normalizer (A : Set G))) (ek : (K ⧸ center K) ≃* Janko4.Model),
        oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype →
        let q := QuotientGroup.mk' (center K)
        let X := (movedComponentSubgroup A (oddActorResidual L A) K).map q
        let U := (movedComponentSubgroup A V K).map q
        U = omegaCenterIn ((normalizer (X : Set (K ⧸ center K))).pCoreIn 2) ∧
          ∀ u ∈ U.map ek.toMonoidHom, u ≠ 1 → IsConj Janko4.a u)

include D S
/-- The actual failure identifies the original module as the elementary radical
center and excludes its second involution-class alternative, with no extra premise. -/
theorem outside_central_natural_inner_component_source_case {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    CentralNaturalInnerComponentSourceCase D S A := by
  have hs := outside_normalized_natural_inner_component_source_case D S hp ho A hne hAe hA hout
  refine ⟨hs,?_⟩
  intro hu K ek hFK
  obtain ⟨hf,⟨e⟩,_⟩ := hs.1.1.1.1.1.2.1
  have hodd := odd_card_of_elementary hp ho A hAe
  exact ⟨moved_projected_module_eq_omega_center D S hA hodd hu K hFK hf e ek,
    moved_janko_module_first_class D S hA hodd hu K hFK hf e ek⟩

/-- Failure retains AT=TA and the original elementary 64 as the elementary
radical center, with its actual first-class fusion. -/
theorem failure_central_natural_inner_component_source_case
    (hnot : ¬ OddKernelNormalizer (T := T) (L := L) (V := V)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      CentralNaturalInnerComponentSourceCase D S A := by
  unfold OddKernelNormalizer at hnot
  push Not at hnot
  obtain ⟨p,hp,ho,A,hne,he,hA,hperm,hout⟩ := hnot
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_central_natural_inner_component_source_case D S hp ho A hne he hA hout⟩

open ChapterE ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan
/-- Apply the elementary radical-center and first-class result to the literal Hall kernel.
Excluding this particular 2A-pure normalizer stays with this task, ordinary C.2.8 with
qt-d-1222-natural-point-fixed-summand, and final 11.2.1 with the weak-closure owner. -/
theorem hall_kernel_central_natural_inner_component_source_case {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H)
    (hk : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧
      A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      CentralNaturalInnerComponentSourceCase D S A := by
  obtain ⟨p,A,hp,ho,hne,he,hA,hperm,hout⟩ := hall_kernel_escape D S hH hlarge hP d hm hk
  exact ⟨p,A,hp,ho,hne,he,hA,hperm,hout,
    outside_central_natural_inner_component_source_case D S hp ho A hne he hA hout⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The uniform elementary-normalizer theorem eliminates the moved-inner
disjunct of the original source reduction. Its application uses the original
V, the same actual component and its full central quotient. Only the ordinary
full-W pushing-up case remains. -/
theorem outside_pushingUpFieldFourCase_of_native_cover
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : NativeElementaryNormalizerCover C)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    PushingUpFieldFourCase D S A := by
  obtain ⟨_,⟨hf,⟨e⟩,_⟩,hcases⟩ :=
    outside_inner_component_source_case D S hp ho A hne hAe hA hout
  rcases hcases with ⟨hpush,_⟩ |
    ⟨hu,K,_,_,_,_,_,_,_,_,hFK,_,_,⟨ek⟩⟩
  · exact hpush
  · exact (moved_janko_false_of_elementary_cover D S C eC hcover hA
      (odd_card_of_elementary hp ho A hAe) hu K hFK hf e ek).elim

/-- Conditional nonbinary specialization of 4.4.3 and Remark 4.4.2. The only
remaining inputs are the independent uniform native cover and the shared
ordinary full-W theorem; neither is asserted to have been proved here.
Final discharge belongs to this odd-normalizer owner. -/
theorem oddKernelNormalizer_of_native_cover
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : NativeElementaryNormalizerCover C)
    (hordinary : OrdinaryFullModuleExclusion D S) :
    OddKernelNormalizer (T := T) (L := L) (V := V) := by
  intro p hp ho A hne hAe hA _
  by_contra hout
  exact pushingUpFieldFourCase_false_of_ordinary D S hordinary
    (outside_pushingUpFieldFourCase_of_native_cover D S C eC hcover hp ho A hne hAe hA hout)

open ChapterE ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan

/-- The conditional normalizer theorem kills the literal elementary kernel
of the actual Hall actor used in 11.2.1. All Hall inclusion and quotient maps
are those of Generation.Hall; no new faithfulness premise is introduced. -/
theorem hall_faithful_of_native_cover
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : NativeElementaryNormalizerCover C)
    (hordinary : OrdinaryFullModuleExclusion D S)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H) :
    d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) = ⊥ :=
  hall_faithful D S (oddKernelNormalizer_of_native_cover D S C eC hcover hordinary)
    hH hlarge hP d hm

include D S

/-- The original nonbinary odd-kernel normalizer conclusion under the uniform
native cover alone. The shared ordinary C.2.8 proof discharges the full-W
input; the moved-inner branch uses the image of the original V. The native
cover and its actual third-local quotient still require their producer. -/
theorem oddKernelNormalizer_of_elementary_cover
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : NativeElementaryNormalizerCover C) :
    OddKernelNormalizer (T := T) (L := L) (V := V) :=
  oddKernelNormalizer_of_native_cover D S C eC hcover
    (ordinaryFullModuleExclusion_of_elementary_cover D S C eC hcover)

/-- Faithfulness of the actual Hall actor with the ordinary callback
discharged. Only the independent uniform native cover and its literal
linear-five quotient remain; all Hall and component maps are unchanged. -/
theorem hall_faithful_of_elementary_cover
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : NativeElementaryNormalizerCover C)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H) :
    d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) = ⊥ :=
  hall_faithful D S (oddKernelNormalizer_of_elementary_cover D S C eC hcover)
    hH hlarge hP d hm

/-- Use the proved native third local and its full intrinsic two-core quotient.
The only remaining input is uniform coverage by the four fixed native locals;
the full ordinary W and original moved V are retained by the preceding assembly.
The cover producer must still prove this premise before final source discharge. -/
theorem oddKernelNormalizer_of_native_four_local_cover
    (hcover : NativeElementaryNormalizerCover Janko4.LocalStructure.LinearFive.M_F) :
    OddKernelNormalizer (T := T) (L := L) (V := V) :=
  oddKernelNormalizer_of_elementary_cover D S Janko4.LocalStructure.LinearFive.M_F
    (Janko4.LocalStructure.LinearFive.M_F_intrinsicQuotient.trans
      Representation.SL5TenDimensional.projectiveEquiv) hcover

/-- The same fixed native cover gives faithfulness of the literal Hall actor.
The embedded third local and its quotient are supplied by their proved native
construction, with no additional quotient or ordinary-exclusion premise. -/
theorem hall_faithful_of_native_four_local_cover
    (hcover : NativeElementaryNormalizerCover Janko4.LocalStructure.LinearFive.M_F)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H) :
    d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) = ⊥ :=
  hall_faithful D S (oddKernelNormalizer_of_native_four_local_cover D S hcover)
    hH hlarge hP d hm

open Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA
open Janko4.LocalStructure.LinearFive (M_F M_F_eq_fullNormalizer M_F_intrinsicQuotient)
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

omit D S in
private theorem source_conjugate_eq_first (g : Janko4.Model) :
    sourceSubgroup.map (MulAut.conj g).toMonoidHom =
      Janko4.InvolutionCentralizers.First.centralizer.map
        (MulAut.conj (g * h)).toMonoidHom := by
  rw [firstCentralizer_eq_source_conjugate, map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

omit D S in
/-- The completed native four-local theorem in the exact interface consumed by
the odd-kernel source.  Each branch keeps its literal ambient conjugator; the
third branch is the embedded `M_F` local with its intrinsic PSL₅ quotient. -/
theorem native_elementary_normalizer_cover :
    NativeElementaryNormalizerCover M_F := by
  intro E hE hEE
  let := hEE
  obtain ⟨i,g,hg⟩ :=
    Janko4.LocalStructure.PureFirstNormalizers.CompleteCover.elementary_normalizer_cover_unconditional
      E hE
  fin_cases i
  · exact Or.inl ⟨g, hg⟩
  · refine Or.inr (Or.inl ⟨g * h, ?_⟩)
    change normalizer (E : Set Janko4.Model) ≤
      sourceSubgroup.map (MulAut.conj g).toMonoidHom at hg
    rwa [source_conjugate_eq_first] at hg
  · refine Or.inr (Or.inr (Or.inl ⟨g, ?_⟩))
    rw [M_F_eq_fullNormalizer]
    exact hg
  · exact Or.inr (Or.inr (Or.inr ⟨g, hg⟩))

/-- Unconditional nonbinary specialization of source 4.4.3 and Remark 4.4.2.
The original `V`, the literal `AT = TA` premise and all component/Hall maps are
retained by `OddKernelNormalizer`; no maximal-Sylow shortcut is used. -/
theorem oddKernelNormalizer_unconditional :
    OddKernelNormalizer (T := T) (L := L) (V := V) :=
  oddKernelNormalizer_of_native_four_local_cover D S native_elementary_normalizer_cover

/-- Faithfulness of the literal Hall actor after discharging the completed
native cover. -/
theorem hall_faithful_unconditional
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H) :
    d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) = ⊥ :=
  hall_faithful D S (oddKernelNormalizer_unconditional D S) hH hlarge hP d hm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
