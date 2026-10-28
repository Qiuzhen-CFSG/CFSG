module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.Numerical
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.Faithful
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.Small
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.StarSource
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.FieldCoprime
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.Minimum
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.RootLift
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.RootSpanTI
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.SourceRoot
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.ModelCartan
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.Overcomponent
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.OvercomponentRanks
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.OvercomponentSections
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.OvercomponentBender
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.OvercomponentRankOne
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.OvercomponentSplit
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.OvercomponentBinary
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.OvercomponentG2
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.OvercomponentTriality
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.SplitTorsion

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.Suzuki
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.RankOneFFSource
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.FFSource
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.FFOrbit
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.FFAssembly

/-!
# The original component, binary models, and faithful maximal overcomponent

Construct the component from the actual 11.3.2 counterexample, extend it
to a faithful maximal local component, and apply the numerical model sieve
at n(H) > 1. Normality here is relative to H. In the normal branch the
model carrier is the literal image in H/core_H(M); in the paired branch
it is the actual K/O₂(K). Every model comes with a concrete isomorphism
and a field exponent bounding the original generation minimum.

The re-exported field-four result completes the parameter and outside-component
conclusion in that concrete row, under the original natural marking and
preceding residual clauses.

The re-exported StarSource catalogue identifies the normal binary PSL₂
and Suzuki rows on K/O₂(K) as well, using the original projection rather
than an assumed central-cover identification. In those rows it also proves
R(H) = O₂(H); the higher-rank alternatives remain on the star image.

The FieldCoprime extension further forces a paired PSL₂ exponent f to satisfy
n < f and gcd(n,f)=1 under the original marking and preceding residual clauses.
It completes the parameter/component conclusion whenever the literal model
has the original field degree, without a recognition-at-the-minimum premise.

The HallTorus and HallProduct extensions identify the whole actual paired
Hall subgroup with the product of its two cyclic factors of order 2^f-1,
using the same exchange element. FixedPoints chooses the prime by parity
of n and proves square centralization from the original field-power action,
then constructs a nonidentity fixed diagonal while retaining the moved point.
CartanExclusion now uses these witnesses in the mixed-action contradiction.

The Minimum extension proves the missing lower bound in the normal PSL₂ row
when an actual elementary subgroup of H maps onto the full root Sylow in
H/O₂(H). It then recognizes the model at n(H) and constructs RankOneReduction
for that row. RootLift now constructs an actual elementary subgroup of the
prescribed Sylow with quotient-image rank at least n(H). In the normal PSL₂
row its image either lies in the original root or forces f = 2m with
n(H) ≤ m+1. Root-normalizer invariance of a nonzero image constructs the full
root lift and completes this normal-row recognition. RootSpan constructs
its actual normalizer-conjugate span inside the prescribed Sylow, with full
root image. Failure of commutativity gives explicit nontrivial commutators
in O₂(H).

RootSpanTI applies the original TI property to V intersected with the root
preimage. Its conjugate span is elementary. The faithful PSL₂ root centralizer
then shows that this intersection has nonzero image whenever V escapes
O₂(H). Thus this branch now has a constructed full elementary lift and
recognition at the genuine generation minimum, including even model degrees
and outer actions. The remaining normal PSL₂ case has V ≤ O₂(H), while
11.3.3 puts its actual weak closure outside O₂(H).

The Overcomponent extension proves Sylow normalization of every local
overcomponent of a normal seed. Omega-center movement makes its actual
reduced module nontrivial, and homogeneous selection constructs a chosen
module. The source catalogue now supplies these objects in the higher-rank
rows without assuming an overcomponent model or an FF conclusion.
OvercomponentRanks discharges its quasisimple-quotient premise in every
symplectic-four row, the even-degree linear-three rows, and the odd-degree
unitary-three rows. The literal star projection supplies cubic rank two,
which passes to the containing local component and excludes the
noncentral-Fitting alternatives. The refined source catalogue includes
the full chosen-module setup in these rows. OvercomponentSections completes
both signed-three parities and the Suzuki containing-quotient setup: the
nonquasisimple alternative would make the seed's simple image a prime-field
PSL₂ group. Actual two-ranks exclude that identification, with the order
62400 handling PSU₃(4). Its original-catalogue application discharges every
simple-image premise through the same minimal-parabolic projection.

OvercomponentBender proves non-enlargement through every Bender containing
two-core quotient. Its concrete Sylow, rank and order comparisons then
exclude binary PSL₂ containing quotients in all non-PSL₂ source rows,
including both signed-three parities and every Suzuki field degree.

OvercomponentRankOne excludes every Bender containing quotient in the
linear-three and symplectic-four rows using their two genuine parabolics.
It separates Suzuki and unitary quotients in both directions by divisibility
by three, and identifies a surviving unitary Bender overcomponent with the
original seed at its actual field exponent. The refined original catalogue
retains every quotient map and the independent generation-parameter bound.

OvercomponentSplit handles SL₃, PSL₃, Sp₄ and G₂ containing quotients.
A proper seed has the actual PSL₂ quotient at the containing field exponent,
so a higher-rank seed cannot be enlarged there. The original catalogue now
excludes these four containing models for Suzuki and unitary seeds, using
the literal central star projection for the latter. Linear-three and
symplectic-four seeds must equal a split containing component.

OvercomponentBinary excludes PSL₃(2), PSL₄(2) and PSL₅(2) containing
quotients for every original seed. Their intrinsic local quotients have
binary degree between three and five. Degree three gives n(H) ≤ 1 via
PSL₂(7); cubic rank forces relative normality in degrees four and five,
whose two-core images contradict the original minimal parabolicity.
The original-catalogue application preserves the independent field exponents.

OvercomponentG2 excludes a G₂ quotient for the original seed in both
relative-normality branches. It therefore proves the seed is proper in
every nonbinary G₂ overcomponent and identifies its literal quotient as
PSL₂ at the containing field exponent. Higher-rank star images consequently
exclude all such containers. The original catalogue retains this recognition
and the three small binary containing-row exclusions together.

OvercomponentTriality excludes a triality quotient for the original seed
and treats every positive containing field degree, including ³D₄(2).
The seed is proper, and its actual two-core quotient is PSL₂ at degree f
or 3f. The central degree-f branch requires f ≥ 2; field two therefore
forces PSL₂(8). Suzuki and higher-rank star rows exclude triality containers.
The original catalogue retains both independent root exponents.

This also supplies the opening model and overcomponent construction of 11.3.5.
It does not yet exclude Suzuki, unitary or rank-two models. Those model/FF
obligations and final RankOneReduction assembly remain with the
parameter-component owner. The linear-geometry
owner retains final discharge of the preceding source bound n ≤ s(G,V).
SourceRoot retains an actual conjugate V^g from the source weak closure.
Its action and core quotient images have the same kernel. Its root intersection
is therefore nonzero even when its image contains outer automorphisms. Saturation
now leaves only a nontrivial core commutator between that same source conjugate
and its conjugate under H ∩ N_G(L), or recognition at generationParameter H.
The unresolved commutator branch still retains V ≤ O₂(H).

SourceAlternatives assembles all four clauses of 11.3.4 from the exact
preceding generation and global-s clauses. Recognition/Source connects the
paired collapse and doubled exclusion to the actual residual-component
conclusion. The normal escaping-V and matching-field branches are complete;
without the odd-kernel input, its surviving normal PSL₂ core obstruction
requires n<f.

ModelCartan now uses that genuine preceding odd-kernel normalizer input to
make the original Hall actor faithful at the actual model exponent f. The
original and doubled automizer bounds, together with the doubled weak-closure
lower bound, give f = generationParameter H in every normal or paired binary
row. This completes the PSL₂ residual-component conclusion even when V≤O₂(H).
Its original-catalogue consumer constructs the faithful maximal overcomponent
and preserves the higher-rank star images and literal paired quotients.
The earlier-source inputs and remaining Suzuki/unitary/rank-two model/FF
exclusions are still explicit obligations.

Paired/Suzuki completes the paired exclusion in both binary rank-one rows.
Its q−1 divisor is proved on the original Suzuki component overlap, then
used with the actual Hall subgroup and Sylow exchange element in the shared
Cartan contradiction. Every source seed is now normal relative to H and
equals the embedded O²(H). The residual catalogue retains its faithful
maximal overcomponent and the higher-rank star models. The normal Suzuki,
unitary and rank-two FF exclusions remain necessary.

RankOneFF proves that a literal Suzuki or unitary-three quotient excludes
FF for the full linear normalizer on every actual chosen Irr⁺ space,
including its fixed layer. RankOneFFSource applies this to the original
containing component: the Bender/FF branch now gives the PSL₂ seed and
complete parameter/residual conclusion. FF existence and the remaining
containing models are still necessary for the unconditional source result.

FFContaining and FFOrders supply the complete full-normalizer containing
shortlist and exclude its finite exceptional rows using actual root-subgroup
orders. FFSource eliminates every Suzuki and unitary source row with an FF
chosen overcomponent, with no assumed containing model. The original catalogue
now leaves PSL₂, which has the complete residual-component conclusion, or a
natural SL₃/Sp₄ seed equal to its maximal overcomponent and to the embedded
O²(H).

FFOrbit completes the rank-two exclusion when the original Sylow orbit is FF.
The proved source 3.2.5 alternatives and doubled-orbit classification supply
Sylow normalization; the literal natural central-quotient action then preserves
two parabolic types, contradicting the original minimal parabolicity.
FFAssembly uses both original 7.0.1 exits to obtain the PSL₂ model and the
full parameter/residual conclusion. It constructs the source seed, faithful
maximal container and chosen module before applying that earlier source
implication. Its only additional input is the normalized 7.0.1 statement,
owned by qt-d-1222-normalized-nonff; final discharge remains necessary.

Source: Aschbacher--Smith, 11.3.5(1), pp.771–772, using E.2.2 and 1.2.9.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H : Subgroup G}

/-- The numerical recognition reduction on the original source counterexample.
The component, its faithful maximal overcomponent and its binary model are
all constructed; the model exponent is not relabelled as n(H). -/
theorem exists_componentSeed_with_binary_models
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary) :
    let P := T.subtype h.outside.1.1.2
    let hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
    ∃ K J : Subgroup G, ComponentSeed T H K ∧ K ≤ J ∧
      J ∈ Chapter1.LStar G (T : Subgroup G) ∧
      J ∈ MainForward.faithfulLocalComponents T ∧
      ¬ J ≤ normalizer (L : Set G) ∧ ⁅sourceZ T,J⁆ ≠ ⊥ ∧
      (((K.subgroupOf H).Normal ∧
        (let I := sourceImage (ChapterB.minimalParabolicMax P hP) (K.subgroupOf H)
         ∃ f : ℕ, 2 ≤ f ∧ ChapterE.generationParameter H ≤ f ∧
           (ClassicalGroup.IsPSL I 2 (2 ^ f) ∨ ClassicalGroup.IsPSU I 3 (2 ^ f) ∨
             ClassicalGroup.IsPSL I 3 (2 ^ f) ∨ ClassicalGroup.IsPSp I 2 (2 ^ f) ∨
             ∃ m : ℕ, 1 ≤ m ∧ f = 2 * m + 1 ∧
               Nonempty (I ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)))) ∨
       (¬ (K.subgroupOf H).Normal ∧
         ((∃ f : ℕ, 2 ≤ f ∧ ChapterE.generationParameter H ≤ f ∧
             ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) ∨
          (∃ m : ℕ, 1 ≤ m ∧ ChapterE.generationParameter H ≤ 2 * m + 1 ∧
             Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))))) := by
  obtain ⟨K,J,s,hKJ,hJ,hf,ho,hm⟩ := exists_componentSeed_with_faithful_maximal h pr hc hs
  refine ⟨K,J,s,hKJ,hJ,hf,ho,hm,?_⟩
  by_cases hn : (K.subgroupOf H).Normal
  · exact Or.inl ⟨hn,s.normal_binary_models h pr hc hs hn⟩
  · exact Or.inr ⟨hn,s.paired_binary_models h pr hc hs hn⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
