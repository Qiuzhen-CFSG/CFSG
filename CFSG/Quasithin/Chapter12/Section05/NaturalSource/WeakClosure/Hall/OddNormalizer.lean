module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.OddLocalRee
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.OddLocalComponent
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.OddLocalSeed
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.OddLocalAction
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpContradiction
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpModuleControl
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpNormalizer
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpCommutator
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpComponentEquality
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpRankTwoProperModels
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpRemainingProperModels
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpReducedProperModels
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpProperModels
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpPumpup
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpOrdinaryPumpup

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.LocalModels
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.OuterModels
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.OuterSmallSylow
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.OuterMcL
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.OuterSymplectic
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.OuterG2
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.OuterLinear
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.OuterUnitary
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.JankoResidual
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.MathieuObstruction
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUp
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpComponents
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpCubic
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpMathieu
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpResidual
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpQuasisimple
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.Reduction
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.Primitive

/-!
# Exterior odd-normalizer control and the literal Hall consumer

The original exterior marking supplies the section-centralizer condition,
the odd-core bound and the exceptional-quotient exclusions in 4.4.3. An outside
normalizer constructs either a pushing-up configuration or a component moved
by the original exterior module. The outer-action sieve and placed-component
analysis retain only the full J₄ central cover.

The p.612 pushing-up branch is excluded. Its original cubic residual is a
normal ordinary M₂₂ component; the full-cover radical splitting provides an
actual involution fixed modulo V. Coprime lifting and relative Sylow
maximality give the required commutator contradiction.

The distinct p.623 branch retains the full residual at the marking's original
involution and its containing normal C-component Q in C_G(z). Trivial action
on (Q/O₂(Q))/Z(Q/O₂(Q)) makes Q itself the comparison subgroup and contradicts
the marked residual obstruction. Otherwise the original actor induces an
automorphism of exact prime order p > 3 fixing an actual M₂₂ section.
Section ranks, Sylow exponents, native Mathieu order spectra and the HS
point-stabilizer calculation leave binary G₂, triality, Ree F₄ and J₄.
The actual J₄ involution centralizers now exclude its odd-prime row. In
the three remaining binary families, the original residual has a quasisimple
two-core quotient, and its literal image is a quasisimple M₂₂ cover which
normalizes no nontrivial two-subgroup. The lifted eleven-by-five subgroup
and self-duality now exclude both binary G₂ and triality through their
actual degree-eight actions. The remaining Ree F₄ row is excluded by lifting
the actual Mathieu hexad local through the full residual-image quotient:
its two-local normalizer has order divisible by fifteen, contrary to the
Ree parabolic order bound. This completes ExteriorOddNormalizerControl.

Each reduction is applied to the literal Hall counterexample, preserving the
full covers, quotient maps, original exterior module and relative Sylow data.
The independent action premise remains with qt-d-1251-fusion-hall.
Structural1222At is produced by qt-d-1222-source and discharged by
qt-d-1251-source.

Source: Aschbacher--Smith, 12.2.11(a), pp.798--799, and 4.4.1--12, pp.619--623.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- Concrete remaining source configurations on the original actor and
module. This is an obstruction to be excluded, not a classification theorem. -/
def ExteriorOddNormalizerSourceCase (s : SylowExteriorMarking D) (A : Subgroup G) : Prop :=
  (∃ J H W : Subgroup G,
    PushLE L (oddActorResidual L A) J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
    H ⊓ s.marking.M < H ∧ V ≤ J.pCoreIn 2 ∧
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ s.marking.M) LH
      (J.pCoreIn 2) W ∧
    (L : Set G) = (LH : Set G) * (L.pCoreIn 2 : Set G) ∧
    (LH.subgroupOf (H ⊓ s.marking.M)).Normal ∧
    Nonempty ((LH ⧸ pCore 2 LH) ≃* Representation.SL5TenDimensional.Group) ∧
    ¬ OddNormalizerExceptionalQuotient (LH ⧸ pCore 2 LH) ∧
    1024 ≤ Nat.card W ∧
    ∃ c : sectionCentralizerIn s.marking.M L,
      V.map (MulAut.conj (c : G)).toMonoidHom ≤ W) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
      normalizer (K : Set (normalizer (A : Set G))) ∧
    V.subgroupOf (normalizer (A : Set G)) ≤
      normalizer (K : Set (normalizer (A : Set G))))

/-- Construct the remaining source cases from an actual outside normalizer. -/
theorem exterior_oddNormalizer_source_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerSourceCase s A := by
  classical
  by_cases hu : UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M
  · exact Or.inr (exterior_oddNormalizer_component_of_core_eq_bot s h p hp hpgt
      A hne hAe hAM hAV (oddNormalizer_reduction_of_cover_uniqueness D A hu hout).2)
  · have ho : Odd (Nat.card A) := by
      let : Fact p.Prime := ⟨hp⟩
      let := hAe
      obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
      rw [hn]
      exact (hp.odd_of_ne_two (by omega)).pow
    obtain ⟨J,H,W,hpush,hH,hJH,hstrict,hVJ,hC,hcover,hN,he,hno,_,_,_,_,_,hsize,hmark⟩ :=
      exterior_oddActorResidual_pushingUp_configuration s h A hAM ho hAV
        (exterior_component_sylow_unique s h) hu
    exact Or.inl ⟨J,H,W,hpush,hH,hJH,hstrict,hVJ,hC,hcover,hN,he,hno,hsize,hmark⟩

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- Literal application to the Hall subgroup constructed by E.2.2: failure
of its three-group conclusion constructs one of the remaining source cases.
The independent action premise is retained, and no normalizer control is assumed. -/
theorem exterior_hall_counterexample_source_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      ExteriorOddNormalizerSourceCase s A := by
  classical
  have hc : ¬ ExteriorOddNormalizerControl s := fun hc => hnot
    (exterior_hall_three_of_controls s h structural action hc hH hHGi hlarge hP d hmax)
  unfold ExteriorOddNormalizerControl at hc
  push Not at hc
  obtain ⟨p,hp,hpgt,A,hne,hAe,hAM,hAV,hout⟩ := hc
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,
    exterior_oddNormalizer_source_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- Failure of residual uniqueness retains the constructed pushing-up source
case. In the unique branch the selected component satisfies the proved model
exclusions, on its original carrier and original residual action. -/
def ExteriorOddNormalizerRefinedCase (s : SylowExteriorMarking D) (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorOddNormalizerSourceCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    ExteriorOddNormalizerComponentCase s A K)

/-- Construct the refined remaining cases from the unchanged original
hypotheses, with no uniqueness or component-exclusion hypothesis added. -/
theorem exterior_oddNormalizer_refined_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerRefinedCase s A := by
  classical
  by_cases hu : UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M
  · obtain ⟨K, hK, hm, houtK, hc, hmodel, _, _⟩ :=
      exterior_oddNormalizer_component_of_core_eq_bot s h p hp hpgt A hne hAe hAM hAV
        (oddNormalizer_reduction_of_cover_uniqueness D A hu hout).2
    have ho : Odd (Nat.card A) := by
      let : Fact p.Prime := ⟨hp⟩
      let := hAe
      obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
      rw [hn]
      exact (hp.odd_of_ne_two (by omega)).pow
    exact Or.inr ⟨K, hK, hm, houtK, hc, hmodel,
      exterior_oddNormalizer_component_cases s h A hAM ho hAV hu hout K hK houtK hmodel⟩
  · exact Or.inl ⟨hu, exterior_oddNormalizer_source_case s h p hp hpgt A hne hAe hAM hAV hout⟩

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- Apply the component exclusions to the literal E.2.2 Hall witness.
The independent action input remains explicit; neither residual uniqueness
nor any of the remaining model exclusions is assumed. -/
theorem exterior_hall_counterexample_refined_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      ExteriorOddNormalizerRefinedCase s A := by
  obtain ⟨p, A, hp, hpgt, hne, hAe, hAM, hAV, hout, _⟩ :=
    exterior_hall_counterexample_source_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p, A, hp, hpgt, hne, hAe, hAM, hAV, hout,
    exterior_oddNormalizer_refined_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The remaining source cases after the complete placed characteristic-two
exclusion. Both J₄ arguments remain: the pushing-up case of printed p.612,
and the normal odd-local component case of printed p.623. -/
def ExteriorOddNormalizerTerminalCase (s : SylowExteriorMarking D) (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorOddNormalizerSourceCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    ExteriorOddNormalizerComponentCase s A K ∧
    ((∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* Representation.SL5TenDimensional.Group,
      Function.Surjective f) ∨
      (K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
        oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
        centralizer (K : Set (normalizer (A : Set G))) =
          pPrimeCore 2 (normalizer (A : Set G)) ∧
        10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model))))

/-- From the original exterior marking, inner residual action now forces the
actual J₄ central quotient. No characteristic-two exclusion is assumed. -/
theorem exterior_oddNormalizer_terminal_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerTerminalCase s A := by
  rcases exterior_oddNormalizer_refined_case s h p hp hpgt A hne hAe hAM hAV hout
    with hu | ⟨K,hK,hm,houtK,hcore,hmodel,hcases⟩
  · exact Or.inl hu
  refine Or.inr ⟨K,hK,hm,houtK,hcore,hmodel,hcases,?_⟩
  rcases hcases with ho | ⟨hn,hv,hf,hc,hr,hm⟩
  · exact Or.inl ho.1
  have hodd : Odd (Nat.card A) := by
    let : Fact p.Prime := ⟨hp⟩
    let := hAe
    obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact (hp.odd_of_ne_two (by omega)).pow
  have hl := exterior_oddNormalizer_placed_local s h A hAM hodd hAV K hf
  exact Or.inr ⟨hn,hv,hf,hc,hr,hl.jankoFour_of_placed_models hm⟩

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- Apply the full placed-model exclusion to the literal E.2.2 Hall witness.
The independent action premise is discharged by qt-d-1251-fusion-hall;
Structural1222At retains qt-d-1222-source and its qt-d-1251-source assembly. -/
theorem exterior_hall_counterexample_terminal_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      ExteriorOddNormalizerTerminalCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,_⟩ :=
    exterior_hall_counterexample_source_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,
    exterior_oddNormalizer_terminal_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The remaining source cases after the binary unitary and odd
three-space outer exclusions. The outer branch now retains only the seven
literal remaining B-model families. The pushing-up and normal J₄ arguments
at printed pp.612 and 623 are separate, still unproved branches. -/
def ExteriorOddNormalizerReducedCase (s : SylowExteriorMarking D) (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorOddNormalizerSourceCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    ExteriorOddNormalizerComponentCase s A K ∧
    ((∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* Representation.SL5TenDimensional.Group,
      Function.Surjective f) ∧
      ExteriorRemainingOuterModel (K ⧸ center K) ∨
      (K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
        oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
        centralizer (K : Set (normalizer (A : Set G))) =
          pPrimeCore 2 (normalizer (A : Set G)) ∧
        10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model))))

/-- Apply the proved outer and inner exclusions to the original marked
normalizer. Every component cover, actor and module is retained. -/
theorem exterior_oddNormalizer_reduced_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerReducedCase s A := by
  rcases exterior_oddNormalizer_refined_case s h p hp hpgt A hne hAe hAM hAV hout
    with hu | ⟨K,hK,hm,houtK,hcore,hmodel,hcases⟩
  · exact Or.inl hu
  refine Or.inr ⟨K,hK,hm,houtK,hcore,hmodel,hcases,?_⟩
  rcases hcases with ho | ⟨hn,hv,hf,hc,hr,hm⟩
  · let : IsQuasisimple K := hK.2
    exact Or.inl ⟨ho.1,exterior_remaining_outer_models hmodel ho.1⟩
  have hodd : Odd (Nat.card A) := by
    let : Fact p.Prime := ⟨hp⟩
    let := hAe
    obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact (hp.odd_of_ne_two (by omega)).pow
  have hl := exterior_oddNormalizer_placed_local s h A hAM hodd hAV K hf
  exact Or.inr ⟨hn,hv,hf,hc,hr,hl.jankoFour_of_placed_models hm⟩

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- Apply both the placed-model and new outer exclusions to the literal E.2.2 Hall witness.
The independent action premise is discharged by qt-d-1251-fusion-hall;
Structural1222At retains qt-d-1222-source and its qt-d-1251-source assembly. -/
theorem exterior_hall_counterexample_reduced_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      ExteriorOddNormalizerReducedCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,_⟩ :=
    exterior_hall_counterexample_source_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,
    exterior_oddNormalizer_reduced_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The remaining configurations after excluding the actual J₃ and Sp₆(2)
outer sections. Four odd classical families and McL remain in that branch.
The pushing-up and normal J₄ arguments at printed pp.612 and623 remain
separate, unproved source obligations. -/
def ExteriorOddNormalizerFiveOuterCase (s : SylowExteriorMarking D) (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorOddNormalizerSourceCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    ExteriorOddNormalizerComponentCase s A K ∧
    ((∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* Representation.SL5TenDimensional.Group,
      Function.Surjective f) ∧
      ExteriorFiveOuterModels (K ⧸ center K) ∨
      (K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
        oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
        centralizer (K : Set (normalizer (A : Set G))) =
          pPrimeCore 2 (normalizer (A : Set G)) ∧
        10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model))))

/-- Apply the proved outer and inner exclusions to the original marked
normalizer. Every component cover, actor and module is retained. -/
theorem exterior_oddNormalizer_five_outer_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerFiveOuterCase s A := by
  rcases exterior_oddNormalizer_refined_case s h p hp hpgt A hne hAe hAM hAV hout
    with hu | ⟨K,hK,hm,houtK,hcore,hmodel,hcases⟩
  · exact Or.inl hu
  refine Or.inr ⟨K,hK,hm,houtK,hcore,hmodel,hcases,?_⟩
  rcases hcases with ho | ⟨hn,hv,hf,hc,hr,hm⟩
  · let : IsQuasisimple K := hK.2
    exact Or.inl ⟨ho.1,exterior_five_outer_models hmodel ho.1⟩
  have hodd : Odd (Nat.card A) := by
    let : Fact p.Prime := ⟨hp⟩
    let := hAe
    obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact (hp.odd_of_ne_two (by omega)).pow
  have hl := exterior_oddNormalizer_placed_local s h A hAM hodd hAV K hf
  exact Or.inr ⟨hn,hv,hf,hc,hr,hl.jankoFour_of_placed_models hm⟩

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- Apply the sharpened Sylow exclusions to the literal E.2.2 Hall witness.
The independent action premise is discharged by qt-d-1251-fusion-hall;
Structural1222At retains qt-d-1222-source and its qt-d-1251-source assembly. -/
theorem exterior_hall_counterexample_five_outer_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      ExteriorOddNormalizerFiveOuterCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,_⟩ :=
    exterior_hall_counterexample_source_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,
    exterior_oddNormalizer_five_outer_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The remaining configurations after excluding the actual McL outer
section as well. Only the four odd classical outer families remain.
The pushing-up and normal J₄ arguments at printed pp.612 and623 remain
separate, unproved source obligations. -/
def ExteriorOddNormalizerFourOuterCase (s : SylowExteriorMarking D) (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorOddNormalizerSourceCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    ExteriorOddNormalizerComponentCase s A K ∧
    ((∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* Representation.SL5TenDimensional.Group,
      Function.Surjective f) ∧
      ExteriorFourOuterModels (K ⧸ center K) ∨
      (K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
        oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
        centralizer (K : Set (normalizer (A : Set G))) =
          pPrimeCore 2 (normalizer (A : Set G)) ∧
        10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model))))

/-- Apply the proved outer and inner exclusions to the original marked
normalizer. Every component cover, actor and module is retained. -/
theorem exterior_oddNormalizer_four_outer_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerFourOuterCase s A := by
  rcases exterior_oddNormalizer_refined_case s h p hp hpgt A hne hAe hAM hAV hout
    with hu | ⟨K,hK,hm,houtK,hcore,hmodel,hcases⟩
  · exact Or.inl hu
  refine Or.inr ⟨K,hK,hm,houtK,hcore,hmodel,hcases,?_⟩
  rcases hcases with ho | ⟨hn,hv,hf,hc,hr,hm⟩
  · let : IsQuasisimple K := hK.2
    exact Or.inl ⟨ho.1,exterior_four_outer_models hmodel ho.1⟩
  have hodd : Odd (Nat.card A) := by
    let : Fact p.Prime := ⟨hp⟩
    let := hAe
    obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact (hp.odd_of_ne_two (by omega)).pow
  have hl := exterior_oddNormalizer_placed_local s h A hAM hodd hAV K hf
  exact Or.inr ⟨hn,hv,hf,hc,hr,hl.jankoFour_of_placed_models hm⟩

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- Apply the sharpened Sylow exclusions to the literal E.2.2 Hall witness.
The independent action premise is discharged by qt-d-1251-fusion-hall;
Structural1222At retains qt-d-1222-source and its qt-d-1251-source assembly. -/
theorem exterior_hall_counterexample_four_outer_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      ExteriorOddNormalizerFourOuterCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,_⟩ :=
    exterior_hall_counterexample_source_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,
    exterior_oddNormalizer_four_outer_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The remaining configurations after excluding the actual odd-prime PSp₄ outer
section as well. Only G₂ and the two degree-four outer families remain.
The pushing-up and normal J₄ arguments at printed pp.612 and623 remain
separate, unproved source obligations. -/
def ExteriorOddNormalizerThreeOuterCase (s : SylowExteriorMarking D) (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorOddNormalizerSourceCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    ExteriorOddNormalizerComponentCase s A K ∧
    ((∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* Representation.SL5TenDimensional.Group,
      Function.Surjective f) ∧
      ExteriorThreeOuterModels (K ⧸ center K) ∨
      (K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
        oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
        centralizer (K : Set (normalizer (A : Set G))) =
          pPrimeCore 2 (normalizer (A : Set G)) ∧
        10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model))))

/-- Apply the proved outer and inner exclusions to the original marked
normalizer. Every component cover, actor and module is retained. -/
theorem exterior_oddNormalizer_three_outer_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerThreeOuterCase s A := by
  rcases exterior_oddNormalizer_refined_case s h p hp hpgt A hne hAe hAM hAV hout
    with hu | ⟨K,hK,hm,houtK,hcore,hmodel,hcases⟩
  · exact Or.inl hu
  refine Or.inr ⟨K,hK,hm,houtK,hcore,hmodel,hcases,?_⟩
  rcases hcases with ho | ⟨hn,hv,hf,hc,hr,hm⟩
  · let : IsQuasisimple K := hK.2
    exact Or.inl ⟨ho.1,exterior_three_outer_models hmodel ho.1⟩
  have hodd : Odd (Nat.card A) := by
    let : Fact p.Prime := ⟨hp⟩
    let := hAe
    obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact (hp.odd_of_ne_two (by omega)).pow
  have hl := exterior_oddNormalizer_placed_local s h A hAM hodd hAV K hf
  exact Or.inr ⟨hn,hv,hf,hc,hr,hl.jankoFour_of_placed_models hm⟩

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- Apply the sharpened Sylow exclusions to the literal E.2.2 Hall witness.
The independent action premise is discharged by qt-d-1251-fusion-hall;
Structural1222At retains qt-d-1222-source and its qt-d-1251-source assembly. -/
theorem exterior_hall_counterexample_three_outer_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      ExteriorOddNormalizerThreeOuterCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,_⟩ :=
    exterior_hall_counterexample_source_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,
    exterior_oddNormalizer_three_outer_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The remaining configurations after excluding the actual odd-prime G₂ outer
section as well. Only the two degree-four outer families remain.
The pushing-up and normal J₄ arguments at printed pp.612 and623 remain
separate, unproved source obligations. -/
def ExteriorOddNormalizerTwoOuterCase (s : SylowExteriorMarking D) (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorOddNormalizerSourceCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    ExteriorOddNormalizerComponentCase s A K ∧
    ((∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* Representation.SL5TenDimensional.Group,
      Function.Surjective f) ∧
      ExteriorTwoOuterModels (K ⧸ center K) ∨
      (K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
        oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
        centralizer (K : Set (normalizer (A : Set G))) =
          pPrimeCore 2 (normalizer (A : Set G)) ∧
        10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model))))

/-- Apply the proved outer and inner exclusions to the original marked
normalizer. Every component cover, actor and module is retained. -/
theorem exterior_oddNormalizer_two_outer_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerTwoOuterCase s A := by
  rcases exterior_oddNormalizer_refined_case s h p hp hpgt A hne hAe hAM hAV hout
    with hu | ⟨K,hK,hm,houtK,hcore,hmodel,hcases⟩
  · exact Or.inl hu
  refine Or.inr ⟨K,hK,hm,houtK,hcore,hmodel,hcases,?_⟩
  rcases hcases with ho | ⟨hn,hv,hf,hc,hr,hm⟩
  · let : IsQuasisimple K := hK.2
    exact Or.inl ⟨ho.1,exterior_two_outer_models hmodel ho.1⟩
  have hodd : Odd (Nat.card A) := by
    let : Fact p.Prime := ⟨hp⟩
    let := hAe
    obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact (hp.odd_of_ne_two (by omega)).pow
  have hl := exterior_oddNormalizer_placed_local s h A hAM hodd hAV K hf
  exact Or.inr ⟨hn,hv,hf,hc,hr,hl.jankoFour_of_placed_models hm⟩

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- Apply the sharpened Sylow exclusions to the literal E.2.2 Hall witness.
The independent action premise is discharged by qt-d-1251-fusion-hall;
Structural1222At retains qt-d-1222-source and its qt-d-1251-source assembly. -/
theorem exterior_hall_counterexample_two_outer_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      ExteriorOddNormalizerTwoOuterCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,_⟩ :=
    exterior_hall_counterexample_source_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,
    exterior_oddNormalizer_two_outer_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The remaining configurations after excluding the actual odd linear-four outer
section as well. Only the unitary degree-four outer family remains.
The pushing-up and normal J₄ arguments at printed pp.612 and623 remain
separate, unproved source obligations. -/
def ExteriorOddNormalizerUnitaryOuterCase (s : SylowExteriorMarking D) (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorOddNormalizerSourceCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    ExteriorOddNormalizerComponentCase s A K ∧
    ((∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* Representation.SL5TenDimensional.Group,
      Function.Surjective f) ∧
      ExteriorUnitaryOuterModel (K ⧸ center K) ∨
      (K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
        oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
        centralizer (K : Set (normalizer (A : Set G))) =
          pPrimeCore 2 (normalizer (A : Set G)) ∧
        10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model))))

/-- Apply the proved outer and inner exclusions to the original marked
normalizer. Every component cover, actor and module is retained. -/
theorem exterior_oddNormalizer_unitary_outer_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerUnitaryOuterCase s A := by
  rcases exterior_oddNormalizer_refined_case s h p hp hpgt A hne hAe hAM hAV hout
    with hu | ⟨K,hK,hm,houtK,hcore,hmodel,hcases⟩
  · exact Or.inl hu
  refine Or.inr ⟨K,hK,hm,houtK,hcore,hmodel,hcases,?_⟩
  rcases hcases with ho | ⟨hn,hv,hf,hc,hr,hm⟩
  · let : IsQuasisimple K := hK.2
    exact Or.inl ⟨ho.1,exterior_unitary_outer_model hmodel ho.1⟩
  have hodd : Odd (Nat.card A) := by
    let : Fact p.Prime := ⟨hp⟩
    let := hAe
    obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact (hp.odd_of_ne_two (by omega)).pow
  have hl := exterior_oddNormalizer_placed_local s h A hAM hodd hAV K hf
  exact Or.inr ⟨hn,hv,hf,hc,hr,hl.jankoFour_of_placed_models hm⟩

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- Apply the sharpened Sylow exclusions to the literal E.2.2 Hall witness.
The independent action premise is discharged by qt-d-1251-fusion-hall;
Structural1222At retains qt-d-1222-source and its qt-d-1251-source assembly. -/
theorem exterior_hall_counterexample_unitary_outer_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      ExteriorOddNormalizerUnitaryOuterCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,_⟩ :=
    exterior_hall_counterexample_source_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,
    exterior_oddNormalizer_unitary_outer_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- After all outer exclusions, only the actual pushing-up configuration or
an inner-action normal J₄ component remains. These require the two separate
source endgames at printed pp.612 and623; neither is assumed here. -/
def ExteriorOddNormalizerInnerCase (s : SylowExteriorMarking D) (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorOddNormalizerSourceCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model))

/-- Eliminate the entire outer-action branch in the original odd normalizer. -/
theorem exterior_oddNormalizer_inner_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerInnerCase s A := by
  rcases exterior_oddNormalizer_refined_case s h p hp hpgt A hne hAe hAM hAV hout
    with hu | ⟨K,hK,hm,houtK,hcore,hmodel,hcases⟩
  · exact Or.inl hu
  rcases hcases with ho | ⟨hn,hv,hf,hc,hr,hplaced⟩
  · let : IsQuasisimple K := hK.2
    exact (exterior_no_outer_section hmodel ho.1).elim
  have hodd : Odd (Nat.card A) := by
    let : Fact p.Prime := ⟨hp⟩
    let := hAe
    obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact (hp.odd_of_ne_two (by omega)).pow
  have hl := exterior_oddNormalizer_placed_local s h A hAM hodd hAV K hf
  exact Or.inr ⟨K,hK,hm,houtK,hcore,hmodel,hn,hv,hf,hc,hr,
    hl.jankoFour_of_placed_models hplaced⟩

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- The literal Hall counterexample now reaches only the two remaining source
branches. The independent action premise belongs to qt-d-1251-fusion-hall;
Structural1222At retains qt-d-1222-source and its qt-d-1251-source assembly. -/
theorem exterior_hall_counterexample_inner_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      ExteriorOddNormalizerInnerCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,_⟩ :=
    exterior_hall_counterexample_source_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,
    exterior_oddNormalizer_inner_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource


@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The p.623 branch with the full residual of the actual marked involution,
its original inclusion and its normal containing component in C_G(z).
The separate p.612 pushing-up branch is retained. -/
def ExteriorOddNormalizerResidualCase (s : SylowExteriorMarking D) (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorOddNormalizerSourceCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
    ExteriorJankoResidualData s A K)

/-- Construct the marked involution residual on the same full J₄ component
selected by the original odd-normalizer argument. -/
theorem exterior_oddNormalizer_residual_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerResidualCase s A := by
  rcases exterior_oddNormalizer_inner_case s h p hp hpgt A hne hAe hAM hAV hout
    with hu | ⟨K,hK,hm,houtK,hcore,hmodel,hn,hv,hf,hc,hr,⟨e⟩⟩
  · exact Or.inl hu
  have hodd : Odd (Nat.card A) := by
    let : Fact p.Prime := ⟨hp⟩
    let := hAe
    obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact (hp.odd_of_ne_two (by omega)).pow
  exact Or.inr ⟨K,hK,hm,houtK,hcore,hmodel,hn,hv,hf,hc,hr,⟨e⟩,
    exterior_janko_fixed_residual s h A hodd hAV K hK hn hv hc e⟩

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- The literal Hall counterexample constructs the marked M₂₂ residual,
controls the original odd actor's T-closure, and forces every T-normalized
comparison group centralized by that actor modulo its two-core into M.
The odd-local identification and generation steps on p.623 still need proof.
The independent action premise belongs to qt-d-1251-fusion-hall;
Structural1222At is discharged by qt-d-1251-source from qt-d-1222-source. -/
theorem exterior_hall_counterexample_residual_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ s.marking.M) ∧
      (∀ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) →
        A ≤ sectionCentralizer I → I ≤ s.marking.M) ∧
      ExteriorOddNormalizerResidualCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,_⟩ :=
    exterior_hall_counterexample_source_case s h structural action hH hHGi hlarge hP d hmax hnot
  have hodd : Odd (Nat.card A) := by
    let : Fact p.Prime := ⟨hp⟩
    let := hAe
    obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact (hp.odd_of_ne_two (by omega)).pow
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,
    exterior_oddActor_closure_control s h A hne hAM hodd hAV,
    D.sourceOrbit_oddActor_comparison h.toHypothesis1221 A hne
      ((s.marking.centralizing_actor_section hAM hAV).trans inf_le_right) hodd,
    exterior_oddNormalizer_residual_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The two distinct J₄ endgames: the ordinary pushing-up component on
p.612 and the odd-normalizer component with its marked M₂₂ residual on p.623.
No constrained C.2.8 component remains in the first branch. -/
def ExteriorOddNormalizerTwoJankoCase (s : SylowExteriorMarking D) (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorPushingUpJankoCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
    ExteriorJankoResidualData s A K)

/-- Every original exterior odd-normalizer counterexample reaches one of
the two full J₄ configurations, with the entire original module retained. -/
theorem exterior_oddNormalizer_two_janko_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerTwoJankoCase s A := by
  rcases exterior_oddNormalizer_residual_case s h p hp hpgt A hne hAe hAM hAV hout
    with ⟨hu,_⟩ | hj
  · have ho : Odd (Nat.card A) := by
      let : Fact p.Prime := ⟨hp⟩
      let := hAe
      obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
      rw [he]
      exact (hp.odd_of_ne_two (by omega)).pow
    exact Or.inl ⟨hu,exterior_pushingUp_janko s h A hAM ho hAV hu⟩
  · exact Or.inr hj

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- The literal Hall witness reaches the two separate full J₄ configurations.
The constrained pushing-up alternatives have been discharged. The original
odd-actor closure and comparison control are retained; the independent action
premise remains with qt-d-1251-fusion-hall and the earlier Structural1222At
premise with qt-d-1222-source, assembled by qt-d-1251-source. -/
theorem exterior_hall_counterexample_two_janko_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ s.marking.M) ∧
      (∀ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) →
        A ≤ sectionCentralizer I → I ≤ s.marking.M) ∧
      ExteriorOddNormalizerTwoJankoCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,_⟩ :=
    exterior_hall_counterexample_residual_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,
    exterior_oddNormalizer_two_janko_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The original p.612 cubic now lies in the actual intersection residual,
fixes sixteen exterior vectors, and has an M₂₂ covering subgroup in its full
centralizer residual. The p.623 branch keeps its separate marked involution. -/
def ExteriorOddNormalizerCubicCase (s : SylowExteriorMarking D) (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorPushingUpCubicCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
    ExteriorJankoResidualData s A K)

/-- Construct the source cubic on the original pushing-up witnesses of the
odd-normalizer counterexample, retaining the separate odd-local branch. -/
theorem exterior_oddNormalizer_cubic_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerCubicCase s A := by
  rcases exterior_oddNormalizer_two_janko_case s h p hp hpgt A hne hAe hAM hAV hout
    with ⟨hu,hj⟩ | hj
  · exact Or.inl ⟨hu,exterior_pushingUp_cubic_case s hj⟩
  · exact Or.inr hj

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- The literal Hall witness reaches the two separate full J₄ configurations.
The cubic construction uses the literal intersection residual and full cover. The original
odd-actor closure and comparison control are retained; the independent action
premise remains with qt-d-1251-fusion-hall and the earlier Structural1222At
premise with qt-d-1222-source, assembled by qt-d-1251-source. -/
theorem exterior_hall_counterexample_cubic_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ s.marking.M) ∧
      (∀ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) →
        A ≤ sectionCentralizer I → I ≤ s.marking.M) ∧
      ExteriorOddNormalizerCubicCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,_⟩ :=
    exterior_hall_counterexample_residual_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,
    exterior_oddNormalizer_cubic_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The two original J₄ configurations, now with the exact p.623 residual
excluded from every T-normalized comparison subgroup centralized by A
modulo its two-core. The full original covering component is retained. -/
def ExteriorOddNormalizerObstructionCase (s : SylowExteriorMarking D)
    (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorPushingUpCubicCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
    ExteriorJankoResidualData s A K ∧
    ∃ z : K, ((z : normalizer (A : Set G)) : G) = s.marking.z ∧ orderOf z = 2 ∧
      ¬ ∃ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) ∧
        A ≤ sectionCentralizer I ∧
        ((solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map
            ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ I)

/-- Apply the M₂₂ obstruction to the actual full component constructed by
the exterior odd-normalizer counterexample. No generation input is used. -/
theorem exterior_oddNormalizer_obstruction_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerObstructionCase s A := by
  rcases exterior_oddNormalizer_cubic_case s h p hp hpgt A hne hAe hAM hAV hout with hu |
    ⟨K,hK,hm,houtK,hcore,hmodel,hn,hv,hf,hc,hr,he,hdata⟩
  · exact Or.inl hu
  have ho : Odd (Nat.card A) := by
    let : Fact p.Prime := ⟨hp⟩
    let := hAe
    obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact (hp.odd_of_ne_two (by omega)).pow
  exact Or.inr ⟨K,hK,hm,houtK,hcore,hmodel,hn,hv,hf,hc,hr,he,hdata,
    exterior_janko_marked_residual_obstruction s h A hne hAM ho hAV K hdata⟩

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- The actual Hall counterexample reaches the strengthened two-branch frontier.
The p.623 branch now needs only its odd-local comparison construction; the
p.612 cubic-centralizer and commutator contradiction remains separate.
The action premise is owned by qt-d-1251-fusion-hall and Structural1222At
by qt-d-1222-source, with final earlier-source discharge in qt-d-1251-source. -/
theorem exterior_hall_counterexample_obstruction_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ s.marking.M) ∧
      (∀ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) →
        A ≤ sectionCentralizer I → I ≤ s.marking.M) ∧
      ExteriorOddNormalizerObstructionCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,_⟩ :=
    exterior_hall_counterexample_residual_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,
    exterior_oddNormalizer_obstruction_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The two original J₄ branches, retaining the marked p.623 residual
obstruction and the normal M₂₂ triple-cover component at the prescribed p.612
cubic. Its full exterior fixed space and original covering component remain. -/
def ExteriorOddNormalizerMarkedCubicCase (s : SylowExteriorMarking D)
    (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorPushingUpCubicComponentCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
    ExteriorJankoResidualData s A K ∧
    ∃ z : K, ((z : normalizer (A : Set G)) : G) = s.marking.z ∧ orderOf z = 2 ∧
      ¬ ∃ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) ∧
        A ≤ sectionCentralizer I ∧
        ((solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map
            ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ I)

/-- Construct the normal cubic-centralizer component at the same residual
cubic, using full-cover fusion and the actual M₂₂ quotient identification. -/
theorem exterior_oddNormalizer_marked_cubic_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerMarkedCubicCase s A := by
  rcases exterior_oddNormalizer_obstruction_case s h p hp hpgt A hne hAe hAM hAV hout
    with ⟨hu,hpush⟩ | hj
  · exact Or.inl ⟨hu,exterior_pushingUp_cubic_component_case s h hpush⟩
  · exact Or.inr hj

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- Apply the identified component to the literal Hall witness. Pushing-up
ambient normality and its commutator contradiction, and the separate p.623
odd-local comparison construction, remain to be proved. The independent action
premise stays with qt-d-1251-fusion-hall; Structural1222At is produced by
qt-d-1222-source, with final discharge in qt-d-1251-source. -/
theorem exterior_hall_counterexample_marked_cubic_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ s.marking.M) ∧
      (∀ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) →
        A ≤ sectionCentralizer I → I ≤ s.marking.M) ∧
      ExteriorOddNormalizerMarkedCubicCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,_⟩ :=
    exterior_hall_counterexample_residual_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,
    exterior_oddNormalizer_marked_cubic_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The two original J₄ branches, retaining the marked p.623 residual
obstruction and the full cubic-centralizer residual at the prescribed p.612
cubic. Its full exterior fixed space and original covering component remain. -/
def ExteriorOddNormalizerFullCubicCase (s : SylowExteriorMarking D)
    (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorPushingUpFullResidualCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
    ExteriorJankoResidualData s A K ∧
    ∃ z : K, ((z : normalizer (A : Set G)) : G) = s.marking.z ∧ orderOf z = 2 ∧
      ¬ ∃ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) ∧
        A ≤ sectionCentralizer I ∧
        ((solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map
            ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ I)

/-- Identify the whole cubic residual at the original exterior cubic,
retaining the separate marked involution obstruction. -/
theorem exterior_oddNormalizer_full_cubic_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerFullCubicCase s A := by
  rcases exterior_oddNormalizer_marked_cubic_case s h p hp hpgt A hne hAe hAM hAV hout
    with ⟨hu,hpush⟩ | hj
  · exact Or.inl ⟨hu,exterior_pushingUp_full_residual_case s h hpush⟩
  · exact Or.inr hj

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- Apply the full residual identification to the literal Hall witness. Pushing-up
ambient normality and its commutator contradiction, and the separate p.623
odd-local comparison construction, remain to be proved. The independent action
premise stays with qt-d-1251-fusion-hall; Structural1222At is produced by
qt-d-1222-source, with final discharge in qt-d-1251-source. -/
theorem exterior_hall_counterexample_full_cubic_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ s.marking.M) ∧
      (∀ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) →
        A ≤ sectionCentralizer I → I ≤ s.marking.M) ∧
      ExteriorOddNormalizerFullCubicCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,_⟩ :=
    exterior_hall_counterexample_residual_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,
    exterior_oddNormalizer_full_cubic_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The two original J₄ branches, retaining the marked p.623 residual
obstruction and the full quasisimple cubic-centralizer residual at the prescribed p.612
cubic, with its ordinary component image in C_H(x). Its full exterior fixed space and original covering component remain. -/
def ExteriorOddNormalizerOrdinaryCubicCase (s : SylowExteriorMarking D)
    (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorPushingUpOrdinaryResidualCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
    ExteriorJankoResidualData s A K ∧
    ∃ z : K, ((z : normalizer (A : Set G)) : G) = s.marking.z ∧ orderOf z = 2 ∧
      ¬ ∃ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) ∧
        A ≤ sectionCentralizer I ∧
        ((solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map
            ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ I)

/-- Prove quasisimplicity of the whole residual at the original exterior cubic,
retaining the separate marked involution obstruction. -/
theorem exterior_oddNormalizer_ordinary_cubic_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerOrdinaryCubicCase s A := by
  rcases exterior_oddNormalizer_full_cubic_case s h p hp hpgt A hne hAe hAM hAV hout
    with ⟨hu,hpush⟩ | hj
  · exact Or.inl ⟨hu,exterior_pushingUp_ordinary_residual_case s h hpush⟩
  · exact Or.inr hj

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- Apply full-residual quasisimplicity to the literal Hall witness. Pushing-up
ambient normality and its commutator contradiction, and the separate p.623
odd-local comparison construction, remain to be proved. The independent action
premise stays with qt-d-1251-fusion-hall; Structural1222At is produced by
qt-d-1222-source, with final discharge in qt-d-1251-source. -/
theorem exterior_hall_counterexample_ordinary_cubic_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ s.marking.M) ∧
      (∀ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) →
        A ≤ sectionCentralizer I → I ≤ s.marking.M) ∧
      ExteriorOddNormalizerOrdinaryCubicCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,_⟩ :=
    exterior_hall_counterexample_residual_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,
    exterior_oddNormalizer_ordinary_cubic_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The two original J₄ branches, retaining the p.623 obstruction and the
constructed p.612 involution. The original full J₄ component is normal in
C_G(r), and its original cubic residual is a normal ordinary component of
C_G(r) ∩ C_G(x). The original marking and all full covers are preserved. -/
def ExteriorOddNormalizerInvolutionCubicCase (s : SylowExteriorMarking D)
    (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorPushingUpInvolutionResidualCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
    ExteriorJankoResidualData s A K ∧
    ∃ z : K, ((z : normalizer (A : Set G)) : G) = s.marking.z ∧ orderOf z = 2 ∧
      ¬ ∃ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) ∧
        A ≤ sectionCentralizer I ∧
        ((solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map
            ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ I)

/-- Construct the involution-centralizer placement on the original exterior
pushing-up witnesses, retaining the separate odd-local branch. -/
theorem exterior_oddNormalizer_involution_cubic_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerInvolutionCubicCase s A := by
  rcases exterior_oddNormalizer_ordinary_cubic_case s h p hp hpgt A hne hAe hAM hAV hout
    with ⟨hu,hpush⟩ | hj
  · exact Or.inl ⟨hu,exterior_pushingUp_involution_residual_case s h hpush⟩
  · exact Or.inr hj

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- The literal Hall counterexample with the constructed p.612 involution
and simultaneous-centralizer component. Source I.3.2 promotion to C_G(x),
the commutator contradiction and the separate p.623 odd-local comparison
remain to be discharged. The independent action premise stays with
qt-d-1251-fusion-hall; Structural1222At is produced by qt-d-1222-source,
with final discharge in qt-d-1251-source. -/
theorem exterior_hall_counterexample_involution_cubic_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ s.marking.M) ∧
      (∀ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) →
        A ≤ sectionCentralizer I → I ≤ s.marking.M) ∧
      ExteriorOddNormalizerInvolutionCubicCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,_⟩ :=
    exterior_hall_counterexample_residual_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,
    exterior_oddNormalizer_involution_cubic_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The two original J₄ branches, retaining the p.623 obstruction and the
constructed p.612 involution. I.3.2 now yields one invariant two-component
in C_G(x) containing the full cubic residual. The original marking and all
full covers are preserved; proper containing components remain to be excluded. -/
def ExteriorOddNormalizerPumpupCubicCase (s : SylowExteriorMarking D)
    (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorPushingUpPumpupResidualCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
    ExteriorJankoResidualData s A K ∧
    ∃ z : K, ((z : normalizer (A : Set G)) : G) = s.marking.z ∧ orderOf z = 2 ∧
      ¬ ∃ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) ∧
        A ≤ sectionCentralizer I ∧
        ((solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map
            ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ I)

/-- Remove the exchanged-component branch on the original exterior
pushing-up witnesses, retaining the separate odd-local branch. -/
theorem exterior_oddNormalizer_pumpup_cubic_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerPumpupCubicCase s A := by
  rcases exterior_oddNormalizer_involution_cubic_case s h p hp hpgt A hne hAe hAM hAV hout
    with ⟨hu,hpush⟩ | hj
  · exact Or.inl ⟨hu,exterior_pushingUp_pumpup_residual_case s h hpush⟩
  · exact Or.inr hj

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- The literal Hall counterexample with I.3.2 reduced to a single containing
two-component. Equality with the cubic residual, the commutator contradiction
and the separate p.623 odd-local comparison remain to be discharged. The independent action premise stays with
qt-d-1251-fusion-hall; Structural1222At is produced by qt-d-1222-source,
with final discharge in qt-d-1251-source. -/
theorem exterior_hall_counterexample_pumpup_cubic_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ s.marking.M) ∧
      (∀ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) →
        A ≤ sectionCentralizer I → I ≤ s.marking.M) ∧
      ExteriorOddNormalizerPumpupCubicCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,_⟩ :=
    exterior_hall_counterexample_residual_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,
    exterior_oddNormalizer_pumpup_cubic_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The two original J₄ branches, retaining the p.623 obstruction and the
constructed p.612 involution. The original cubic residual lies in a normal
ordinary component of C_G(x); proper containment supplies a faithful
involution on its actual Theorem B central quotient. The original marking
and all full covers are preserved; proper containing components remain to be excluded. -/
def ExteriorOddNormalizerOrdinaryPumpupCubicCase (s : SylowExteriorMarking D)
    (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorPushingUpOrdinaryPumpupCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
    ExteriorJankoResidualData s A K ∧
    ∃ z : K, ((z : normalizer (A : Set G)) : G) = s.marking.z ∧ orderOf z = 2 ∧
      ¬ ∃ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) ∧
        A ≤ sectionCentralizer I ∧
        ((solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map
            ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ I)

/-- Construct the normal ordinary overcomponent and faithful quotient action
on the original exterior witnesses, retaining the separate odd-local branch. -/
theorem exterior_oddNormalizer_ordinary_pumpup_cubic_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerOrdinaryPumpupCubicCase s A := by
  rcases exterior_oddNormalizer_involution_cubic_case s h p hp hpgt A hne hAe hAM hAV hout
    with ⟨hu,hpush⟩ | hj
  · exact Or.inl ⟨hu,exterior_pushingUp_ordinary_pumpup_case s h hpush⟩
  · exact Or.inr hj

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- The literal Hall counterexample with its normal ordinary overcomponent.
Equality with the cubic residual, the p.612 commutator contradiction and
separate p.623 odd-local comparison remain to be discharged.
The independent action premise stays with
qt-d-1251-fusion-hall; Structural1222At is produced by qt-d-1222-source,
with final discharge in qt-d-1251-source. -/
theorem exterior_hall_counterexample_ordinary_pumpup_cubic_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ s.marking.M) ∧
      (∀ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) →
        A ≤ sectionCentralizer I → I ≤ s.marking.M) ∧
      ExteriorOddNormalizerOrdinaryPumpupCubicCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,_⟩ :=
    exterior_hall_counterexample_residual_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,
    exterior_oddNormalizer_ordinary_pumpup_cubic_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The two original J₄ branches, retaining the p.623 obstruction and the
constructed p.612 involution. The original cubic residual lies in a normal
ordinary component of C_G(x). Proper containment supplies a faithful
involution on its actual central quotient; the quotient lies in the reduced
list of Lie families, HS and McL. All original covers and markings remain. -/
def ExteriorOddNormalizerProperModelsCubicCase (s : SylowExteriorMarking D)
    (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorPushingUpProperModelsCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
    ExteriorJankoResidualData s A K ∧
    ∃ z : K, ((z : normalizer (A : Set G)) : G) = s.marking.z ∧ orderOf z = 2 ∧
      ¬ ∃ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) ∧
        A ≤ sectionCentralizer I ∧
        ((solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map
            ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ I)

/-- Apply the proved proper-component model exclusions to the original
exterior witnesses, retaining the separate odd-local branch. -/
theorem exterior_oddNormalizer_proper_models_cubic_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerProperModelsCubicCase s A := by
  rcases exterior_oddNormalizer_involution_cubic_case s h p hp hpgt A hne hAe hAM hAV hout
    with ⟨hu,hpush⟩ | hj
  · exact Or.inl ⟨hu,exterior_pushingUp_proper_models_case s h hpush⟩
  · exact Or.inr hj

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- The literal Hall counterexample after excluding Theorem B(1), B(4),
and eleven B(5) overcomponent rows. The remaining model exclusions,
the p.612 commutator contradiction and separate p.623 odd-local comparison
remain to be discharged.
The independent action premise stays with
qt-d-1251-fusion-hall; Structural1222At is produced by qt-d-1222-source,
with final discharge in qt-d-1251-source. -/
theorem exterior_hall_counterexample_proper_models_cubic_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ s.marking.M) ∧
      (∀ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) →
        A ≤ sectionCentralizer I → I ≤ s.marking.M) ∧
      ExteriorOddNormalizerProperModelsCubicCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,_⟩ :=
    exterior_hall_counterexample_residual_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,
    exterior_oddNormalizer_proper_models_cubic_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The two original J₄ branches, retaining the p.623 obstruction and the
constructed p.612 involution. The original cubic residual lies in a normal
ordinary component of C_G(x). Proper containment supplies a faithful
involution on its actual central quotient; the quotient lies in the reduced
list of four odd Lie families, binary PSU₃, rank-two families and McL. All original covers and markings remain. -/
def ExteriorOddNormalizerReducedProperModelsCubicCase (s : SylowExteriorMarking D)
    (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorPushingUpReducedProperModelsCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
    ExteriorJankoResidualData s A K ∧
    ∃ z : K, ((z : normalizer (A : Set G)) : G) = s.marking.z ∧ orderOf z = 2 ∧
      ¬ ∃ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) ∧
        A ≤ sectionCentralizer I ∧
        ((solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map
            ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ I)

/-- Apply the proved proper-component model exclusions to the original
exterior witnesses, retaining the separate odd-local branch. -/
theorem exterior_oddNormalizer_reduced_proper_models_cubic_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerReducedProperModelsCubicCase s A := by
  rcases exterior_oddNormalizer_involution_cubic_case s h p hp hpgt A hne hAe hAM hAV hout
    with ⟨hu,hpush⟩ | hj
  · exact Or.inl ⟨hu,exterior_pushingUp_reduced_proper_models_case s h hpush⟩
  · exact Or.inr hj

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- The literal Hall counterexample after additionally excluding HS, odd
PSL₂/PSL₃/PSU₃, binary PSL₂ and Suzuki proper overcomponents. The remaining model exclusions,
the p.612 commutator contradiction and separate p.623 odd-local comparison
remain to be discharged.
The independent action premise stays with
qt-d-1251-fusion-hall; Structural1222At is produced by qt-d-1222-source,
with final discharge in qt-d-1251-source. -/
theorem exterior_hall_counterexample_reduced_proper_models_cubic_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ s.marking.M) ∧
      (∀ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) →
        A ≤ sectionCentralizer I → I ≤ s.marking.M) ∧
      ExteriorOddNormalizerReducedProperModelsCubicCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,_⟩ :=
    exterior_hall_counterexample_residual_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,
    exterior_oddNormalizer_reduced_proper_models_cubic_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The two original J₄ branches, retaining the p.623 obstruction and the
constructed p.612 involution. The original cubic residual lies in a normal
ordinary component of C_G(x). Proper containment supplies a faithful
involution on its actual central quotient; the quotient lies in the reduced
list of three odd Lie families, six binary rank-two families and McL. All original covers and markings remain. -/
def ExteriorOddNormalizerRemainingProperModelsCubicCase (s : SylowExteriorMarking D)
    (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorPushingUpRemainingProperModelsCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
    ExteriorJankoResidualData s A K ∧
    ∃ z : K, ((z : normalizer (A : Set G)) : G) = s.marking.z ∧ orderOf z = 2 ∧
      ¬ ∃ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) ∧
        A ≤ sectionCentralizer I ∧
        ((solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map
            ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ I)

/-- Apply the proved proper-component model exclusions to the original
exterior witnesses, retaining the separate odd-local branch. -/
theorem exterior_oddNormalizer_remaining_proper_models_cubic_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerRemainingProperModelsCubicCase s A := by
  rcases exterior_oddNormalizer_involution_cubic_case s h p hp hpgt A hne hAe hAM hAV hout
    with ⟨hu,hpush⟩ | hj
  · exact Or.inl ⟨hu,exterior_pushingUp_remaining_proper_models_case s h hpush⟩
  · exact Or.inr hj

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- The literal Hall counterexample after additionally excluding Fermat PSL₄,
binary PSU₃ and PSL₃, and the small symplectic, G₂ and Tits proper overcomponents. The remaining model exclusions,
the p.612 commutator contradiction and separate p.623 odd-local comparison
remain to be discharged.
The independent action premise stays with
qt-d-1251-fusion-hall; Structural1222At is produced by qt-d-1222-source,
with final discharge in qt-d-1251-source. -/
theorem exterior_hall_counterexample_remaining_proper_models_cubic_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ s.marking.M) ∧
      (∀ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) →
        A ≤ sectionCentralizer I → I ≤ s.marking.M) ∧
      ExteriorOddNormalizerRemainingProperModelsCubicCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,_⟩ :=
    exterior_hall_counterexample_residual_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,
    exterior_oddNormalizer_remaining_proper_models_cubic_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The two original J₄ branches, retaining the p.623 obstruction and the
constructed p.612 involution. The original cubic residual lies in a normal
ordinary component of C_G(x). Proper containment supplies a faithful
involution on its actual central quotient; the quotient lies in the reduced
list of three odd Lie families, binary PSU₄ and McL. All original covers and markings remain. -/
def ExteriorOddNormalizerRankTwoProperModelsCubicCase (s : SylowExteriorMarking D)
    (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorPushingUpRankTwoProperModelsCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
    ExteriorJankoResidualData s A K ∧
    ∃ z : K, ((z : normalizer (A : Set G)) : G) = s.marking.z ∧ orderOf z = 2 ∧
      ¬ ∃ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) ∧
        A ≤ sectionCentralizer I ∧
        ((solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map
            ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ I)

/-- Apply the proved proper-component model exclusions to the original
exterior witnesses, retaining the separate odd-local branch. -/
theorem exterior_oddNormalizer_rank_two_proper_models_cubic_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerRankTwoProperModelsCubicCase s A := by
  rcases exterior_oddNormalizer_involution_cubic_case s h p hp hpgt A hne hAe hAM hAV hout
    with ⟨hu,hpush⟩ | hj
  · exact Or.inl ⟨hu,exterior_pushingUp_rank_two_proper_models_case s h hpush⟩
  · exact Or.inr hj

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- The literal Hall counterexample after excluding binary symplectic, G₂,
triality and Ree F₄ proper overcomponents, together with PSU₅(4). The
remaining three odd Lie families, binary PSU₄ and McL exclusions,
the p.612 commutator contradiction and separate p.623 odd-local comparison
remain to be discharged.
The independent action premise stays with
qt-d-1251-fusion-hall; Structural1222At is produced by qt-d-1222-source,
with final discharge in qt-d-1251-source. -/
theorem exterior_hall_counterexample_rank_two_proper_models_cubic_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ s.marking.M) ∧
      (∀ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) →
        A ≤ sectionCentralizer I → I ≤ s.marking.M) ∧
      ExteriorOddNormalizerRankTwoProperModelsCubicCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,_⟩ :=
    exterior_hall_counterexample_residual_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,
    exterior_oddNormalizer_rank_two_proper_models_cubic_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The original cubic residual equals its normal ordinary overcomponent.
Both original J₄ branches retain the entire cover, literal quotient maps
and exterior marking. The separate p.623 odd-local branch is unchanged. -/
def ExteriorOddNormalizerComponentEqualityCubicCase (s : SylowExteriorMarking D)
    (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorPushingUpComponentEqualityCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
    ExteriorJankoResidualData s A K ∧
    ∃ z : K, ((z : normalizer (A : Set G)) : G) = s.marking.z ∧ orderOf z = 2 ∧
      ¬ ∃ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) ∧
        A ≤ sectionCentralizer I ∧
        ((solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map
            ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ I)

/-- Apply the full residual equality to the original exterior witnesses. -/
theorem exterior_oddNormalizer_component_equality_cubic_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerComponentEqualityCubicCase s A := by
  rcases exterior_oddNormalizer_involution_cubic_case s h p hp hpgt A hne hAe hAM hAV hout
    with ⟨hu,hpush⟩ | hj
  · exact Or.inl ⟨hu,exterior_pushingUp_component_equality_case s h hpush⟩
  · exact Or.inr hj

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- The literal Hall counterexample with the original cubic residual now
equal to its normal ordinary containing component. The p.612 commutator
contradiction and separate p.623 odd-local comparison remain to be proved.
The independent action premise remains with qt-d-1251-fusion-hall;
Structural1222At is produced by qt-d-1222-source, with final discharge in
qt-d-1251-source. -/
theorem exterior_hall_counterexample_component_equality_cubic_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ s.marking.M) ∧
      (∀ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) →
        A ≤ sectionCentralizer I → I ≤ s.marking.M) ∧
      ExteriorOddNormalizerComponentEqualityCubicCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,_⟩ :=
    exterior_hall_counterexample_residual_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,
    exterior_oddNormalizer_component_equality_cubic_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The original cubic has a fixed exterior vector moved by its full residual.
The p.612 branch retains the resulting obstruction to every binary central
commutator image. The separate p.623 odd-local branch retains its full cover,
quotient maps and original marked involution. -/
def ExteriorOddNormalizerCommutatorCubicCase (s : SylowExteriorMarking D)
    (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorPushingUpCommutatorCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
    ExteriorJankoResidualData s A K ∧
    ∃ z : K, ((z : normalizer (A : Set G)) : G) = s.marking.z ∧ orderOf z = 2 ∧
      ¬ ∃ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) ∧
        A ≤ sectionCentralizer I ∧
        ((solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map
            ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ I)

/-- Retain both original J₄ branches and add the actual moved fixed vector
and proved commutator obstruction to the pushing-up branch. -/
theorem exterior_oddNormalizer_commutator_cubic_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerCommutatorCubicCase s A := by
  rcases exterior_oddNormalizer_component_equality_cubic_case s h p hp hpgt A hne hAe hAM hAV hout
    with ⟨hu,hpush⟩ | hj
  · exact Or.inl ⟨hu,exterior_pushingUp_commutator_case s h hpush⟩
  · exact Or.inr hj

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- Apply the moved-vector and commutator obstruction to the literal Hall
counterexample. The source normalizer R₁ and a nonzero commutator remain to
be constructed; the separate p.623 odd-local comparison also remains.
Structural1222At is produced by qt-d-1222-source and discharged by
qt-d-1251-source. The independent action premise stays with
qt-d-1251-fusion-hall. -/
theorem exterior_hall_counterexample_commutator_cubic_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ s.marking.M) ∧
      (∀ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) →
        A ≤ sectionCentralizer I → I ≤ s.marking.M) ∧
      ExteriorOddNormalizerCommutatorCubicCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,_⟩ :=
    exterior_hall_counterexample_residual_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,
    exterior_oddNormalizer_commutator_cubic_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The p.612 branch now includes the literal enlarged normalizer R₁ and
its nonzero commutator at the selected involution, together with every
previous cubic, cover and module marking. The separate p.623 branch remains. -/
def ExteriorOddNormalizerEnlargedCase (s : SylowExteriorMarking D)
    (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorPushingUpNormalizerCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
    ExteriorJankoResidualData s A K ∧
    ∃ z : K, ((z : normalizer (A : Set G)) : G) = s.marking.z ∧ orderOf z = 2 ∧
      ¬ ∃ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) ∧
        A ≤ sectionCentralizer I ∧
        ((solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map
            ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ I)

/-- Retain both source branches and construct the actual enlarged binary
normalizer in the pushing-up branch. Its module-control and quotient-fixed
involution conditions are still required before applying commutator vanishing. -/
theorem exterior_oddNormalizer_enlarged_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerEnlargedCase s A := by
  rcases exterior_oddNormalizer_commutator_cubic_case s h p hp hpgt A hne hAe hAM hAV hout
    with ⟨hu,hpush⟩ | hj
  · exact Or.inl ⟨hu,exterior_pushingUp_normalizer_case s h hpush⟩
  · exact Or.inr hj

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- The literal Hall counterexample now produces the actual source R₁
and a nonzero commutator, retaining the full original exterior module and
cubic residual. The module-control and quotient-fixed involution step of
p.612 and the distinct p.623 odd-local comparison remain.
Structural1222At is produced by qt-d-1222-source and discharged by
qt-d-1251-source. The independent action premise stays with
qt-d-1251-fusion-hall. -/
theorem exterior_hall_counterexample_enlarged_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ s.marking.M) ∧
      (∀ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) →
        A ≤ sectionCentralizer I → I ≤ s.marking.M) ∧
      ExteriorOddNormalizerEnlargedCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,_⟩ :=
    exterior_hall_counterexample_residual_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,
    exterior_oddNormalizer_enlarged_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- Both original J₄ branches, with R₁ centralizing the original exterior
module and the full radical splitting retained in the p.612 branch. -/
def ExteriorOddNormalizerModuleControlCase (s : SylowExteriorMarking D)
    (A : Subgroup G) : Prop :=
  (¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M ∧
    ExteriorPushingUpModuleControlCase s A) ∨
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
    ExteriorJankoResidualData s A K ∧
    ∃ z : K, ((z : normalizer (A : Set G)) : G) = s.marking.z ∧ orderOf z = 2 ∧
      ¬ ∃ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) ∧
        A ≤ sectionCentralizer I ∧
        ((solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map
            ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ I)

/-- Apply the full-cover rank comparison to the actual enlarged normalizer.
The fixed-modulo-V involution choice and the separate odd-local branch remain. -/
theorem exterior_oddNormalizer_module_control_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerModuleControlCase s A := by
  rcases exterior_oddNormalizer_enlarged_case s h p hp hpgt A hne hAe hAM hAV hout
    with ⟨hu,hpush⟩ | hj
  · exact Or.inl ⟨hu,exterior_pushingUp_module_control_case s h hpush⟩
  · exact Or.inr hj

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- The literal Hall counterexample has R₁ centralizing the original V,
a full-cover radical splitting, and a commutator outside V at the current
involution. Source p.612 must still identify the component intersection and
choose an involution fixed modulo V; p.623's odd-local comparison remains.
Structural1222At is produced by qt-d-1222-source and discharged by
qt-d-1251-source. The independent action premise stays with
qt-d-1251-fusion-hall. -/
theorem exterior_hall_counterexample_module_control_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ s.marking.M) ∧
      (∀ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) →
        A ≤ sectionCentralizer I → I ≤ s.marking.M) ∧
      ExteriorOddNormalizerModuleControlCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,_⟩ :=
    exterior_hall_counterexample_residual_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,
    exterior_oddNormalizer_module_control_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The remaining p.623 odd-local configuration, with the original full cover,
marked involution residual and ambient containing component. The p.612
pushing-up alternative has been excluded. -/
def ExteriorOddNormalizerOddLocalCase (s : SylowExteriorMarking D)
    (A : Subgroup G) : Prop :=
  (∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧
    ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M ∧
    pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
    K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    10 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
    ExteriorJankoResidualData s A K ∧
    ∃ z : K, ((z : normalizer (A : Set G)) : G) = s.marking.z ∧ orderOf z = 2 ∧
      ¬ ∃ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) ∧
        A ≤ sectionCentralizer I ∧
        ((solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map
            ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ I)

/-- The complete p.612 contradiction leaves only the distinct p.623 branch
of an exterior odd-normalizer counterexample. -/
theorem exterior_oddNormalizer_odd_local_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerOddLocalCase s A := by
  rcases exterior_oddNormalizer_module_control_case s h p hp hpgt A hne hAe hAM hAV hout
    with ⟨_,hpush⟩ | hj
  · exact (exterior_pushingUp_module_control_false s h hpush).elim
  · exact hj

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- The literal Hall counterexample now has only the original odd-local J₄
configuration on p.623. The full residual, odd actor closure and quotient
maps are retained. Structural1222At is produced by qt-d-1222-source and
finally discharged by qt-d-1251-source; the action premise remains with
qt-d-1251-fusion-hall. -/
theorem exterior_hall_counterexample_odd_local_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ s.marking.M) ∧
      (∀ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) →
        A ≤ sectionCentralizer I → I ≤ s.marking.M) ∧
      ExteriorOddNormalizerOddLocalCase s A := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,_⟩ :=
    exterior_hall_counterexample_residual_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,
    exterior_oddNormalizer_odd_local_case s h p hp hpgt A hne hAe hAM hAV hout⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04 OddLocalMathieu
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The remaining p.623 counterexample has the literal odd-prime action and
full residual embedding, together with the reduced simple-section catalogue.
The binary exceptional families and J₄ still require exclusion. -/
theorem exterior_oddNormalizer_odd_action_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerOddLocalCase s A ∧
      ∃ K : Subgroup (normalizer (A : Set G)),
        IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
        ExteriorJankoResidualData s A K ∧ ExteriorOddLocalActionData s p A K ∧
        ∃ Q : Subgroup (centralizer ({s.marking.z} : Set G)),
          Q.IsCComponent ∧ Q.Normal ∧ IsQuasisimple (Q ⧸ pCore 2 Q) ∧
          (T : Subgroup G) ≤ normalizer (Q.map (centralizer ({s.marking.z} : Set G)).subtype : Set G) ∧
          ChapterA.Section02.IsTheoremCModel (SimpleSection Q) ∧
          HasMathieuFixedSection (SimpleSection Q) p ∧ RemainingOddLocalModel (SimpleSection Q) := by
  have hj := exterior_oddNormalizer_odd_local_case s h p hp hpgt A hne hAe hAM hAV hout
  refine ⟨hj,?_⟩
  obtain ⟨K,hK,hm,houtK,hcore,hmodel,hn,hV,hF,hcent,hrank,he,r,hobs⟩ := hj
  have d := exterior_janko_odd_local_action s h p hp hpgt A hne hAe hAM hAV K r
  exact ⟨K,hK,hn,he,r,d,exterior_odd_local_remaining_models s hp hpgt d⟩

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- Apply the p.623 odd-prime action and model sieve to the original Hall
counterexample. The full J₄ cover and marked residual are retained. The
independent action premise remains with qt-d-1251-fusion-hall;
Structural1222At is produced by qt-d-1222-source and discharged by qt-d-1251-source. -/
theorem exterior_hall_counterexample_odd_action_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ s.marking.M) ∧
      (∀ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) →
        A ≤ sectionCentralizer I → I ≤ s.marking.M) ∧
      ExteriorOddNormalizerOddLocalCase s A ∧
      ∃ K : Subgroup (normalizer (A : Set G)),
        IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
        ExteriorJankoResidualData s A K ∧ ExteriorOddLocalActionData s p A K ∧
        ∃ Q : Subgroup (centralizer ({s.marking.z} : Set G)),
          Q.IsCComponent ∧ Q.Normal ∧ IsQuasisimple (Q ⧸ pCore 2 Q) ∧
          (T : Subgroup G) ≤ normalizer (Q.map (centralizer ({s.marking.z} : Set G)).subtype : Set G) ∧
          ChapterA.Section02.IsTheoremCModel (SimpleSection Q) ∧
          HasMathieuFixedSection (SimpleSection Q) p ∧ RemainingOddLocalModel (SimpleSection Q) := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,_⟩ :=
    exterior_hall_counterexample_odd_local_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,
    exterior_oddNormalizer_odd_action_case s h p hp hpgt A hne hAe hAM hAV hout⟩
end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04 OddLocalMathieu
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The p.623 counterexample has only the three binary model rows. The full
seed has a quasisimple two-core quotient and its image is a quasisimple
Mathieu cover normalizing no nontrivial two-subgroup. The original full J₄
cover K is retained; J₄ has been excluded as the distinct containing section. -/
theorem exterior_oddNormalizer_odd_seed_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerOddLocalCase s A ∧
      ∃ K : Subgroup (normalizer (A : Set G)),
        IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
        ExteriorJankoResidualData s A K ∧ ExteriorOddLocalSeedCase s p A K := by
  have hj := exterior_oddNormalizer_odd_local_case s h p hp hpgt A hne hAe hAM hAV hout
  refine ⟨hj,?_⟩
  obtain ⟨K,hK,hm,houtK,hcore,hmodel,hn,hV,hF,hcent,hrank,he,r,hobs⟩ := hj
  have d := exterior_janko_odd_local_action s h p hp hpgt A hne hAe hAM hAV K r
  exact ⟨K,hK,hn,he,r,exterior_odd_local_seed_case s h hp hpgt d⟩

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- Apply the J₄ exclusion and seed-core theorem to the original Hall
counterexample. The original full cover, involution and residual are retained. The
independent action premise remains with qt-d-1251-fusion-hall;
Structural1222At is produced by qt-d-1222-source and discharged by qt-d-1251-source. -/
theorem exterior_hall_counterexample_odd_seed_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ s.marking.M) ∧
      (∀ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) →
        A ≤ sectionCentralizer I → I ≤ s.marking.M) ∧
      ExteriorOddNormalizerOddLocalCase s A ∧
      ∃ K : Subgroup (normalizer (A : Set G)),
        IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
        ExteriorJankoResidualData s A K ∧ ExteriorOddLocalSeedCase s p A K := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,_⟩ :=
    exterior_hall_counterexample_odd_local_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,
    exterior_oddNormalizer_odd_seed_case s h p hp hpgt A hne hAe hAM hAV hout⟩
end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04 OddLocalMathieu
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The original odd-normalizer counterexample has an ordinary Mathieu
component in the common fixed group of the whole odd actor, on the literal
simple-section map of the same containing C-component. -/
theorem exterior_oddNormalizer_odd_component_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerOddLocalCase s A ∧
      ∃ K : Subgroup (normalizer (A : Set G)),
        IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
        ExteriorJankoResidualData s A K ∧ ExteriorOddLocalComponentCase s p A K := by
  obtain ⟨hj,K,hK,hn,he,r,d⟩ := exterior_oddNormalizer_odd_seed_case
    s h p hp hpgt A hne hAe hAM hAV hout
  exact ⟨hj,K,hK,hn,he,r,exterior_odd_local_component_case s hp hpgt hAe hAV d⟩

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- Apply the common-fixed-component construction to the original Hall
counterexample, preserving the whole actor, full cover, involution and residual. The
independent action premise remains with qt-d-1251-fusion-hall;
Structural1222At is produced by qt-d-1222-source and discharged by qt-d-1251-source. -/
theorem exterior_hall_counterexample_odd_component_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ s.marking.M) ∧
      (∀ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) →
        A ≤ sectionCentralizer I → I ≤ s.marking.M) ∧
      ExteriorOddNormalizerOddLocalCase s A ∧
      ∃ K : Subgroup (normalizer (A : Set G)),
        IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
        ExteriorJankoResidualData s A K ∧ ExteriorOddLocalComponentCase s p A K := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,_⟩ :=
    exterior_hall_counterexample_odd_local_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,
    exterior_oddNormalizer_odd_component_case s h p hp hpgt A hne hAe hAM hAV hout⟩
end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04 OddLocalMathieu
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The original odd-normalizer counterexample has only the general Ree F₄
comparison row. The original full Mathieu cover, both quotient kernels and
componenthood in the whole odd actor's common fixed group are retained. -/
theorem exterior_oddNormalizer_ree_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (p : ℕ) (hp : p.Prime) (hpgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hAM : A ≤ s.marking.M) (hAV : A ≤ centralizer (V : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M) :
    ExteriorOddNormalizerOddLocalCase s A ∧
      ∃ K : Subgroup (normalizer (A : Set G)),
        IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
        ExteriorJankoResidualData s A K ∧ ExteriorOddLocalReeCase s p A K := by
  obtain ⟨hj,K,hK,hn,he,r,d⟩ := exterior_oddNormalizer_odd_component_case
    s h p hp hpgt A hne hAe hAM hAV hout
  exact ⟨hj,K,hK,hn,he,r,exterior_odd_local_ree_case s d⟩

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- Apply the G₂ and triality exclusions to the original Hall counterexample.
Only the general Ree F₄ row remains, with the original whole actor, full
cover, involution, residual and literal quotient maps preserved. The
independent action premise remains with qt-d-1251-fusion-hall;
Structural1222At is produced by qt-d-1222-source and discharged by qt-d-1251-source. -/
theorem exterior_hall_counterexample_ree_case
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H)
    (hnot : ¬ IsPGroup 3 d.witness.abelianGroup) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧
      A ≠ ⊥ ∧ IsElementaryAbelian p A ∧ A ≤ s.marking.M ∧
      A ≤ centralizer (V : Set G) ∧ ¬ normalizer (A : Set G) ≤ s.marking.M ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ s.marking.M) ∧
      (∀ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) →
        A ≤ sectionCentralizer I → I ≤ s.marking.M) ∧
      ExteriorOddNormalizerOddLocalCase s A ∧
      ∃ K : Subgroup (normalizer (A : Set G)),
        IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
        ExteriorJankoResidualData s A K ∧ ExteriorOddLocalReeCase s p A K := by
  obtain ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,_⟩ :=
    exterior_hall_counterexample_odd_local_case s h structural action hH hHGi hlarge hP d hmax hnot
  exact ⟨p,A,hp,hpgt,hne,hAe,hAM,hAV,hout,hclosure,hcomparison,
    exterior_oddNormalizer_ree_case s h p hp hpgt A hne hAe hAM hAV hout⟩
end CFSG.Quasithin.Chapter12.Section05.NaturalSource

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The specialized Chapter 4 odd-normalizer control for the original faithful
PSL₅(2) exterior marking. The section-centralizer condition, pushing-up
contradiction and every exceptional component row are proved from the
original hypotheses; the action-centralization premise remains independent. -/
theorem exterior_oddNormalizer_control (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    ExteriorOddNormalizerControl s := by
  intro p hp hpgt A hne hAe hAM hAV
  by_contra hout
  obtain ⟨_,K,_,_,_,_,d⟩ := exterior_oddNormalizer_ree_case
    s h p hp hpgt A hne hAe hAM hAV hout
  exact not_exterior_odd_local_ree_case s d

open ChapterE.Section06.FixedPointBounds.ParabolicCartan ChapterB

/-- Apply the proved odd-normalizer control to the literal E.2.2 Hall
subgroup. Only the independent action input and the original earlier
structural theorem remain: their final assembly belongs to
qt-d-1251-fusion-hall and qt-d-1251-source, respectively. -/
theorem exterior_hall_three_of_odd_action
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (action : ExteriorOddActionCentralizes s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHGi : H ≤ s.marking.Gi 1) (hlarge : 1 < ChapterE.generationParameter H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {f : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f)
    (hmax : minimalParabolicMax (T.subtype hH.1.1.2) hP = s.marking.M.subgroupOf H) :
    IsPGroup 3 d.witness.abelianGroup :=
  exterior_hall_three_of_controls s h structural action
    (exterior_oddNormalizer_control s h) hH hHGi hlarge hP d hmax
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
