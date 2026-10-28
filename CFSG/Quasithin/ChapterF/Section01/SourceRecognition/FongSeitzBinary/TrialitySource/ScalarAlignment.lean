module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.GeometricApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.Relabeling
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.NaturalCoordinates
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.ScalarComparison

/-!
# Scalar alignment in a section of the literal source U

The two leading commutator calculations on Fong--Seitz II p.219 live in
one section of the same U. Here M is normal in U, and every section map
is explicitly the canonical quotient map after the original root map's
codomain restriction. No normality in the whole unknown group is asserted.

Recover the natural action's field embedding from its SL₂ homomorphism
and root/Weyl axes, restrict it to the already marked fixed subfield, and
compare it with the unnormalized cubic tensor expression. This forces
x=1, y=theta and the scalar-twist identities. Relabeling the entire long
rank-one map by the inverse twist then makes the whole natural actor the
standard inclusion and makes the leading mixed coefficient a*b. Both
signs and the torus use that same relabeling by the Relabeling theorems.

The final consumers apply the relabeled pinning to the existing positive
reconstruction and preserve the original/geometric S images and Q.q.
The pinning and placements can be supplied by GeometricApplication; both
orientations and the small fields remain allowed. These results do not
construct M, the two-dimensional action, or the eight-dimensional tensor
action from 6E(b). In particular the displayed unnormalized tensor action,
the remaining EarlierModuleEquations and mixed torus relations still need
source proofs before the full triality source family is complete.

Source: Fong--Seitz II (9.24)--(9.29), printed pp.218--219; the entire-actor
relabeling immediately before (9.27), and the relative radical sections
there. The original normal-generation and full marked comparison owners
retain the same actual quotient and endpoint conventions.
-/


@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.PSL2.SemilinearCoverage
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
open Triality.Standard Triality.Standard.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.ScalarAlignment
variable {X F : Type*} [Group X] [Field F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  {σ : F ≃+* F}
local notation "K" => ScalarMarking.SourceFixed (σ := σ)

/-- A root in a literal section of the original U. Normality is only in U. -/
def sectionRoot {E : Type*} [AddGroup E] (r : Multiplicative E →* (X ⧸ Q.D))
    (hr : r.range ≤ split.U) (M : Subgroup split.U) [M.Normal] :
    Multiplicative E →* (split.U ⧸ M) :=
  (QuotientGroup.mk' M).comp (r.codRestrict split.U (fun a => hr ⟨a,rfl⟩))

variable (p : RankOnePair σ (X ⧸ Q.D)) (w : WeylPlacement Q p)
  (hs : (p.shortOrbit 0).range = simpleRoot Q split (w.indices 0))
  (hl : (p.longOrbit 0).range = simpleRoot Q split (w.indices 1))
  (hm : rotationOrder Q = 6)

include hs in
private theorem short_le : (p.shortOrbit 0).range ≤ split.U :=
  hs.le.trans (simpleRoot_le Q split (w.indices 0))
include hl in
private theorem long_le : (p.longOrbit 0).range ≤ split.U :=
  hl.le.trans (simpleRoot_le Q split (w.indices 1))
include w hs hl hm in
private theorem next_le : (p.shortOrbit 1).range ≤ split.U :=
  RootGeometry.ranges_le_unipotent Q split p w hs hl hm 2

variable (M : Subgroup split.U) [M.Normal]

def sectionA : Multiplicative F →* (split.U ⧸ M) :=
  sectionRoot Q split (p.shortOrbit 0) (by exact short_le Q split p w hs) M
def sectionB : Multiplicative K →* (split.U ⧸ M) :=
  sectionRoot Q split (p.longOrbit 0) (by exact long_le Q split p w hl) M
def sectionC : Multiplicative F →* (split.U ⧸ M) :=
  sectionRoot Q split (p.shortOrbit 1) (by exact next_le Q split p w hs hl hm) M

local notation "A" => sectionA Q split p w hs M
local notation "B" => sectionB Q split p w hl M
local notation "C" => sectionC Q split p w hs hl hm M

/-- Relabeling acts on the same section map of the whole source actor. -/
theorem sectionB_relabel (η : K ≃+* K) (b : K) :
    sectionB Q split (p.relabelLong η) (w.relabelLong Q p η)
      ((p.relabelLong_long_range η 0).trans hl) M (.ofAdd b) = B (.ofAdd (η b)) := by
  apply congrArg (QuotientGroup.mk' M)
  apply Subtype.ext
  exact p.relabelLong_long η 0 b

variable [Finite F] {n : ℕ} {hn : 0 < n} (e : ScalarMarking (binaryParameters n hn) σ)

include e in
/-- Compare the unnormalized natural and cubic tensor actions in a section of
this very U. The natural field map is recovered from SL₂, then restricted to
the existing fixed field. Comparing the two reversed commutators forces the
basis labels and determines the relabeling of the entire long rank-one map. -/
theorem normalize_lower_section
    (r : SL2 K →* SL2 F)
    (hU : ∀ b, ∃ c : F, r (uni b) = uni c) (hW : r (weyl K) = weyl F)
    (hfaith : Function.Injective C)
    (hnatural : ∀ (a : F) (b : K),
      rightCommutator (A (.ofAdd a)) (B (.ofAdd b)) =
        C (.ofAdd (a * (r (uni b)).val 0 1)))
    (τ₁ τ₂ ρ : K ≃+* K) (θ x y : F)
    (htensor : ∀ a₀ a₁ a₂ b : K,
      rightCommutator (B (.ofAdd b)) (A (.ofAdd (a₀.val+a₁.val*θ+a₂.val*θ^2))) =
        C (.ofAdd (x*(τ₂ (τ₁.symm b)).val *
          ((τ₂ (ρ a₀)).val+(τ₂ (ρ a₁)).val*y+(τ₂ (ρ a₂)).val*y^2)))) :
    x = 1 ∧ y = θ ∧ ρ.trans τ₂ = RingEquiv.refl K ∧
      r.comp (Theory.PSL2.sl2FieldAut (τ₁.symm.trans τ₂).symm).toMonoidHom =
        Matrix.SpecialLinearGroup.map (ScalarMarking.SourceFixed (σ := σ)).subtype ∧
      ∀ (a : F) (b : K),
        rightCommutator
          (sectionB Q split (p.relabelLong (τ₁.symm.trans τ₂).symm)
            (w.relabelLong Q p (τ₁.symm.trans τ₂).symm)
            ((p.relabelLong_long_range (τ₁.symm.trans τ₂).symm 0).trans hl) M (.ofAdd b))
          (A (.ofAdd a)) = C (.ofAdd (a*b.val)) := by
  obtain ⟨κ,hκ⟩ := NaturalCoordinates.exists_fixed_automorphism e r hU hW
  have hnat (a : F) (b : K) :
      rightCommutator (A (.ofAdd a)) (B (.ofAdd b)) = C (.ofAdd (a*(κ b).val)) := by
    rw [hnatural,hκ]
    change C (.ofAdd (a*(κ ((uni b).val 0 1)).val)) = C (.ofAdd (a*(κ b).val))
    rw [uni_val]
    rfl
  obtain ⟨hx,hy,hmatch,hρ,hrel⟩ := ScalarComparison.normalized_section
    (ScalarMarking.SourceFixed (σ := σ)).subtype κ τ₁ τ₂ ρ θ x y C hfaith
    (fun a => A (.ofAdd a)) (fun b => B (.ofAdd b)) hnat htensor
  refine ⟨hx,hy,hρ,?_,?_⟩
  · rw [hκ,← hmatch]
    exact NaturalCoordinates.relabel_field_map _ κ
  intro a b
  rw [sectionB_relabel]
  exact hrel a b

/-- The normalized whole pinning feeds the existing positive reconstruction.
The remaining tensor equations and covariance still have to be constructed;
the source field, original endpoints, full U and quotient are preserved. -/
def positiveData (η : K ≃+* K)
    (row : StructuralRow Q split (w.indices 0) (w.indices 1))
    (hfaith : Function.Injective p.longMap) (θ : F) (hθ : σ θ ≠ θ)
    (d : EarlierModuleEquations (p.relabelLong η) e θ) :
    TrialityPresentation.PositiveRootData Q split n hn σ :=
  StructuralApplication.positiveData Q split (p.relabelLong η) (w.relabelLong Q p η)
    ((p.relabelLong_short_range η 0).trans hs) ((p.relabelLong_long_range η 0).trans hl)
    hm row (hfaith.comp (Theory.PSL2.sl2FieldAut η).injective) e θ hθ d

/-- Literal original/geometric S-image application of that normalized pinning. -/
theorem nativeHom_range_marked (η : K ≃+* K)
    (row : StructuralRow Q split (w.indices 0) (w.indices 1))
    (hfaith : Function.Injective p.longMap) (θ : F) (hθ : σ θ ≠ θ)
    (d : EarlierModuleEquations (p.relabelLong η) e θ)
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (marking : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam) (h : HypothesisF11 L S) :
    (positiveData Q split p w hs hl hm e η row hfaith θ hθ d).nativeHom.range =
      (MarkedLocal.sylowMap Q marking h).range :=
  TrialityPresentation.PositiveRootData.nativeHom_range_marked _ marking h

/-- The original numerator retains its literal quotient image of S after
relabeling the whole pinning, with no universal-completion descent. -/
theorem nativeHom_range_original {G : Type*} [Group G]
    {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h₀ : HypothesisF11 L S) (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (p₀ : RankOnePair σ (generated L S ⧸ Q₀.D)) (w₀ : WeylPlacement Q₀ p₀)
    (hs₀ : (p₀.shortOrbit 0).range = simpleRoot Q₀ split₀ (w₀.indices 0))
    (hl₀ : (p₀.longOrbit 0).range = simpleRoot Q₀ split₀ (w₀.indices 1))
    (hm₀ : rotationOrder Q₀ = 6) (η : K ≃+* K)
    (row₀ : StructuralRow Q₀ split₀ (w₀.indices 0) (w₀.indices 1))
    (hf₀ : Function.Injective p₀.longMap) (θ : F) (hθ : σ θ ≠ θ)
    (d₀ : EarlierModuleEquations (p₀.relabelLong η) e θ) :
    (positiveData Q₀ split₀ p₀ w₀ hs₀ hl₀ hm₀ e η row₀ hf₀ θ hθ d₀).nativeHom.range =
      (S.subgroupOf (generated L S)).map Q₀.q :=
  TrialityPresentation.nativeHom_range_original h₀ Q₀ split₀ _

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.ScalarAlignment
