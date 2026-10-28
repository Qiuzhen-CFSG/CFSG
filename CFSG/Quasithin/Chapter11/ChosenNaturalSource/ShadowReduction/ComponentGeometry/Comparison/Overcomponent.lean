module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.Embeddings
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.Normalized
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.ModuleExclusions
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.SourceModules
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.OddTernaryPairs
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.OddTernaryCore
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.OddTernaryComparison
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.SporadicPoints
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.PointAlternatives
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.JankoPoints
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.HallJankoPoints
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.SectionOrderPoints
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.MathieuPoints
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.MathieuTwentyThreePoints
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.MathieuCoverPoints
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.JankoFourPlacement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.JankoFourRecognition
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison

/-!
# Chosen-flag consumers for the proper-overcomponent argument

Every subgroup here is the original ComponentGeometry.ofFlag subgroup.
Failure of maximality gives a proper maximal overcomponent, its faithful
action on the actual reduced subgroup, and T-normalization. The latter
rules out the nonnormal row of 7.0.1. For the full embedding shortlist,
the radical-centralization input eliminates the nilpotent extension and
constructs a genuine chosen-module problem for the remaining pairs.

The complete containing catalogue and rank-one exclusions are now applied
to the original flag in EmbeddingProof. The prime and quadratic-prime PSL₂
containers are excluded through their actual A₅ point-component images.
The split, Ree and both triality rows are also excluded. Thus every proper
container forces q = 4, and the point component is maximal for q > 4.

The new full-catalogue comparison proves quasisimplicity of every proper
maximal container and excludes both alternating-seven containing covers.
It therefore excludes FF and orthogonal-minus actions without a proper-pair
premise. Earlier 3.2.5 alternatives extend this to the full orbit. The
maximality endpoint retains the positive normalized-source implication and
3.2.5 explicitly. The signed odd ternary branch is now complete: its
literal point quotient embeds faithfully, the full Sylow action excludes
both A₇ covers, and rank and order comparisons exhaust the quasisimple
point catalogue. The remaining nonquasisimple point quotient gives the
elementary-plane-by-SL₂(5) proper pair, with p = 5 and linear sign derived.
The sporadic comparison now excludes nonquasisimple point quotients in
J₁, J₂, M₂₂, its triple cover, M₂₃, HS and Ru, retaining the literal
quotient maps. The J₄ comparison now uses its actual involution centralizers
and the faithful Frattini action of the full Sylow two-subgroup to exclude
its nonquasisimple point row. The complete catalogue therefore leaves only
the quintic elementary-plane pair in this branch, and supplies the actual
chosen-module consumer without an embedding premise. J₂ is now excluded
as a proper containing quotient in every branch. In the quasisimple-point
branch the full catalogue leaves seven sporadic containing rows, and the
point quotient is neither J₁ nor J₂. The actual chosen-module application
retains these derived comparisons. The HS and Ru quotient-section bounds
now exclude both containing rows in every branch. The refined chosen-module
consumer leaves only M₂₂, its triple cover, M₂₃, J₁ and J₄ for a
quasisimple point. The native J₁ Sylow-action and M₂₂ local-section
comparisons now exclude both of those containing rows, leaving the triple
M₂₂ cover, M₂₃ and J₄. The refined consumer retains the original
chosen module. The M₂₃ point comparison now constructs exactly the
PSL₃(4), A₇ or M₂₂ proper pair from the full point catalogue and applies
it to the containing chosen module. Descent through the genuine triple
M₂₂ center now excludes that containing cover, retaining the full point
catalogue and both intrinsic two-core maps. The combined chosen-module
consumer leaves a proved proper pair or J₄. In the latter row, the
original point image now has nontrivial two-core and lies with the full
Sylow in the first involution centralizer; all Mathieu-local placements
are excluded. The triple-cover recognition and the Hall argument remain
with this owner;
unconditional 11.4.2 is not asserted.
EarlierGeometry uses qt-d-1222-natural-relative-components and
qt-d-1222-natural-line-action; the shared radical implication is produced
by qt-d-1222-comparison-nonquasisimple. Their discharge and final 11.4.2
assembly belong to qt-d-1222-shadow-component-comparison.
Source: Aschbacher--Smith, 11.4.2, printed p.776.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : Chapter12.Section02.ChosenModule T L V}

/-- The actual chosen flag supplies a strict maximal counterexample with
faithful action and a fixed component orbit. No embedding or FF input is used. -/
theorem ofFlag_counterexample
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hn : (ofFlag S f X z H).Kz ∉ Chapter1.LStar G (T : Subgroup G)) :
    ∃ J ∈ Chapter1.LStar G (T : Subgroup G),
      (ofFlag S f X z H).Kz < J ∧
      z ∈ reducedIn T J ∧
      ChapterA.Section04.IsFaithfulSignalizerType J ∧
      Chapter3.Section02.localOrbit T J = J := by
  obtain ⟨J, hJ, hle⟩ := h.exists_maximal_overcomponent
  have hlt : (ofFlag S f X z H).Kz < J := lt_of_le_of_ne hle (by
    intro he
    exact hn (he.symm ▸ hJ))
  exact ⟨J, hJ, hlt, point_mem_reduced h hJ.1, faithful h hJ.1 hlt,
    localOrbit_eq h hJ.1 hle⟩

/-- Applying the complete embedding shortlist to the actual flag excludes
its nilpotent row and selects an original chosen module for the remaining J.
The displayed embedding premise still needs its classification proof. -/
theorem ofFlag_chosenModule_of_embedding
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hrad : MaximalRadicalCentralization T) {J : Subgroup G}
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J)
    (hemb : ProperEmbedding (ofFlag S f X z H).Kz J) :
    QuasisimplePair (ofFlag S f X z H).Kz J ∧
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
      ∃ W : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T J W) := by
  obtain ⟨hp, hq, _, _⟩ := quasisimple_setup_of_embedding h hrad hJ hlt hemb
  exact ⟨hp, exists_chosenModule h hJ hlt hq⟩

/-- The derived nonquasisimple-point comparison constructs the original
chosen module for its containing component. No proper-embedding or
radical-centralization premise is required. -/
theorem ofFlag_chosenModule_of_nonquasisimple_point
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hn : ¬ IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J) :
    QuasisimplePair (ofFlag S f X z H).Kz J ∧
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
      ∃ W : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T J W) := by
  obtain ⟨_, hsmall, hlarge, _⟩ := EmbeddingProof.ofFlag_nonquasisimple_proper_pair
    S f X z H h hne hn hlinear h1132 e hcent hJ hlt
  have hq := EmbeddingProof.ofFlag_proper_overcomponent_quasisimple
    S f X z H h hne hlinear h1132 e hcent hJ hlt
  exact ⟨.elementaryLinear 5 (by decide) (by decide) hsmall hlarge,
    exists_chosenModule h hJ hlt hq⟩

/-- The full quasisimple-point catalogue supplies the actual containing
chosen module, excludes the J₂ containing row, and excludes both small
Janko point quotients. All remaining models refer to the original quotient. -/
theorem ofFlag_chosenModule_of_quasisimple_point
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hqs : IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J) :
    S.field.degree = 2 ∧
      EmbeddingProof.QuasisimplePointContainer (J ⧸ pCore 2 J) ∧
      (¬ Nonempty (((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ≃* Janko1.Model)) ∧
      (¬ Nonempty (((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ≃*
        Sporadic.LeechRelated.J2.Carrier)) ∧
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
      ∃ W : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T J W) := by
  obtain ⟨hd,hm⟩ := EmbeddingProof.ofFlag_quasisimple_point_containers
    S f X z H h hne hqs hlinear h1132 e hcent hJ hlt
  have hq := EmbeddingProof.ofFlag_proper_overcomponent_quasisimple
    S f X z H h hne hlinear h1132 e hcent hJ hlt
  exact ⟨hd,hm,EmbeddingProof.point_not_jankoOne_in_containers h hJ.1 hlt hm,
    EmbeddingProof.point_not_jankoTwo_in_containers h hJ.1 hlt hm,
    exists_chosenModule h hJ hlt hq⟩

/-- The new HS and Ru exclusions feed the actual containing chosen module.
The full source catalogue leaves only the Mathieu and Janko carriers,
with the original point quotient and inherited hypotheses unchanged. -/
theorem ofFlag_chosenModule_of_mathieu_janko_point_container
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hqs : IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J) :
    S.field.degree = 2 ∧
      EmbeddingProof.MathieuJankoPointContainer (J ⧸ pCore 2 J) ∧
      (¬ Nonempty (((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ≃* Janko1.Model)) ∧
      (¬ Nonempty (((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ≃*
        Sporadic.LeechRelated.J2.Carrier)) ∧
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
      ∃ W : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T J W) := by
  obtain ⟨hd,hm⟩ := EmbeddingProof.ofFlag_quasisimple_point_mathieu_janko_containers
    S f X z H h hne hqs hlinear h1132 e hcent hJ hlt
  obtain ⟨_,_,h1,h2,hyp,hchosen⟩ := ofFlag_chosenModule_of_quasisimple_point
    S f X z H h hne hqs hlinear h1132 e hcent hJ hlt
  exact ⟨hd,hm,h1,h2,hyp,hchosen⟩

/-- The J₁ and M₂₂ exclusions feed the actual containing chosen module.
Only the triple cover of M₂₂, M₂₃ and J₄ remain in the quasisimple-point
branch; the literal point quotient and original source inputs are retained. -/
theorem ofFlag_chosenModule_of_cover_or_large_point_container
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hqs : IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J) :
    S.field.degree = 2 ∧
      (Chapter1.Section02.LocalModels.IsM22Cover (J ⧸ pCore 2 J) ∨
        Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M23) ∨
        Nonempty ((J ⧸ pCore 2 J) ≃* Janko4.Model)) ∧
      (¬ Nonempty (((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ≃* Janko1.Model)) ∧
      (¬ Nonempty (((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ≃*
        Sporadic.LeechRelated.J2.Carrier)) ∧
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
      ∃ W : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T J W) := by
  obtain ⟨hd,hm⟩ := EmbeddingProof.ofFlag_quasisimple_point_cover_or_large_container
    S f X z H h hne hqs hlinear h1132 e hcent hJ hlt
  obtain ⟨_,_,h1,h2,hyp,hchosen⟩ := ofFlag_chosenModule_of_quasisimple_point
    S f X z H h hne hqs hlinear h1132 e hcent hJ hlt
  exact ⟨hd,hm,h1,h2,hyp,hchosen⟩

/-- The M₂₃ row supplies its original proper pair and the actual
containing chosen module, without a shortened-catalogue premise. -/
theorem ofFlag_chosenModule_of_mathieuTwentyThree_point_container
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J)
    (hm : Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M23)) :
    QuasisimplePair (ofFlag S f X z H).Kz J ∧
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
      ∃ W : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T J W) := by
  have hpair := EmbeddingProof.ofFlag_mathieuTwentyThree_proper_pair
    S f X z H h hne hlinear h1132 e hJ.1 hlt hm
  have hq := EmbeddingProof.ofFlag_proper_overcomponent_quasisimple
    S f X z H h hne hlinear h1132 e hcent hJ hlt
  exact ⟨hpair,exists_chosenModule h hJ hlt hq⟩

/-- Apply the complete comparison to the original containing chosen
module: the quintic and M₂₃ pairs are proved, while the central M₂₂ cover
and J₄ retain their literal quotient models as the remaining cases. -/
theorem ofFlag_chosenModule_of_proper_embedding_or_remaining_container
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J) :
    S.field.degree = 2 ∧
      (ProperEmbedding (ofFlag S f X z H).Kz J ∨
        Chapter1.Section02.LocalModels.IsM22Cover (J ⧸ pCore 2 J) ∨
        Nonempty ((J ⧸ pCore 2 J) ≃* Janko4.Model)) ∧
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
      ∃ W : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T J W) := by
  obtain ⟨hd,hp⟩ := EmbeddingProof.ofFlag_proper_embedding_or_cover_or_jankoFour
    S f X z H h hne hlinear h1132 e hcent hJ hlt
  have hq := EmbeddingProof.ofFlag_proper_overcomponent_quasisimple
    S f X z H h hne hlinear h1132 e hcent hJ hlt
  exact ⟨hd,hp,exists_chosenModule h hJ hlt hq⟩

/-- The actual containing chosen module satisfies a proved proper pair or
the sole remaining J₄ comparison. The complete source catalogue and its
nonquasisimple quintic branch are retained. -/
theorem ofFlag_chosenModule_of_proper_embedding_or_jankoFour
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J) :
    S.field.degree = 2 ∧
      (ProperEmbedding (ofFlag S f X z H).Kz J ∨
        Nonempty ((J ⧸ pCore 2 J) ≃* Janko4.Model)) ∧
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
      ∃ W : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T J W) := by
  obtain ⟨hd,hp⟩ := EmbeddingProof.ofFlag_proper_embedding_or_jankoFour
    S f X z H h hne hlinear h1132 e hcent hJ hlt
  have hq := EmbeddingProof.ofFlag_proper_overcomponent_quasisimple
    S f X z H h hne hlinear h1132 e hcent hJ hlt
  exact ⟨hd,hp,exists_chosenModule h hJ hlt hq⟩
/-- The actual containing chosen module retains every proved proper pair.
In the remaining J₄ row, the literal point image has nontrivial two-core
and lies with the full Sylow in the first involution centralizer. -/
theorem ofFlag_chosenModule_of_proper_embedding_or_jankoFour_placement
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J) :
    S.field.degree = 2 ∧
      (ProperEmbedding (ofFlag S f X z H).Kz J ∨
        EmbeddingProof.JankoFourPointPlacement (ofFlag S f X z H) J) ∧
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
      ∃ W : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T J W) := by
  obtain ⟨hd,hp⟩ := EmbeddingProof.ofFlag_proper_embedding_or_jankoFour_placement
    S f X z H h hne hlinear h1132 e hcent hJ hlt
  have hq := EmbeddingProof.ofFlag_proper_overcomponent_quasisimple
    S f X z H h hne hlinear h1132 e hcent hJ hlt
  exact ⟨hd,hp,exists_chosenModule h hJ hlt hq⟩

/-- The recognized proper embedding supplies the actual chosen module for
its containing component. The J₄ row is now the genuine triple-M₂₂ pair. -/
theorem ofFlag_chosenModule_of_proper_embedding
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J) :
    S.field.degree = 2 ∧ ProperEmbedding (ofFlag S f X z H).Kz J ∧
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
      ∃ W : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T J W) := by
  obtain ⟨hd,hemb⟩ := EmbeddingProof.ofFlag_proper_embedding
    S f X z H h hne hlinear h1132 e hcent hJ hlt
  have hq := EmbeddingProof.ofFlag_proper_overcomponent_quasisimple
    S f X z H h hne hlinear h1132 e hcent hJ hlt
  exact ⟨hd,hemb,exists_chosenModule h hJ hlt hq⟩


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent
