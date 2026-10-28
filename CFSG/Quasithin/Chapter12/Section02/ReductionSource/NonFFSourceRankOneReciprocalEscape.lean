module
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Suzuki
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceRankOneOddControl
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Normal
public import CFSG.Quasithin.Chapter7.NormalizedSource.Alternatives

/-!
# Reciprocal pushing up on the original rank-one chosen module

Both actual unitary and Suzuki central quotients now give the full
pushing-up witnesses and their generalized-Fitting escape when the odd
fixed residual fails uniqueness. The original Sylow, module equality,
Chapter K action, non-FF hypothesis and odd actor are retained. The Suzuki
argument constructs the reversed component, places the other H-conjugate
inside it, and excludes the genuine C.2.7 models on the literal star map.
The intermediate reciprocal APIs remain available with their original
statements and quotient markings.

Source: Aschbacher--Smith, 4.2.5--10, pp.609--610, used in 4.4.6 and12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Chapter7.NormalizedSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

set_option linter.unusedVariables false in
/-- The unitary chosen-module branch has the full ambient Fitting escape.
All original source hypotheses, the Sylow and the actor remain explicit. -/
theorem sourceOrbit_unitary_reciprocal_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {s : ℕ} (hs2 : 2 ≤ s)
    (hq : ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    EscapeCase L D.sourceOrbit A := by
  have hc := (le_sectionCentralizer_iff A L).mp
    (hA.trans (D.sourceOrbit_relative_centralizer_le_sectionCentralizer h.toHypothesis1221 hV))
  have hM := h.toHypothesis1221.sylow_normalized_maximal_unique D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer D.sylow_normalizes_component,hM.2⟩
  exact (congrArg (fun U : Subgroup G => EscapeCase L U A) hV).mp <|
    unitary_escape_case_of_not_unique h.toHypothesis1221 D hu hs2
    (hq.of_mulEquiv (D.orbitCentralQuotientEquiv h.toHypothesis1221)) A hc.1 hc.2 ho
    (hV ▸ hA.trans inf_le_right) hnot

set_option linter.unusedVariables false in
/-- The actual Suzuki marking reaches the complete reciprocal setup and
4.2.6--8. The final 4.2.9--10 contradiction is not asserted here. -/
theorem sourceOrbit_suzuki_reciprocal_case
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ReciprocalCase L D.sourceOrbit A ∧
      ∀ g : G, Nonempty (
        (((L.map (MulAut.conj g).toMonoidHom) ⧸ pCore 2 (L.map (MulAut.conj g).toMonoidHom)) ⧸
          center ((L.map (MulAut.conj g).toMonoidHom) ⧸
            pCore 2 (L.map (MulAut.conj g).toMonoidHom))) ≃* SuzukiMatrixGroup m) := by
  have hc := (le_sectionCentralizer_iff A L).mp
    (hA.trans (D.sourceOrbit_relative_centralizer_le_sectionCentralizer h.toHypothesis1221 hV))
  have hM := h.toHypothesis1221.sylow_normalized_maximal_unique D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer D.sylow_normalizes_component,hM.2⟩
  refine ⟨?_,?_⟩
  · exact (congrArg (fun U : Subgroup G => ReciprocalCase L U A) hV).mp <|
    reciprocal_case_of_not_unique h.toHypothesis1221 D hu
      A hc.1 hc.2 ho (hV ▸ hA.trans inf_le_right) hnot
  · intro g
    let c : L.map (MulAut.conj g).toMonoidHom ≃* L :=
      (L.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
    let q := QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
    exact ⟨(centerQuotientCongr q).trans
      ((D.orbitCentralQuotientEquiv h.toHypothesis1221).trans e)⟩

set_option linter.unusedVariables false in
/-- Source 4.2.9 on the actual Suzuki orbit. Under the contrary Fitting
containment the same witnesses give an outside component of N_G(L), together
with its nontrivial quotient action on the reciprocal span. -/
theorem sourceOrbit_suzuki_reciprocal_component_case
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ReciprocalComponentCase L D.sourceOrbit A ∧
      ∀ g : G, Nonempty (
        (((L.map (MulAut.conj g).toMonoidHom) ⧸ pCore 2 (L.map (MulAut.conj g).toMonoidHom)) ⧸
          center ((L.map (MulAut.conj g).toMonoidHom) ⧸
            pCore 2 (L.map (MulAut.conj g).toMonoidHom))) ≃* SuzukiMatrixGroup m) := by
  refine ⟨?_,(D.sourceOrbit_suzuki_reciprocal_case h hmany hV hs hnm hnon
    hm e A hne hA ho hnot).2⟩
  have hc := (le_sectionCentralizer_iff A L).mp
    (hA.trans (D.sourceOrbit_relative_centralizer_le_sectionCentralizer h.toHypothesis1221 hV))
  have hM := h.toHypothesis1221.sylow_normalized_maximal_unique D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer D.sylow_normalizes_component,hM.2⟩
  exact (congrArg (fun U : Subgroup G => ReciprocalComponentCase L U A) hV).mp <|
    reciprocal_component_case_of_not_unique h.toHypothesis1221 D hu
    A hc.1 hc.2 ho (hV ▸ hA.trans inf_le_right) hnot

set_option linter.unusedVariables false in
/-- The source odd-prime rank bound of 4.2.10 on the actual Suzuki orbit,
with all original reciprocal witnesses and the concrete quotient marking. -/
theorem sourceOrbit_suzuki_reciprocal_rank_case
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ReciprocalRankCase L D.sourceOrbit A ∧
      ∀ g : G, Nonempty (
        (((L.map (MulAut.conj g).toMonoidHom) ⧸ pCore 2 (L.map (MulAut.conj g).toMonoidHom)) ⧸
          center ((L.map (MulAut.conj g).toMonoidHom) ⧸
            pCore 2 (L.map (MulAut.conj g).toMonoidHom))) ≃* SuzukiMatrixGroup m) := by
  refine ⟨?_,(D.sourceOrbit_suzuki_reciprocal_case h hmany hV hs hnm hnon
    hm e A hne hA ho hnot).2⟩
  have hc := (le_sectionCentralizer_iff A L).mp
    (hA.trans (D.sourceOrbit_relative_centralizer_le_sectionCentralizer h.toHypothesis1221 hV))
  have hM := h.toHypothesis1221.sylow_normalized_maximal_unique D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer D.sylow_normalizes_component,hM.2⟩
  exact (congrArg (fun U : Subgroup G => ReciprocalRankCase L U A) hV).mp <|
    reciprocal_rank_case_of_not_unique h.toHypothesis1221 D hu
    A hc.1 hc.2 ho (hV ▸ hA.trans inf_le_right) hnot

set_option linter.unusedVariables false in
/-- The selected outside component is normal in the actual N_G(L).
The original Suzuki marking, reciprocal witnesses and odd-rank bound remain. -/
theorem sourceOrbit_suzuki_reciprocal_normal_case
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ReciprocalNormalCase L D.sourceOrbit A ∧
      ∀ g : G, Nonempty (
        (((L.map (MulAut.conj g).toMonoidHom) ⧸ pCore 2 (L.map (MulAut.conj g).toMonoidHom)) ⧸
          center ((L.map (MulAut.conj g).toMonoidHom) ⧸
            pCore 2 (L.map (MulAut.conj g).toMonoidHom))) ≃* SuzukiMatrixGroup m) := by
  refine ⟨?_,(D.sourceOrbit_suzuki_reciprocal_case h hmany hV hs hnm hnon
    hm e A hne hA ho hnot).2⟩
  have hc := (le_sectionCentralizer_iff A L).mp
    (hA.trans (D.sourceOrbit_relative_centralizer_le_sectionCentralizer h.toHypothesis1221 hV))
  have hM := h.toHypothesis1221.sylow_normalized_maximal_unique D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer D.sylow_normalizes_component,hM.2⟩
  exact (congrArg (fun U : Subgroup G => ReciprocalNormalCase L U A) hV).mp <|
    reciprocal_normal_case_of_not_unique h.toHypothesis1221 D hu
    A hc.1 hc.2 ho (hV ▸ hA.trans inf_le_right) hnot


end CFSG.Quasithin.Chapter12.Section02.ChosenModule

open Representation.BinaryOffender BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Chapter7.NormalizedSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

set_option linter.unusedVariables false in
/-- The original Suzuki orbit supplies the actual other-conjugate placement,
exact odd-prime rank, normal nonsolvable star image, and its unchanged
two-core quotient. All original ambient hypotheses and markings remain. -/
theorem sourceOrbit_suzuki_reciprocal_placement_case
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ReciprocalPlacementCase L D.sourceOrbit A ∧
      ∀ g : G, Nonempty (
        (((L.map (MulAut.conj g).toMonoidHom) ⧸ pCore 2 (L.map (MulAut.conj g).toMonoidHom)) ⧸
          center ((L.map (MulAut.conj g).toMonoidHom) ⧸
            pCore 2 (L.map (MulAut.conj g).toMonoidHom))) ≃* SuzukiMatrixGroup m) := by
  refine ⟨?_,(D.sourceOrbit_suzuki_reciprocal_case h hmany hV hs hnm hnon
    hm e A hne hA ho hnot).2⟩
  have hc := (le_sectionCentralizer_iff A L).mp
    (hA.trans (D.sourceOrbit_relative_centralizer_le_sectionCentralizer h.toHypothesis1221 hV))
  have hM := h.toHypothesis1221.sylow_normalized_maximal_unique D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer D.sylow_normalizes_component,hM.2⟩
  exact (congrArg (fun U : Subgroup G => ReciprocalPlacementCase L U A) hV).mp <|
    reciprocal_placement_case_of_not_unique h.toHypothesis1221 D hu
    A hc.1 hc.2 ho (hV ▸ hA.trans inf_le_right) hnot

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Chapter7.NormalizedSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

set_option linter.unusedVariables false in
/-- The actual Suzuki chosen-module branch has the full ambient Fitting escape.
All original source hypotheses, the Sylow and the actor remain explicit. -/
theorem sourceOrbit_suzuki_reciprocal_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnm : ¬ HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    EscapeCase L D.sourceOrbit A := by
  have hc := (le_sectionCentralizer_iff A L).mp
    (hA.trans (D.sourceOrbit_relative_centralizer_le_sectionCentralizer h.toHypothesis1221 hV))
  have hM := h.toHypothesis1221.sylow_normalized_maximal_unique D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer D.sylow_normalizes_component,hM.2⟩
  exact (congrArg (fun U : Subgroup G => EscapeCase L U A) hV).mp <|
    suzuki_escape_case_of_not_unique h.toHypothesis1221 D hu (by omega)
    ((D.orbitCentralQuotientEquiv h.toHypothesis1221).trans e) A hc.1 hc.2 ho
    (hV ▸ hA.trans inf_le_right) hnot

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
