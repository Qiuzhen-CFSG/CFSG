module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation.Sp4Contradiction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation.G2Reselection
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation.ProjectiveKernels

/-!
# Both terminal orientations in the original source triangle

The canonical-other-residual theorem identifies the supplied K₀ using its
distinction from L₁ and K. Common-normal and original 7.0.1/3.2.5 inputs
construct the faithful maximal join I = K₀ ∨ L₂ and its reselected natural
geometry outside the retained SL₃(4) row.

For G₂/G₂, B.4.6(14) identifies the original cubic X₁ with X ∩ L₂ and with
the reselected point quotient kernel. For Sp₄/Sp₄, the four actual Cartan
action characters identify the same cubic with that kernel. Both conclusions
contradict its action in the original PSL₃(4) component and PGL₃(4) extension.
All quotient kernels use their full intrinsic two-cores.

The conditional consumer combines these contradictions with the earlier
SL₃ exclusions on the exact original L and the same canonical I. It proves
both opposite orientations, assembles every FieldFourTriangle clause and
applies RefinementReduction.complete. The common normal subgroup, earlier
source outputs and both same-vertex SL₃ exclusions remain explicit; their
final discharge is retained by the original relative-components and natural
local-geometry owners. This is the terminal implication, not an unconditional
proof of all of 11.1.2.
Source: Aschbacher--Smith, 11.1.2, printed pp.762--764.
-/

open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
open Triangle Triangle.TerminalOrientation
public noncomputable section
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (f : InvariantFlag (.g2 m))

/-- At the same canonical K₀, the original G₂/G₂ branch supplies all the
reselected geometry and identifies the literal cubic quotient kernels.
The common normal subgroup and original earlier-source results remain explicit. -/
theorem g2_canonical_common_normal_reselection
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hne₀ : K₀ ≠ f.Li 0)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G))
    (hpre : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      Chapter7.NormalizedSource.Alternatives G D_J.orbitRepresentation D_J.orbitComponent ∧
        D_J.Source325Alternatives)
    (hmI : ClassificationModels.IsG2At
      ((K₀ ⊔ f.Li 1 : Subgroup G) ⧸ pCore 2 (K₀ ⊔ f.Li 1 : Subgroup G)) 4) :
    (∀ J : Subgroup G, J ∈ Chapter1.L G T → J ≤ K → J ≠ K → J ≠ f.Li 0 → J = K₀) ∧
      f.Li 0 ⊔ K₀ = K ∧ K₀ ∈ Chapter1.He G ∧
      (K₀ ⊔ f.Li 1) ∈ Chapter1.LStar G T ∧
      (K₀ ⊔ f.Li 1) ∈ MainForward.faithfulLocalComponents T ∧
      Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3 ∧
      ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 0) ≤ Closure.coreQuotientCentralizer K ∧
      ∃ (U : Subgroup G) (D_I : ChosenModule T (K₀ ⊔ f.Li 1) U)
        (S_I : D_I.NonbinaryNaturalInput), S_I.field.degree = 2 ∧
        IsCartan T (K₀ ⊔ f.Li 1) X ∧
        X ⊓ Closure.coreQuotientCentralizer K₀ = X ⊓ f.Li 1 ∧
        X ⊓ Closure.coreQuotientCentralizer K₀ =
          X ⊓ Closure.coreQuotientCentralizer (f.Li 0) ∧
        ∃ f_I : InvariantFlag (coordinates D_I S_I), f_I.IsInnerUnique ∧
          K ≤ centralizer (f_I.Vi 0 : Set G) ∧
          f_I.Li 0 = K₀ ∧ f_I.Li 1 = f.Li 1 ∧ f_I.Ri 1 = f.Ri 1 ∧
          Source.NormalComponentIn (normalizer (f_I.Vi 0 : Set G)) K ∧
          f_I.Li 0 < K ∧ K ∈ Chapter1.He G ∧
          ∀ J : Subgroup G, Source.ComponentIn (normalizer (f_I.Vi 0 : Set G)) J →
            f_I.Li 0 ≤ J → J = K := by
  obtain ⟨J,hJ,hJK,hne,hne₁,hunique,hTJ,hHe,hgen,hmJ⟩ :=
    first_triangle_other_residual D S f hm₁ hK hLK hk
  have he : K₀ = J := hunique K₀ hK₀ hK₀K.le hK₀K.ne hne₀
  subst J
  obtain ⟨hmax,hsource,U,D_I,hcases⟩ :=
    g2_triangle_reselected_component_of_common_normal_and_source701325
      D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
      hQ hQT hTQ hKQ hLQ hpre
  have hnot : ¬ Source.IsSL
      ((K₀ ⊔ f.Li 1 : Subgroup G) ⧸ pCore 2 (K₀ ⊔ f.Li 1 : Subgroup G)) 3 4 := by
    rintro ⟨F,_,_,hF,⟨e⟩⟩
    obtain ⟨E,_,_,hE,⟨g⟩⟩ := hmI
    have hc := Nat.card_congr (e.symm.trans g).toEquiv
    rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,Atlas.G2.card_Model,hF,hE] at hc
    norm_num at hc
  obtain ⟨S_I,hd,hf,hm,hcartan,f_I,hinner,hpoint,hfirst,hsecond,hradical,
    hrelative,hfirstK,hKHe,huniqueK⟩ := hcases.resolve_left hnot
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hcard₁,_⟩ :=
    g2_canonical_triangle_cubic D S m f hu hm₁ hfour hX hK hLK hk hp
  have he := point_kernel_eq_plane_of_g2_model D_I S_I hd hmI f_I hcartan
  rw [hfirst,hsecond] at he
  exact ⟨hunique,hgen,hHe,hmax.1,
    (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T _).mpr ⟨hmax.1.1,hmax.2⟩,hcard₁,
    first_projective_cubic_not_central D S f hu hfour hX hK hk inf_le_left hcard₁,
    U,D_I,S_I,hd,
    hcartan,he,he.trans (g2_point_kernel_eq_plane S m hfour f hX).symm,
    f_I,hinner,hpoint,hfirst,hsecond,hradical,hrelative,hfirstK,hKHe,huniqueK⟩

/-- The original G₂/G₂ triangle is impossible. Its canonical cubic would
lie in both local quotient kernels of the same PSL₃(4) component, contrary
to its faithful action on the full quotient. Common Q and 7.0.1/3.2.5 are
the preceding source inputs; no orientation or SL₃ exclusion is assumed. -/
theorem g2_canonical_common_normal_not_g2
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hne₀ : K₀ ≠ f.Li 0)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G))
    (hpre : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      Chapter7.NormalizedSource.Alternatives G D_J.orbitRepresentation D_J.orbitComponent ∧
        D_J.Source325Alternatives)
 :
    ¬ ClassificationModels.IsG2At
      ((K₀ ⊔ f.Li 1 : Subgroup G) ⧸ pCore 2 (K₀ ⊔ f.Li 1 : Subgroup G)) 4 := by
  intro hmI
  obtain ⟨_,_,_,_,_,hcard₁,_,U,D_I,S_I,hd,hXI,he,hker,rest⟩ :=
    g2_canonical_common_normal_reselection D S m f hu hm₁ hm₂ hfour hfix hX hK hLK
      hK₀ hK₀K hne₀ hTK₀ hk hp hcard hmove hQ hQT hTQ hKQ hLQ hpre hmI
  exact first_projective_cubic_not_in_other_kernel D S f hu hm₁ hfour hX hK hLK
    hK₀ hK₀K hne₀ hk inf_le_left hcard₁ inf_le_right (hker.ge.trans inf_le_right)


end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
open Triangle Triangle.TerminalOrientation
public noncomputable section
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

/-- Terminal source implication, retaining the two preceding SL₃ exclusions
on the original L and the same canonical I = K₀ ∨ L₂. The common Q and
7.0.1/3.2.5 outputs are earlier-source inputs. Both orientations and faithful
maximality are proved here. Their final discharge belongs to the original
relative-components and natural-local-geometry assembly owners. -/
theorem canonical_orientation_of_common_normal_and_sl3_exclusions
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hne₀ : K₀ ≠ f.Li 0)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G))
    (hpre : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      Chapter7.NormalizedSource.Alternatives G D_J.orbitRepresentation D_J.orbitComponent ∧
        D_J.Source325Alternatives)
    (hnotL : ¬ Source.IsSL (L ⧸ pCore 2 L) 3 4)
    (hnotI : ¬ Source.IsSL
      ((K₀ ⊔ f.Li 1 : Subgroup G) ⧸ pCore 2 (K₀ ⊔ f.Li 1 : Subgroup G)) 3 4) :
    (K₀ ⊔ f.Li 1) ∈ Chapter1.LStar G T ∧
      (K₀ ⊔ f.Li 1) ∈ MainForward.faithfulLocalComponents T ∧
      TriangleOrientation L (K₀ ⊔ f.Li 1) := by
  have hF : Nat.card S.field.Carrier = 4 := by simpa [hfour] using S.field.card_eq
  cases c with
  | sl3 m => exact (hnotL ⟨S.field.Carrier,inferInstance,inferInstance,hF,⟨m.groupEquiv⟩⟩).elim
  | sp4 m =>
    obtain ⟨hmax,_,U,D_I,hcases⟩ :=
      sp4_triangle_reselected_component_of_common_normal_and_source701325
        D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
        hQ hQT hTQ hKQ hLQ hpre
    obtain ⟨_,_,_,hmI,_⟩ := hcases.resolve_left hnotI
    refine ⟨hmax.1,
      (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T _).mpr ⟨hmax.1.1,hmax.2⟩,?_⟩
    rcases hmI with hSp | hG
    · exact (sp4_canonical_common_normal_not_sp4 D S m f hu hm₁ hm₂ hfour hfix
        hX hK hLK hK₀ hK₀K hne₀ hTK₀ hk hp hcard hmove hQ hQT hTQ hKQ hLQ hpre hSp).elim
    · exact .inr ⟨⟨S.field.Carrier,inferInstance,inferInstance,hF,⟨m.groupEquiv⟩⟩,hG⟩
  | g2 m =>
    obtain ⟨hmax,_,U,D_I,hcases⟩ :=
      g2_triangle_reselected_component_of_common_normal_and_source701325
        D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
        hQ hQT hTQ hKQ hLQ hpre
    obtain ⟨_,_,_,hmI,_⟩ := hcases.resolve_left hnotI
    refine ⟨hmax.1,
      (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T _).mpr ⟨hmax.1.1,hmax.2⟩,?_⟩
    rcases hmI with hSp | hG
    · exact .inl ⟨⟨S.field.Carrier,inferInstance,inferInstance,hF,⟨m.groupEquiv⟩⟩,hSp⟩
    · exact (g2_canonical_common_normal_not_g2 D S m f hu hm₁ hm₂ hfour hfix
        hX hK hLK hK₀ hK₀K hne₀ hTK₀ hk hp hcard hmove hQ hQT hTQ hKQ hLQ hpre hG).elim

/-- All literal clauses of the conditional field-four triangle: the
canonical other residual, its uniqueness, the faithful maximal join and
both opposite orientations. No triangle or orientation is an input. -/
theorem field_four_triangle_of_common_normal_and_sl3_exclusions
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hne₀ : K₀ ≠ f.Li 0)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G))
    (hpre : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      Chapter7.NormalizedSource.Alternatives G D_J.orbitRepresentation D_J.orbitComponent ∧
        D_J.Source325Alternatives)
    (hnotL : ¬ Source.IsSL (L ⧸ pCore 2 L) 3 4)
    (hnotI : ¬ Source.IsSL
      ((K₀ ⊔ f.Li 1 : Subgroup G) ⧸ pCore 2 (K₀ ⊔ f.Li 1 : Subgroup G)) 3 4) :
    FieldFourTriangle T L (f.Li 0) (f.Li 1) K X := by
  obtain ⟨J,hJ,hJK,hne,hne₁,hunique,_⟩ :=
    first_triangle_other_residual D S f hm₁ hK hLK hk
  have he : K₀ = J := hunique K₀ hK₀ hK₀K.le hK₀K.ne hne₀
  obtain ⟨hmax,hfaith,ho⟩ :=
    canonical_orientation_of_common_normal_and_sl3_exclusions D S f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hne₀ hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ hpre hnotL hnotI
  refine ⟨hp,K₀,hK₀,hK₀K.le,hK₀K.ne,hne₀,?_,hmax,hfaith,ho⟩
  intro A hA hAK hneA hneA₁
  exact (hunique A hA hAK hneA hneA₁).trans he.symm

/-- Apply the terminal construction to the original refinement reduction.
The extra premises are the retained earlier-source outputs on these same
vertices; this conditional implication does not assert their discharge. -/
theorem refinement_complete_of_common_normal_and_sl3_exclusions
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hne₀ : K₀ ≠ f.Li 0)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G))
    (hpre : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      Chapter7.NormalizedSource.Alternatives G D_J.orbitRepresentation D_J.orbitComponent ∧
        D_J.Source325Alternatives)
    (hnotL : ¬ Source.IsSL (L ⧸ pCore 2 L) 3 4)
    (hnotI : ¬ Source.IsSL
      ((K₀ ⊔ f.Li 1 : Subgroup G) ⧸ pCore 2 (K₀ ⊔ f.Li 1 : Subgroup G)) 3 4)
    {i : Fin 2} (href : RefinementReduction L (f.Li 0) (f.Li 1) K X i S.field.degree) :
    RefinementAlternative T L (f.Li 0) (f.Li 1) K X i S.field.degree := by
  apply href.complete
  intro _ _ _
  exact field_four_triangle_of_common_normal_and_sl3_exclusions D S f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hne₀ hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ hpre hnotL hnotI

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
