module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted.Models
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Construction.Prescribed
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.ParameterBound
/-!
# Marked Hall witnesses with intrinsic normalizer escape

The Hall subgroup contains the exact reflected cyclic subgroup constructed
from the marked model. Thus its prime-subgroup normalizers escape the actual
minimal-parabolic maximal subgroup. Both single and exchanged component
families retain their original quotient maps and source clauses.
Source: Aschbacher–Smith E.2.2 and E.6.27, pp.215–216,257.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted
open ChapterB
variable {X : Type*} [Group X] [Finite X]
theorem intrinsic_of_cyclic_escape (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    {f : ℕ} (hf : 0 < f) (hc : HallControl S hP)
    (he : ∃ D : Subgroup X, D ≤ minimalParabolicMax S hP ∧ IsCyclic D ∧ Nat.card D=2^f-1 ∧
      ∀ (p : ℕ) (_ : Fact p.Prime) (A : Subgroup X), Odd p → A ≤ D → IsPGroup p A →
        ¬ normalizer (A : Set X) ≤ minimalParabolicMax S hP) :
    ∃ d : IntrinsicHallCartanData S hP f,
      ∀ (p : ℕ) (_ : Fact p.Prime) (A : Subgroup X), Odd p → A ≤ d.witness.cyclicGroup →
        IsPGroup p A → ¬ normalizer (A : Set X) ≤ minimalParabolicMax S hP := by
  obtain ⟨D,hDM,hDc,hcard,hN⟩ := he
  obtain ⟨d,hd⟩ := intrinsic_with_prescribed_cyclic S hP hf hc D hDM hDc hcard
  exact ⟨d,hd.symm ▸ hN⟩

theorem bender_intrinsic_escape (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    {f : ℕ} (hf : 0 < f) {K : Subgroup X} (hK : K.IsCComponent)
    (hc : SingleClauses (minimalParabolicMax S hP) K S)
    (hm : BenderModel (minimalParabolicMax S hP) K f) :
    ∃ d : IntrinsicHallCartanData S hP f,
      ∀ (p : ℕ) (_ : Fact p.Prime) (A : Subgroup X), Odd p → A ≤ d.witness.cyclicGroup →
        IsPGroup p A → ¬ normalizer (A : Set X) ≤ minimalParabolicMax S hP :=
  intrinsic_of_cyclic_escape S hP hf (bender_hallControl S hP hK hc hm)
    (bender_cyclic_escape S hP K hc hm)

theorem exchanged_intrinsic_escape (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    {f : ℕ} (hf : 0 < f) {K : Subgroup X} (hK : K.IsCComponent)
    (hqs : Theory.GroupTheory.IsQuasisimple (K ⧸ pCore 2 K))
    (hc : ExchangedClauses (minimalParabolicMax S hP) K S)
    (hm : ExchangedModel (minimalParabolicMax S hP) K f) :
    ∃ d : IntrinsicHallCartanData S hP f,
      ∀ (p : ℕ) (_ : Fact p.Prime) (A : Subgroup X), Odd p → A ≤ d.witness.cyclicGroup →
        IsPGroup p A → ¬ normalizer (A : Set X) ≤ minimalParabolicMax S hP := by
  obtain ⟨N,hNM,hn,hgen,hd⟩ := ExchangedHall.normal_section hc hK hqs
    (minimalParabolicMax_spec S hP).2 (ExchangedHall.model_overlap_commutator hm)
  exact intrinsic_of_cyclic_escape S hP hf
    (ExchangedHall.hallControl_of_normal_section S hP N hNM hn hgen hd)
    (rank_one_cyclic_escape S hP K (.inr hc) hm)

theorem diagram_intrinsic_escape (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    {f : ℕ} (hf : 1 < f) {K : Subgroup X} (hK : K.IsCComponent)
    (hc : SingleClauses (minimalParabolicMax S hP) K S)
    (hm : DiagramModel (minimalParabolicMax S hP) K S f) :
    ∃ d : IntrinsicHallCartanData S hP f,
      ∀ (p : ℕ) (_ : Fact p.Prime) (A : Subgroup X), Odd p → A ≤ d.witness.cyclicGroup →
        IsPGroup p A → ¬ normalizer (A : Set X) ≤ minimalParabolicMax S hP := by
  apply intrinsic_of_cyclic_escape S hP (by omega) _ (diagram_cyclic_escape S hP K hc hf hm)
  rcases hm with ⟨F,hF,hfin,hchar,_,hcard,e,he,_⟩ | ⟨F,hF,hfin,hchar,_,hcard,e,he,_⟩
  · exact DiagramHall.linear_hallControl hf hcard S hP K hK hc e he
  · exact DiagramHall.symplectic_hallControl S hP hK hc hf hcard e he
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted
