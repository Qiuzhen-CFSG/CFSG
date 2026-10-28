module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.MarkedLocal
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.LocalCoordinates

/-!
# Normal generation without perfect local factors

Pull a normal subgroup containing the actual unipotent image back to each
original factor. Each pullback contains the original Sylow. Frattini's
argument and uniqueness of its proper overgroup force both pullbacks to
be the whole factors. The factor and original Sylow images generate the
same marked quotient. This includes the nonperfect local case q=2.

The final specialization retains the literal original generated quotient.
Source: DGS, Groups and Graphs, Theorem D, printed p.224; AS F.1.1--3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include Q e h split

/-- A normal subgroup containing the actual original unipotent group is the whole quotient,
including when the local rank-one factors are not perfect. -/
theorem normal_eq_top_of_unipotent_le (R : Subgroup (X ⧸ Q.D)) [R.Normal]
    (hU : split.U ≤ R) : R = ⊤ := by
  have hf (i : Fin 2) : (factorMap Q e i).range ≤ R := by
    let : Finite (L i) := h.finite_local i
    obtain ⟨T,hT⟩ := h.sylow i
    let f := factorMap Q e i
    have hTR : (T : Subgroup (L i)) ≤ R.comap f := by
      intro t ht
      have htS : (t : G) ∈ S := by
        have hm : (t : G) ∈ (T : Subgroup (L i)).map (L i).subtype :=
          mem_map_of_mem _ ht
        rw [hT] at hm
        exact hm.1
      have he : f t = sylowMap Q e h ⟨t,htS⟩ := endpoint_sylow Q e h i ⟨t,htS⟩
      change f t ∈ R
      rw [he]
      exact hU ((sylow_range Q e h split) ▸ (show sylowMap Q e h ⟨t,htS⟩ ∈
        (sylowMap Q e h).range from ⟨_,rfl⟩))
    have facts := rankOneSylowFacts_of_rankOneQuotient (h.quotient i) T
    have hfull : (⊤ : Subgroup (L i)) ≤ R.comap f := by
      rw [← local_normalClosure_eq_top T facts.proper facts.unique_maximal]
      exact normalClosure_le_normal hTR
    rintro _ ⟨t,rfl⟩
    exact hfull (mem_top t)
  apply top_unique
  rw [← factors_generate Q e h]
  exact sup_le (sup_le (hf 0) (hf 1)) ((sylow_range Q e h split).le.trans hU)

/-- The original unipotent group normally generates this same marked finite quotient. -/
theorem unipotent_normalClosure_eq_top :
    normalClosure (split.U : Set (X ⧸ Q.D)) = ⊤ :=
  normal_eq_top_of_unipotent_le Q e h split _ le_normalClosure

omit Q e split in
/-- Application to the literal generated-source quotient and its original marking. -/
theorem original_unipotent_normalClosure_eq_top
    (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits) :
    normalClosure (split₀.U : Set ((generated L S) ⧸ Q₀.D)) = ⊤ :=
  unipotent_normalClosure_eq_top Q₀ (originalMarkedIso Q₀) h split₀
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
