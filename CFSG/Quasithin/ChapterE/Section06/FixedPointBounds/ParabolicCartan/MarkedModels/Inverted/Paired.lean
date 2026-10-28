module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted.Normal
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.PairedMarked
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NumericalPaired
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.ExchangedClauses
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
/-!
# The complete reflected dispatcher and its sole odd paired row

Every original exchanged binary PSL2 or Suzuki component supplies actual
E-generation, the correct numerical upper bound and the same reflected
Hall witness. The full original component selection therefore leaves only
the literal paired odd-prime PSL2 family; all other rows give the actual
residual E.6.27 alternative without earlier containment callbacks.
Source: Aschbacher–Smith E.2.2 and E.6.27, pp.215–216,257.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted
open ChapterB
universe u
variable {H:Type u} [Group H] [Finite H]
theorem source_exchanged_intrinsic_escape
    (hH:IsSQTK KnownSimple.IsKnownSimple H) (T:Sylow 2 H) (hP:IsMinimalParabolicOver T ⊤)
    (hs:¬Group.IsSolvable H) (K:Subgroup H) (hK:K.IsCComponent)
    (hqs:IsQuasisimple (K⧸pCore 2 K)) (hgen:K⊔(T:Subgroup H)=⊤) (hn : ¬K.Normal)
    {f : ℕ} (hm : ExchangedModel (minimalParabolicMax T hP) K f) :
    IsEGenerated f H ∧ generationParameter H≤f ∧
      ∃ d : IntrinsicHallCartanData T hP f,
        ∀ (p : ℕ) (_ : Fact p.Prime) (A : Subgroup H), Odd p → A ≤ d.witness.cyclicGroup →
          IsPGroup p A → ¬ normalizer (A : Set H) ≤ minimalParabolicMax T hP := by
  have hc := source_exchanged_clauses (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    hH T hP hs hK hqs hgen hn
  have hmodel : (2 ≤ f ∧ ClassicalGroup.IsPSL
      (sourceImage (minimalParabolicMax T hP) K) 2 (2^f)) ∨
      ∃ m : ℕ, 0 < m ∧ f = 2*m+1 ∧ Nonempty
        ((sourceImage (minimalParabolicMax T hP) K) ≃*
          BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
    rcases hm with ⟨F,hF,hfin,hchar,hf,hcard,e,he⟩ | ⟨m,hm,hf,e,he⟩
    · exact Or.inl ⟨hf,F,hF,hfin,hcard,⟨e⟩⟩
    · exact Or.inr ⟨m,by omega,hf,⟨e⟩⟩
  have hf : 0 < f := by
    rcases hmodel with ⟨hf,_⟩ | ⟨m,hm,hf,_⟩ <;> omega
  exact ⟨paired_bender_isEGenerated ChapterA.Section02.theoremA_knownSimple hH T hP hs K hK hgen hn hmodel,
    paired_bender_parameter_le ChapterA.Section02.theoremA_knownSimple hH T hP hs K hK hgen hn hmodel,
    exchanged_intrinsic_escape T hP hf hK hqs hc hm⟩

theorem source_exchanged_intrinsic_escape_or_odd
    (hH:IsSQTK KnownSimple.IsKnownSimple H) (T:Sylow 2 H) (hP:IsMinimalParabolicOver T ⊤)
    (hs:¬Group.IsSolvable H) (K:Subgroup H) (hK:K.IsCComponent)
    (hqs:IsQuasisimple (K⧸pCore 2 K)) (hgen:K⊔(T:Subgroup H)=⊤) (hn : ¬K.Normal) :
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ 7 ≤ p ∧
      ClassicalGroup.IsPSL (sourceImage (minimalParabolicMax T hP) K) 2 p) ∨
    ∃ f:ℕ, IsEGenerated f H ∧ generationParameter H≤f ∧
      ∃ d : IntrinsicHallCartanData T hP f,
        ∀ (p : ℕ) (_ : Fact p.Prime) (A : Subgroup H), Odd p → A ≤ d.witness.cyclicGroup →
          IsPGroup p A → ¬ normalizer (A : Set H) ≤ minimalParabolicMax T hP := by
  rcases source_exchanged_marked_cases ChapterA.Section02.theoremA_knownSimple
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hH T hP hs K hK hgen hn with
    ⟨f,hf,hm⟩ | ho
  · exact Or.inr ⟨f,source_exchanged_intrinsic_escape hH T hP hs K hK hqs hgen hn hm⟩
  · exact Or.inl ho
/-- The actual original minimal parabolic is reduced to the sole remaining
paired odd-prime row, or supplies the complete reflected Cartan witness. -/
theorem source_intrinsic_escape_or_paired_odd
    (hH:IsSQTK KnownSimple.IsKnownSimple H) (T:Sylow 2 H) (hP:IsMinimalParabolicOver T ⊤)
    (hn : 1 < generationParameter H) :
    (∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      K ⊔ (T : Subgroup H) = ⊤ ∧ ¬K.Normal ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ 7 ≤ p ∧
        ClassicalGroup.IsPSL (sourceImage (minimalParabolicMax T hP) K) 2 p) ∨
    ∃ f:ℕ, IsEGenerated f H ∧ generationParameter H≤f ∧
      ∃ d : IntrinsicHallCartanData T hP f,
        ∀ (p : ℕ) (_ : Fact p.Prime) (A : Subgroup H), Odd p → A ≤ d.witness.cyclicGroup →
          IsPGroup p A → ¬ normalizer (A : Set H) ≤ minimalParabolicMax T hP := by
  have hs : ¬Group.IsSolvable H := by
    intro hs
    let := hs
    exact (Nat.not_le_of_gt hn) generationParameter_le_one_of_solvable
  obtain ⟨K,hK,hqs,hgen,_⟩ := Structure.source_original_component hH T hP hs
  by_cases hnorm : K.Normal
  · let := hnorm
    exact Or.inr (source_normal_intrinsic_escape ChapterA.Section02.theoremA_knownSimple
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hH T hP hs hn K hK hqs hgen)
  · rcases source_exchanged_intrinsic_escape_or_odd hH T hP hs K hK hqs hgen hnorm with ho|hg
    · exact Or.inl ⟨K,hK,hqs,hgen,hnorm,ho⟩
    · exact Or.inr hg

variable {G : Type u} [Group G] [Finite G]
theorem source_residual_alternative_or_paired_odd
    {T : Sylow 2 G} {U M V : Subgroup G}
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (hU : U ≠ ⊥) (hUV : U ≤ V)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : (j : ℕ∞) < globalR V)
    (hJ : thompsonJ (M ⊓ centralizer (U : Set G)) j ≤ M ⊓ centralizer (V : Set G))
    (R : Sylow 2 ↥(M ⊓ centralizer (U : Set G)))
    (S : Sylow 2 (centralizer (U : Set G)))
    (hS : (S : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype =
      (R : Subgroup ↥(M ⊓ centralizer (U : Set G))).map (M ⊓ centralizer (U : Set G)).subtype)
    (P : Subgroup (primeToResidual 2 (centralizer (U : Set G))))
    (hP : ChapterB.IsMinimalParabolicOver (residualSylow S) P)
    (hn : j < generationParameter P)
    (hescape : ¬ (P.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
      (centralizer (U : Set G)).subtype ≤ M) :
    (∃ K : Subgroup P, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      K ⊔ (parabolicSylow S P hP : Subgroup P) = ⊤ ∧ ¬K.Normal ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ 7 ≤ p ∧ ClassicalGroup.IsPSL
        (sourceImage (minimalParabolicMax (parabolicSylow S P hP)
          (minimalParabolic_subtype (residualSylow S) P hP)) K) 2 p) ∨
    ∃ f : ℕ, IsEGenerated f P ∧ generationParameter P ≤ f ∧
      ParabolicCartanAlternative V M U
        ((P.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
          (centralizer (U : Set G)).subtype) f := by
  have hn1 : 1 < generationParameter P := lt_of_le_of_lt hj1 hn
  rcases source_intrinsic_escape_or_paired_odd (residual_sqtk h hU hUV P)
    (parabolicSylow S P hP) (minimalParabolic_subtype (residualSylow S) P hP) hn1 with ho|hg
  · exact Or.inl ho
  · obtain ⟨f,hg,hb,d,hN⟩ := hg
    have hM := Overlap.source_residual_maximal_eq_overlap h hU hUV hj1 hj hJ R S hS
      P hP d.maximal_solvable hescape
    have hC : (residualEmbedding U P).range ≤ centralizer (U : Set G) := by
      rintro _ ⟨x,rfl⟩
      exact ((x : primeToResidual 2 (centralizer (U : Set G))) :
        centralizer (U : Set G)).property
    have hR : (R : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
        (M ⊓ centralizer (U : Set G)).subtype =
        (parabolicSylow S P hP : Subgroup P).map (residualEmbedding U P) := by
      rw [parabolicSylow_image]
      exact hS.symm
    have hout := alternative_of_intrinsic_escape d hN (residualEmbedding U P)
      (residualEmbedding_injective U P) M U V hC hM R hR
    rw [residualEmbedding_range] at hout
    exact Or.inr ⟨f,hg,hb,hout⟩

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted
