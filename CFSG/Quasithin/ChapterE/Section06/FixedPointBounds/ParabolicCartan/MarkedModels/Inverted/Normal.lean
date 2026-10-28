module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted.Intrinsic
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted.Transport
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NormalE626
/-!
# Original normal-component Cartan alternative without callbacks

The complete original component catalogue excludes its odd and binary-small
rows by their proved generation bounds. Every remaining binary model gives
its actual exponent and a reflected Hall–Cartan witness. E.6.26 supplies the
literal ambient maximal marking; cyclic faithfulness or its escaping odd
normalizer then gives the full E.6.27 alternative. No E.6.26, 4.4.13, model,
or numerical equality premise remains.
Source: Aschbacher–Smith E.2.2 and E.6.26–27, pp.215–216,256–257.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted
open ChapterB
universe u
variable {H:Type u} [Group H] [Finite H] {κ:GroupClass.{u}}
theorem source_normal_intrinsic_escape
    (hA:ChapterA.Section02.TheoremA κ H)
    (hC:∀(G:Type u) [Group G] [Finite G],ChapterA.Section02.TheoremC κ G)
    (hH:IsSQTK κ H) (T:Sylow 2 H) (hP:IsMinimalParabolicOver T ⊤)
    (hs:¬Group.IsSolvable H) (hn:1<generationParameter H)
    (K:Subgroup H) (hK:K.IsCComponent) [K.Normal]
    (hqs:IsQuasisimple (K⧸pCore 2 K)) (hgen:K⊔(T:Subgroup H)=⊤) :
    ∃ f:ℕ, IsEGenerated f H ∧ generationParameter H≤f ∧
      ∃ d : IntrinsicHallCartanData T hP f,
        ∀ (p : ℕ) (_ : Fact p.Prime) (A : Subgroup H), Odd p → A ≤ d.witness.cyclicGroup →
          IsPGroup p A → ¬ normalizer (A : Set H) ≤ minimalParabolicMax T hP := by
  have hc := source_single_clauses T hP hs K hK hqs hgen
  rcases source_normal_geometric_cases hA hC hH T hP hs K hK hgen with h2|h3|hb|hl|hsp|hbi
  · exact (single_odd_linear_false_of_parameter_gt_one hA hH T hP hs K hK hgen h2 hn).elim
  · obtain ⟨p,hp,ho,_,huni|hlin⟩:=h3
    · exact (normal_odd_three_false_of_parameter_gt_one hA hH T hP hs K hK hgen hp ho
        (Or.inr huni.2) hn).elim
    · obtain ⟨_,F,hF,hfin,hcard,e,_⟩:=hlin
      exact (normal_odd_three_false_of_parameter_gt_one hA hH T hP hs K hK hgen hp ho
        (Or.inl ⟨F,hF,hfin,hcard,⟨e⟩⟩) hn).elim
  · cases hb with
    | linear f hf hm =>
      have hg := normal_classical_isEGenerated hA hH T hP hs K hK hgen (.inl ⟨hf,hm⟩)
      have hu := normal_classical_parameter_le hA hH T hP hs K hK hgen (.inl ⟨hf,hm⟩)
      exact ⟨f,hg,hu,bender_intrinsic_escape T hP (by omega) hK hc
        (.inl (source_linear_borel_model T hP hs K hK hgen hf hm))⟩
    | unitary f hf hm =>
      have hg := normal_classical_isEGenerated hA hH T hP hs K hK hgen (.inr (.inl ⟨hf,hm⟩))
      have hu := normal_classical_parameter_le hA hH T hP hs K hK hgen (.inr (.inl ⟨hf,hm⟩))
      exact ⟨f,hg,hu,bender_intrinsic_escape T hP (by omega) hK hc
        (.inr (source_unitary_borel_model T hP hs K hK hgen hf hm))⟩
    | suzuki m hm he =>
      obtain ⟨hg,hu⟩ := normal_suzuki_generation T hP hs K hK hgen hm he
      exact ⟨2*m+1,hg,hu,bender_intrinsic_escape T hP (by omega) hK hc
        (.inl (source_suzuki_borel_model T hP hs K hK hgen hm he))⟩
  · obtain ⟨f,hf,hm⟩:=hl
    have hg := normal_classical_isEGenerated hA hH T hP hs K hK hgen (.inr (.inr ⟨hf,hm⟩))
    have hu := normal_classical_parameter_le hA hH T hP hs K hK hgen (.inr (.inr ⟨hf,hm⟩))
    exact ⟨f,hg,hu,diagram_intrinsic_escape T hP (hn.trans_le hu) hK hc
      (source_binary_linear_three_model T hP hs K hK hgen hf hm)⟩
  · obtain ⟨f,hf,hm⟩:=hsp
    exact ⟨f,normal_symplectic_isEGenerated hA hH T hP hs K hK hgen hf hm,
      normal_symplectic_parameter_le hA hH T hP hs K hK hgen hf hm,
      diagram_intrinsic_escape T hP hf hK hc
        (source_binary_symplectic_model T hP hs K hK hgen hf hm)⟩
  · exact ((Nat.not_le_of_gt hn) (normal_binary_six_parameter_le T hP hs K hK hgen hbi)).elim

variable {G : Type u} [Group G] [Finite G]
theorem source_normal_residual_alternative
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
    (K : Subgroup P) (hK : K.IsCComponent) [K.Normal]
    (hqs : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (parabolicSylow S P hP : Subgroup P) = ⊤)
    (hescape : ¬ (P.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
      (centralizer (U : Set G)).subtype ≤ M) :
    ∃ f : ℕ, IsEGenerated f P ∧ generationParameter P ≤ f ∧
      ParabolicCartanAlternative V M U
        ((P.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
          (centralizer (U : Set G)).subtype) f := by
  have hn1 : 1 < generationParameter P := lt_of_le_of_lt hj1 hn
  have hs : ¬ Group.IsSolvable P := by
    intro hs
    let := hs
    exact (Nat.not_le_of_gt hn1) generationParameter_le_one_of_solvable
  obtain ⟨f,hg,hb,d,hN⟩ := source_normal_intrinsic_escape
    ChapterA.Section02.theoremA_knownSimple (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    (residual_sqtk h hU hUV P) (parabolicSylow S P hP)
    (minimalParabolic_subtype (residualSylow S) P hP) hs hn1 K hK hqs hgen
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
  exact ⟨f,hg,hb,hout⟩

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted
