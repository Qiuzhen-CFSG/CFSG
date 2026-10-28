module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NormalAdequate
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NumericalOddTwo
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.UpperBound
/-!
# Complete normal-component Cartan bounds for E.6.27

The genuine normal-component source catalogue now has all its generation
bounds discharged. Odd-characteristic rows and the binary derived symplectic
row have generation parameter at most one. Each remaining characteristic-two
row supplies actual E-generation and a Hall–Cartan witness at its field
exponent, bounding the original group's parameter from above.

The residual-parabolic applications retain the original embedding, Sylow and
maximal-overgroup marking. The last theorem applies the actual 4.4.13 source
implication to give the alternative used by E.6.27. No equality of generation
parameters across a solvable kernel is asserted.

Source: Aschbacher–Smith E.2.2 and E.6.27, printed pp.215–216,257.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
universe u
variable {H:Type u} [Group H] [Finite H] {κ:GroupClass.{u}}
theorem source_normal_intrinsic_cartan
    (hA:ChapterA.Section02.TheoremA κ H)
    (hC:∀(G:Type u) [Group G] [Finite G],ChapterA.Section02.TheoremC κ G)
    (hH:IsSQTK κ H) (T:Sylow 2 H) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (hs:¬Group.IsSolvable H) (hn:1<generationParameter H)
    (K:Subgroup H) (hK:K.IsCComponent) [K.Normal]
    (hqs:IsQuasisimple (K⧸pCore 2 K)) (hgen:K⊔(T:Subgroup H)=⊤) :
    ∃f:ℕ,IsEGenerated f H ∧ generationParameter H≤f ∧ Nonempty (IntrinsicHallCartanData T hP f) := by
  rcases normal_cyclic_cartan_or_odd_two hA hC hH T hP hs hn K hK hqs hgen with ho|hc
  · exact (single_odd_linear_false_of_parameter_gt_one hA hH T hP hs K hK hgen ho hn).elim
  · exact hc

theorem residual_normal_cartan {G:Type u} [Group G] [Finite G]
    {U M:Subgroup G} (S:Sylow 2 (centralizer (U:Set G)))
    (P:Subgroup (primeToResidual 2 (centralizer (U:Set G))))
    (hP:ChapterB.IsMinimalParabolicOver (residualSylow S) P)
    (hA:ChapterA.Section02.TheoremA κ P)
    (hC:∀(X:Type u) [Group X] [Finite X],ChapterA.Section02.TheoremC κ X)
    (hG:IsSQTK κ P) (hs:¬Group.IsSolvable P) (hn:1<generationParameter P)
    (K:Subgroup P) (hK:K.IsCComponent) [K.Normal]
    (hqs:IsQuasisimple (K⧸pCore 2 K))
    (hgen:K⊔(parabolicSylow S P hP:Subgroup P)=⊤)
    (hM:ChapterB.minimalParabolicMax (parabolicSylow S P hP)
      (minimalParabolic_subtype (residualSylow S) P hP)=M.comap (residualEmbedding U P))
    (R:Sylow 2 ↥(M⊓centralizer (U:Set G)))
    (hR:(R:Subgroup ↥(M⊓centralizer (U:Set G))).map (M⊓centralizer (U:Set G)).subtype=
      (S:Subgroup (centralizer (U:Set G))).map (centralizer (U:Set G)).subtype) :
    ∃f:ℕ,IsEGenerated f P ∧ generationParameter P≤f ∧
      Nonempty (HallCartanData (residualEmbedding U P) M U (parabolicSylow S P hP) f) := by
  obtain ⟨f,hg,hb,⟨d⟩⟩:=source_normal_intrinsic_cartan hA hC hG (parabolicSylow S P hP)
    (minimalParabolic_subtype (residualSylow S) P hP) hs hn K hK hqs hgen
  exact ⟨f,hg,hb,⟨transportResidual S P hP f d M hM R hR⟩⟩
/-- The complete normal-component branch of the original large-parabolic
Cartan alternative, with all model, generation and Hall inputs discharged. -/
theorem residual_normal_alternative {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {U M V : Subgroup G}
    (h : HypothesisE61 κ T M V) (hU : U ≠ ⊥) (hUV : U ≤ V)
    (earlier : Source4413One κ G)
    (S : Sylow 2 (centralizer (U : Set G)))
    (P : Subgroup (primeToResidual 2 (centralizer (U : Set G))))
    (hP : ChapterB.IsMinimalParabolicOver (residualSylow S) P)
    (hA : ChapterA.Section02.TheoremA κ P)
    (hC : ∀ (X : Type u) [Group X] [Finite X], ChapterA.Section02.TheoremC κ X)
    (hG : IsSQTK κ P) (hs : ¬Group.IsSolvable P) (hn : 1 < generationParameter P)
    (K : Subgroup P) (hK : K.IsCComponent) [K.Normal]
    (hqs : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (parabolicSylow S P hP : Subgroup P) = ⊤)
    (hM : ChapterB.minimalParabolicMax (parabolicSylow S P hP)
      (minimalParabolic_subtype (residualSylow S) P hP) = M.comap (residualEmbedding U P))
    (R : Sylow 2 ↥(M ⊓ centralizer (U : Set G)))
    (hR : (R : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
      (M ⊓ centralizer (U : Set G)).subtype =
      (S : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype)
    (hescape : ¬ (P.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
      (centralizer (U : Set G)).subtype ≤ M) :
    ∃ f : ℕ, IsEGenerated f P ∧ generationParameter P ≤ f ∧
      ParabolicCartanAlternative V M U
        ((P.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
          (centralizer (U : Set G)).subtype) f := by
  obtain ⟨f, hg, hb, ⟨d⟩⟩ := residual_normal_cartan S P hP hA hC hG hs hn
    K hK hqs hgen hM R hR
  exact ⟨f, hg, hb, residual_alternative_of_hall_data_at h hU hUV earlier P
    (parabolicSylow S P hP) (minimalParabolic_subtype (residualSylow S) P hP)
    (residual_twoCore_ne_bot h hU hUV S P hP) hn hM hescape d⟩

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
