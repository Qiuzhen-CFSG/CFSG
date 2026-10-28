module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NumericalClassical.Generation
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NormalClauses
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.Bender
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.LinearThree
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.ParameterBound
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Transport
/-!
# Source-correct classical Cartan witnesses for the original group

The genuine normal PSL2, PSU3 and PSL3 source families give actual
E-generation and n(H) bounded by their field exponent. The same original
component has its proved structural and Borel or diagram marking. These
produce the complete Hall–Cartan witness at that exponent, and the final
application retains the actual residual embedding and prescribed Sylow.
No equality between the original and quotient generation parameters is
used. The original overlap placement is retained for its source owner.

Source: Aschbacher–Smith E.2.2 and E.6.27, printed pp.215–216,257.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
universe u
variable {H:Type u} [Group H] [Finite H] {κ:GroupClass.{u}}
theorem normal_classical_intrinsic
    (hA:ChapterA.Section02.TheoremA κ H) (hH:IsSQTK κ H)
    (T:Sylow 2 H) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (hs:¬Group.IsSolvable H) (hn:1<generationParameter H)
    (K:Subgroup H) (hK:K.IsCComponent) [K.Normal]
    (hqs:IsQuasisimple (K⧸pCore 2 K)) (hgen:K⊔(T:Subgroup H)=⊤) {f:ℕ}
    (hm:
      (2≤f ∧ ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 2 (2^f)) ∨
      (2≤f ∧ ClassicalGroup.IsPSU (sourceImage (ChapterB.minimalParabolicMax T hP) K) 3 (2^f)) ∨
      (0<f ∧ ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 3 (2^f))) :
    IsEGenerated f H ∧ generationParameter H≤f ∧ Nonempty (IntrinsicHallCartanData T hP f) := by
  have hupper:=normal_classical_parameter_le hA hH T hP hs K hK hgen hm
  have hgenf:=normal_classical_isEGenerated hA hH T hP hs K hK hgen hm
  have hc:=source_single_clauses T hP hs K hK hqs hgen
  refine ⟨hgenf,hupper,?_⟩
  rcases hm with ⟨hf,hm⟩|⟨hf,hm⟩|⟨hf,hm⟩
  · exact bender_intrinsic_at T hP (by omega) hK hc
      (Or.inl (source_linear_borel_model T hP hs K hK hgen hf hm))
  · exact bender_intrinsic_at T hP (by omega) hK hc
      (Or.inr (source_unitary_borel_model T hP hs K hK hgen hf hm))
  · exact diagram_intrinsic_at T hP (hn.trans_le hupper) hK hc
      (source_binary_linear_three_model T hP hs K hK hgen hf hm)

/-- The original E.6.27 residual parabolic receives the same complete witness
at the actual classical field exponent, together with its numerical bound. -/
theorem residual_normal_classical_cartan {G:Type u} [Group G] [Finite G]
    {U M:Subgroup G} (S:Sylow 2 (centralizer (U:Set G)))
    (P:Subgroup (primeToResidual 2 (centralizer (U:Set G))))
    (hP:ChapterB.IsMinimalParabolicOver (residualSylow S) P)
    (hA:ChapterA.Section02.TheoremA κ P) (hG:IsSQTK κ P)
    (hs:¬Group.IsSolvable P) (hn:1<generationParameter P)
    (K:Subgroup P) (hK:K.IsCComponent) [K.Normal]
    (hqs:IsQuasisimple (K⧸pCore 2 K))
    (hgen:K⊔(parabolicSylow S P hP:Subgroup P)=⊤) {f:ℕ}
    (hm:
      (2≤f ∧ ClassicalGroup.IsPSL (sourceImage
        (ChapterB.minimalParabolicMax (parabolicSylow S P hP)
          (minimalParabolic_subtype (residualSylow S) P hP)) K) 2 (2^f)) ∨
      (2≤f ∧ ClassicalGroup.IsPSU (sourceImage
        (ChapterB.minimalParabolicMax (parabolicSylow S P hP)
          (minimalParabolic_subtype (residualSylow S) P hP)) K) 3 (2^f)) ∨
      (0<f ∧ ClassicalGroup.IsPSL (sourceImage
        (ChapterB.minimalParabolicMax (parabolicSylow S P hP)
          (minimalParabolic_subtype (residualSylow S) P hP)) K) 3 (2^f)))
    (hM:ChapterB.minimalParabolicMax (parabolicSylow S P hP)
      (minimalParabolic_subtype (residualSylow S) P hP)=M.comap (residualEmbedding U P))
    (R:Sylow 2 ↥(M⊓centralizer (U:Set G)))
    (hR:(R:Subgroup ↥(M⊓centralizer (U:Set G))).map (M⊓centralizer (U:Set G)).subtype=
      (S:Subgroup (centralizer (U:Set G))).map (centralizer (U:Set G)).subtype) :
    IsEGenerated f P ∧ generationParameter P≤f ∧
      Nonempty (HallCartanData (residualEmbedding U P) M U (parabolicSylow S P hP) f) := by
  obtain ⟨hg,hb,⟨d⟩⟩:=normal_classical_intrinsic hA hG (parabolicSylow S P hP)
    (minimalParabolic_subtype (residualSylow S) P hP) hs hn K hK hqs hgen hm
  exact ⟨hg,hb,⟨transportResidual S P hP f d M hM R hR⟩⟩

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
