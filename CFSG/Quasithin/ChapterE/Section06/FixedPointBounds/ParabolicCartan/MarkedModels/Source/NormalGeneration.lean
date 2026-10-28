module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NormalComplete
public import CFSG.Quasithin.ChapterE.Section05.SourceGeneration
/-!
# Attainment on original normal-component minimal parabolics

Every genuine normal-component source family supplies positive
E-generation on the original H through its full solvable core. This
includes the odd and binary derived symplectic families at index one.
No hypothesis n(H)>1 or equality across the quotient is used.

Odd-order solvability makes H even; the proved minimum specification then
gives positive attained n(H). The final application supplies the complete
E.5.2 higher-Thompson generation conclusion at each j≥n(H), with the
original carrier and Sylow. Minimality is retained: this does not claim
attainment for arbitrary overgroups or the general E.1.11 theorem.
Source: Aschbacher–Smith E.1.6, E.2.2 and E.5.2, pp.211,215–216,243.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}
theorem source_normal_generation_exists
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremC κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    ∃ f : ℕ, 0 < f ∧ IsEGenerated f H := by
  rcases source_normal_geometric_cases hA hC hH T hP hs K hK hgen with h2|h3|hb|hl|hsp|hbi
  · exact ⟨1,by decide,single_odd_linear_isEGenerated hA hH T hP hs K hK hgen h2⟩
  · obtain ⟨p,hp,ho,_,huni|hlin⟩ := h3
    · exact ⟨1,by decide,normal_odd_three_isEGenerated hA hH T hP hs K hK hgen hp ho (.inr huni.2)⟩
    · obtain ⟨_,F,hF,hfin,hcard,e,_⟩ := hlin
      exact ⟨1,by decide,normal_odd_three_isEGenerated hA hH T hP hs K hK hgen hp ho
        (.inl ⟨F,hF,hfin,hcard,⟨e⟩⟩)⟩
  · cases hb with
    | linear f hf hm => exact ⟨f,by omega,
        normal_classical_isEGenerated hA hH T hP hs K hK hgen (.inl ⟨hf,hm⟩)⟩
    | unitary f hf hm => exact ⟨f,by omega,
        normal_classical_isEGenerated hA hH T hP hs K hK hgen (.inr (.inl ⟨hf,hm⟩))⟩
    | suzuki m hm he => exact ⟨2*m+1,by omega,
        (normal_suzuki_generation T hP hs K hK hgen (by omega) he).1⟩
  · obtain ⟨f,hf,hm⟩ := hl
    exact ⟨f,by omega,normal_classical_isEGenerated hA hH T hP hs K hK hgen (.inr (.inr ⟨hf,hm⟩))⟩
  · obtain ⟨f,hf,hm⟩ := hsp
    exact ⟨f,by omega,normal_symplectic_isEGenerated hA hH T hP hs K hK hgen hf hm⟩
  · exact ⟨1,by decide,normal_binary_six_isEGenerated T hP hs K hK hgen hbi⟩

theorem source_normal_generation_spec
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremC κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    0 < generationParameter H ∧ IsEGenerated (generationParameter H) H :=
  generationParameter_spec (fun ho => hs (odd_order_theorem H ho))
    (source_normal_generation_exists hA hC hH T hP hs K hK hgen)

theorem source_normal_isEGenerated_of_parameter_le
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremC κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {j : ℕ} (hj : generationParameter H ≤ j) :
    IsEGenerated j H :=
  (source_normal_generation_spec hA hC hH T hP hs K hK hgen).2.mono hj
/-- The actual original normal-component carrier satisfies the complete
higher-Thompson centralizer generation theorem at every j≥n(H). -/
theorem source_normal_thompson_generators
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremC κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (S : Sylow 2 H) (i j : ℕ)
    (hj : generationParameter H ≤ j) :
    thompsonCentralizerGenerators (S : Subgroup H) i j = ⊤ :=
  source_E_5_2_of_positive_parameter S i j
    (source_normal_generation_spec hA hC hH T hP hs K hK hgen).1 hj

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
