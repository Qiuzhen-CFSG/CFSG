module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.OddFamilies
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.PairedMarked
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.ResidualComponentBender
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.ResidualSymplectic
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.LinearThree.BinarySmallExclusion
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.Binary.SmallExclusion
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.OddLinearTwo.SmallExclusion
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.OddDegreeThree.SmallExclusion
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedOddLinearTwo.SmallParameter
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The two remaining small-automizer component models

Apply the actual E.2.2 component catalogue to the original minimal
parabolic. The small conjugation action and residual-centralization
hypotheses exclude the Bender, even linear-three, symplectic, and normal
odd linear-two rows. Odd degree three reduces to PSL₃(3), and the exchanged
odd row reduces to PSL₂(7). The original component, quotient map, and
normality alternative are retained for the geometric subgroup reductions.

These are the last two cases before the solvable H₀ reduction in
Aschbacher–Smith E.2.17, printed pp.229–230.
-/
public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses
open Section06.FixedPointBounds.ParabolicCartan.MarkedModels
universe u v
variable {H : Type u} {D : Type v} [Group H] [Finite H] [Group D] [Finite D] {κ : GroupClass.{u}}

private theorem source_normal_small_rank_three
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremC κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H) (hV : Nat.card V = 16)
    (U : Subgroup H) (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (f : U →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (V : Set H)).subgroupOf U) (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U V hU f hf hk))
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H)) :
    SingleOddRankThreeModel (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H) := by
  rcases source_normal_geometric_cases hA hC hH T hP hs K hK hgen with h2|h3|hb|hl|hsp|hbi
  · exact (OddLinearTwo.source_odd_linear_small_automizer_false T hP hs K hK hgen h2
      V hVT hvn hcore hout hfit hV U hTU hU f hf hk hD hratio hres).elim
  · exact h3
  · exact (PairedBender.source_original_component_bender_residual_exclusion hA hH T hP hs K hK
      hgen hb V hVT hvn hout hres).elim
  · obtain ⟨n,hn,hm⟩ := hl
    exact (LinearThree.source_linear_three_small_automizer_false T hP hs K hK hgen
      (by omega) hm V hVT hvn hcore hout hfit hV U hTU hU f hf hk hD hratio hres).elim
  · obtain ⟨n,hn,hm⟩ := hsp
    exact (source_not_nonbinary_symplectic_of_residual_centralizes T hP hs K hK hgen
      (by omega) hm V hVT hvn hout hres).elim
  · exact (SymplecticFour.Binary.source_binary_symplectic_small_automizer_false T hP hs K hK
      hgen hbi V hVT hvn hcore hout hfit hV U hTU hU f hf hk hD hratio hres).elim

/-- The original normal component has star image PSL₃(3). -/
theorem source_normal_small_linear_three
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremC κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H) (hV : Nat.card V = 16)
    (U : Subgroup H) (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (f : U →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (V : Set H)).subgroupOf U) (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U V hU f hf hk))
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H)) :
    ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 3 := by
  obtain ⟨p,hp,ho,_,hu|hl⟩ := source_normal_small_rank_three hA hC hH T hP hs K hK hgen
    V hVT hvn hcore hout hfit hV U hTU hU f hf hk hD hratio hres
  · exact (OddDegreeThree.unitary_source_small_false T hP hs K hK hgen hp ho hu.2
      V hVT hvn hcore hout hfit hV U hTU hU f hf hk hD hratio hres).elim
  · obtain ⟨_,F,hF,hfin,hsize,e,_⟩ := hl
    have hm : ClassicalGroup.IsPSL
        (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 p :=
      ⟨F,hF,hfin,hsize,⟨e⟩⟩
    have he := OddDegreeThree.linear_source_prime_eq_three T hP hs K hK hgen hp ho hm
      V hVT hvn hcore hout hfit hV U hTU hU f hf hk hD hratio hres
    exact he ▸ hm

private theorem source_exchanged_small_odd_model
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremC κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬K.Normal)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hout : ¬V ≤ ChapterB.minimalParabolicCore T hP)
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ 7 ≤ p ∧
      ClassicalGroup.IsPSL (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 p := by
  rcases source_exchanged_marked_cases hA hC hH T hP hs K hK hgen hn with ⟨n,_,hm⟩ | hm
  · have hb : ClassificationModels.IsBenderModel
        (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) := by
      rcases hm with ⟨F,hF,hfin,hchar,hn,hcard,e,_⟩ | ⟨m,hm,_,e,_⟩
      · exact .linear n hn ⟨F,hF,hfin,hcard,⟨e⟩⟩
      · exact .suzuki m hm ⟨e⟩
    exact (PairedBender.source_original_component_bender_residual_exclusion hA hH T hP hs K hK
      hgen hb V hVT hvn hout hres).elim
  · exact hm

/-- Select an original component and isolate exactly the two geometric
source cases still requiring a local subgroup reduction. -/
theorem source_small_nonsolvable_component_cases
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremC κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H) (hV : Nat.card V = 16)
    (U : Subgroup H) (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (f : U →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (V : Set H)).subgroupOf U) (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U V hU f hf hk))
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H)) :
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      K ⊔ (T : Subgroup H) = ⊤ ∧
      ((K.Normal ∧ ClassicalGroup.IsPSL
         (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 3) ∨
       (¬K.Normal ∧ ClassicalGroup.IsPSL
         (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 7)) := by
  obtain ⟨K,hK,hqs,hgen,_⟩ := Structure.source_original_component hH T hP hs
  refine ⟨K,hK,hqs,hgen,?_⟩
  by_cases hn : K.Normal
  · let := hn
    exact Or.inl ⟨hn,source_normal_small_linear_three hA hC hH T hP hs K hK hgen
      V hVT hvn hcore hout hfit hV U hTU hU f hf hk hD hratio hres⟩
  · obtain ⟨p,hp,ho,hseven,hm⟩ := source_exchanged_small_odd_model hA hC hH T hP hs K hK hgen hn
      V hVT hvn hout hres
    have he := PairedOddLinearTwo.source_small_parameter_eq_seven_of_seven_le hA hH
      T hP hs K hK hgen hn hp ho hseven hm
      V hVT hvn hcore hout hfit hV U hTU hU f hf hk hD hratio
    exact Or.inr ⟨hn,he ▸ hm⟩

end CFSG.Quasithin.ChapterE.Witnesses
