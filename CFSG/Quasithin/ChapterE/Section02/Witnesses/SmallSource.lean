module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SmallNonsolvableModels
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedOddLinearTwo.SevenExclusion
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.OddDegreeThree.TernaryExclusion
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.SmallNormalSource
/-!
# Original E.2.17 small-automizer source theorem

The original component catalogue reduces the nonsolvable case to a normal
PSL₃(3) component or exchanged PSL₂(7) components. The proved source exclusions
eliminate both cases using the same selected V, Sylow subgroup and action.
The resulting solvability supplies the normal quaternion core constructed by
the solvable source theorem. No component model or local placement hypothesis
is added to the original source data.

Source: Aschbacher–Smith E.2.17, printed pp.229–230.
-/
public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses
universe u v
variable {H : Type u} {D : Type v} [Group H] [Finite H] [Group D] [Finite D] {κ : GroupClass.{u}}
/-- The original small automizer forces the minimal parabolic to be solvable. -/
theorem source_small_solvable
    (hA : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremA κ G)
    (hC : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremC κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
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
    Group.IsSolvable H := by
  by_contra hs
  obtain ⟨K,hK,hqK,hgen,hcases⟩ := source_small_nonsolvable_component_cases (hA H) hC hH
    T hP hs V hVT hvn hcore hout hfit hV U hTU hU f hf hk hD hratio hres
  rcases hcases with ⟨hn,hm⟩ | ⟨hn,hm⟩
  · let := hn
    exact OddDegreeThree.source_ternary_small_automizer_false hH T hP hs
      K hK hqK hgen hm V hVT hvn hcore hout hfit hV U hTU hU f hf hk hD hratio hres
  · exact PairedOddLinearTwo.source_seven_small_automizer_false hA hH T hP hs
      K hK hqK hgen hn hm V hVT hvn hcore hout hfit hV U hTU hU f hf hk hD hratio hres

/-- The original small action supplies the ambient normal quaternion core. -/
theorem BenderPlacement.source_small_normal_core
    (hA : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremA κ G)
    (hC : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremC κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
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
    ∃ P : Subgroup H, P.Normal ∧ P ≤ (T : Subgroup H) ∧
      Nonempty (QuaternionCentralProductData P) ∧
      U = P ⊔ (U ⊓ centralizer (V : Set H)) ∧
      P ⊓ centralizer (V : Set H) = P ⊓ V ∧
      ⁅U ⊓ centralizer (V : Set H),P⁆ ≤ P ⊓ V := by
  have hs := source_small_solvable hA hC hH T hP V hVT hvn hcore hout hfit hV
    U hTU hU f hf hk hD hratio hres
  exact BenderPlacement.source_solvable_small_normal_core hH T hP hs hVT hvn hcore hout
    hfit hV hTU hU f hf hk hD hratio hres

end CFSG.Quasithin.ChapterE.Witnesses
