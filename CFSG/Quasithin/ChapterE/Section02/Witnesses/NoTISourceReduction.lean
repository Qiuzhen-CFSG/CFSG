module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SourceAlternatives
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.Binary.WeakSource
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.WeakAction
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedBender.Original
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.OddLinearTwo.Original
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.OddDegreeThree.Original
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.LinearThree.Original
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.OddFamilies
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# The no-TI source reduction for the outside-core cubic bound

The source component catalogue and the existing original witness constructions
handle every row except odd PSL3 and symplectic four. This reduction does not
replace normality under the Sylow subgroup by normality under its maximal
overgroup, and does not impose TI. It retains the original component, maximal
core, quotient map and module, so the remaining geometric estimates can be
applied directly to the original E.2.13 action.

Source: Aschbacher--Smith E.2.8--13, printed pp.222--225, used in 3.1.6,
printed pp.573--574.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Witnesses
open Section06.FixedPointBounds.ParabolicCartan.MarkedModels BenderPlacement
universe u
variable {H : Type u} [Group H] [Finite H]
theorem source_original_witness_or_oddLinearThree_or_symplectic
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬V ≤ ChapterB.minimalParabolicCore T hP) :
    (∃n:ℕ,Nonempty (OriginalWitness T (ChapterB.minimalParabolicMax T hP) V n)) ∨
    ∃K:Subgroup H,K.IsCComponent ∧ K.Normal ∧ K⊔(T:Subgroup H)=⊤ ∧
      ((∃p:ℕ,p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL
        (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 p) ∨
       (∃f:ℕ,2≤f ∧ ClassicalGroup.IsPSp
        (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 (2^f)) ∨
        Nonempty ((K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) ≃*
          commutator (ClassicalGroup.PSp 2 (ZMod 2)))) := by
  by_cases hs : Group.IsSolvable H
  · obtain ⟨w⟩ := Solvable.solvable_witness T hP hs V hVT hvn hVM hout
    exact Or.inl ⟨1,⟨OriginalWitness.of_dihedral w⟩⟩
  obtain ⟨K,hK,hqs,hgen,_⟩ := Structure.source_original_component hH T hP hs
  by_cases hnorm : K.Normal
  · let := hnorm
    rcases source_normal_geometric_cases ChapterA.Section02.theoremA_knownSimple
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hH T hP hs K hK hgen with
      h2|h3|hb|hl|hsp|hbi
    · obtain ⟨p,d,hp,hp3,hd,hd2,hmod,F,hF,hfin,hcard,e,_⟩ := h2
      have ho : Odd p := hp.odd_of_ne_two (by omega)
      have hlarge : 5<p^d := by
        rcases (show d=1 ∨ d=2 by omega) with hd|hd
        · subst d; simp only [pow_one] at hmod ⊢; omega
        · subst d; nlinarith
      have hnine : p^d≠9 := by
        intro he
        rcases (show d=1 ∨ d=2 by omega) with hd|hd
        · subst d
          simp only [pow_one] at he
          rw [he] at hp
          norm_num at hp
        · subst d
          nlinarith
      obtain ⟨w⟩ := OddLinearTwo.source_original ChapterA.Section02.theoremA_knownSimple
        hH T hP hs K hK hgen hp ho hlarge hnine ⟨F,hF,hfin,hcard,⟨e⟩⟩ V hVT hvn hVM hout
      exact Or.inl ⟨1,⟨OriginalWitness.of_dihedral w⟩⟩
    · obtain ⟨p,hp,ho,_,huni|hlin⟩ := h3
      · obtain ⟨w⟩ := OddDegreeThree.unitary_source_original T hP hs K hK hgen hp ho
          huni.2 V hVT hvn hVM hout
        exact Or.inl ⟨1,⟨OriginalWitness.of_dihedral w⟩⟩
      · obtain ⟨_,F,hF,hfin,hcard,e,_⟩ := hlin
        exact Or.inr ⟨K,hK,hnorm,hgen,Or.inl ⟨p,hp,ho,F,hF,hfin,hcard,⟨e⟩⟩⟩
    · obtain ⟨n,_,w⟩ := source_of_normal_supplement T hP V hVT hvn hVM hout K hgen hb
      exact Or.inl ⟨n,w⟩
    · obtain ⟨n,hn,hm⟩ := hl
      exact Or.inl ⟨n,LinearThree.source_original T hP hs K hK hgen (by omega) hm V hVT hvn hVM hout⟩
    · exact Or.inr ⟨K,hK,hnorm,hgen,Or.inr (Or.inl hsp)⟩
    · exact Or.inr ⟨K,hK,hnorm,hgen,Or.inr (Or.inr hbi)⟩
  · obtain ⟨n,_,w⟩ := PairedBender.original_source ChapterA.Section02.theoremA_knownSimple
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hH T hP hs K hK hgen hnorm
      V hVT hvn hVM hout
    exact Or.inl ⟨n,w⟩

open Representation.BinaryOffender
open scoped IsMulCommutative

/-- All rows already carrying an original pair give the required weak estimate,
with no TI condition on the module. The two remaining families retain their
literal quotient rather than an unmarked abstract model. -/
theorem source_cubicRatio_le_two_or_oddLinearThree_or_nonbinary_symplectic
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (V U : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H)
    (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H)) :
    cubicRatio (DihedralCubic.canonicalAction U V hU) ≤ 2 ∨
    ∃ K : Subgroup H, K.IsCComponent ∧ K.Normal ∧ K ⊔ (T : Subgroup H) = ⊤ ∧
      ((∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL
        (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 p) ∨
       (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSp
        (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 (2^f))) := by
  rcases source_original_witness_or_oddLinearThree_or_symplectic hH T hP V hVT hvn hVM hout with
    ⟨n,⟨w⟩⟩ | hmodels
  · exact Or.inl (original_witness_cubicRatio_le_two hP hVT hvn hVM hout hfit w hTU hU)
  · obtain ⟨K,hK,hN,hgen,hm⟩ := hmodels
    rcases hm with hl | hsp | ⟨e⟩
    · exact Or.inr ⟨K,hK,hN,hgen,Or.inl hl⟩
    · exact Or.inr ⟨K,hK,hN,hgen,Or.inr hsp⟩
    · obtain ⟨e⟩ := e
      let := hN
      have hs : ¬ Group.IsSolvable H := by
        intro h
        let := h
        exact hK.not_isSolvable
          (Group.isSolvable_of_isSolvable_injective (f := K.subtype) K.subtype_injective)
      exact Or.inl (SymplecticFour.Binary.source_cubicRatio_le_two
        T hP hs K hK hgen e V hVT hvn hVM hout hfit U hTU hU)

end CFSG.Quasithin.ChapterE.Witnesses
