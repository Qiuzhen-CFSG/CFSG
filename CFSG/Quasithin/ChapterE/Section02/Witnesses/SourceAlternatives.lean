module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.Source
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedBender.Original
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.OddLinearTwo.Original
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.OddDegreeThree.Original
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.LinearThree.Original
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.OddFamilies
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# Original witness construction outside the symplectic families

The actual source component catalogue selects the original normal or
exchanged component. Solvable and odd rows give a lifted dihedral pair;
normal Bender, exchanged, and binary PSL₃ rows supply their marked SL₂ or
Suzuki pairs. The odd PSL₃ row uses TI before quotienting, including p=3.
Every witness retains V, an internal conjugator, the prescribed Sylow and
two-closed relative core. Only the two original normal symplectic model
families remain, with their exact original quotient map.
Source: Aschbacher–Smith E.2.2, E.2.7–9 and E.2.15, pp.215–222,228.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Witnesses
open Section06.FixedPointBounds.ParabolicCartan.MarkedModels BenderPlacement
universe u
variable {H : Type u} [Group H] [Finite H]
theorem source_original_witness_or_symplectic
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬V ≤ ChapterB.minimalParabolicCore T hP)
    (hTI : ∀g∈ChapterB.minimalParabolicMax T hP,
      V⊓V.map (MulAut.conj g).toMonoidHom=⊥ ∨ V.map (MulAut.conj g).toMonoidHom=V) :
    (∃n:ℕ,Nonempty (OriginalWitness T (ChapterB.minimalParabolicMax T hP) V n)) ∨
    ∃K:Subgroup H,K.IsCComponent ∧ K.Normal ∧ K⊔(T:Subgroup H)=⊤ ∧
      ((∃f:ℕ,2≤f ∧ ClassicalGroup.IsPSp
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
        obtain ⟨w⟩ := OddDegreeThree.linear_source_original_of_ti T hP hs K hK hgen hp ho
          ⟨F,hF,hfin,hcard,⟨e⟩⟩ V hVT hvn hVM hout hTI
        exact Or.inl ⟨1,⟨OriginalWitness.of_dihedral w⟩⟩
    · obtain ⟨n,_,w⟩ := source_of_normal_supplement T hP V hVT hvn hVM hout K hgen hb
      exact Or.inl ⟨n,w⟩
    · obtain ⟨n,hn,hm⟩ := hl
      exact Or.inl ⟨n,LinearThree.source_original T hP hs K hK hgen (by omega) hm V hVT hvn hVM hout⟩
    · exact Or.inr ⟨K,hK,hnorm,hgen,Or.inl hsp⟩
    · exact Or.inr ⟨K,hK,hnorm,hgen,Or.inr hbi⟩
  · obtain ⟨n,_,w⟩ := PairedBender.original_source ChapterA.Section02.theoremA_knownSimple
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hH T hP hs K hK hgen hnorm
      V hVT hvn hVM hout
    exact Or.inl ⟨n,w⟩
end CFSG.Quasithin.ChapterE.Witnesses
