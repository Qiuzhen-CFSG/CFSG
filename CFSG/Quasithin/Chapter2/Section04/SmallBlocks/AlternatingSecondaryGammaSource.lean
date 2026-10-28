module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSelectedCentralizerSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondaryNonCharacteristicSource
/-!
# The original secondary Gamma packet

The retained affine pair involution has centralizer T_u in M and an actual
Sylow subgroup T_u in its ambient centralizer. Its affine centralizer is
not contained in M, giving the required local pair and maximal Gamma
selection. The same marks exclude characteristic two. Every hypothesis
is from the original single alternating-five branch of Section 2.4.

Source: Aschbacher--Smith, 2.4.29, printed p.545.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_secondary_gamma_packet
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hcounter : ¬IsTheorem241Model G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD : (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G) = ⊥) :
    let B := M ⊓ d.block.map d.H.subtype
    let K := (pResidual 2 B).map B.subtype
    let P := K.pCoreIn 2
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let U := ((blockU d.block).map d.block.subtype).map d.H.subtype
    let J := elementaryAbelianMaxJ R
    let Z := (center P).map P.subtype
    ∃ eH : d.H ≃* BinaryFiveAffine.W,
      ((blockU d.block).map d.block.subtype).map eH.toMonoidHom=BinaryFiveAffine.vectorGroup ∧
      (d.S : Subgroup d.H).map eH.toMonoidHom=(BinaryFiveAffine.standardSylow : Subgroup BinaryFiveAffine.W) ∧
      d.MarkedA5CentralizerPacket eH ∧
      let u : G := (eH.symm BinaryFiveAffine.t : d.H)
      let s : G := (eH.symm BinaryFiveAffine.standardSwap : d.H)
      let z : G := (eH.symm BinaryFiveAffine.standardZ : d.H)
      u∈U ∧ orderOf u=2 ∧ u∈(center J).map J.subtype ∧ u∉Z ∧
      s∈R ∧ s∉J ∧ R ⊓ centralizer ({u}:Set G)=J ∧
      Z=zpowers z ∧ z=u*s*u*s⁻¹ ∧
      (center J).map J.subtype=zpowers u ⊔ zpowers z ∧
      Z≤(center (T:Subgroup G)).map (T:Subgroup G).subtype ∧
      u∈P ∧ Nat.card (center J)=4 ∧ IsElementaryAbelian 2 (center J) ∧
      IsElementaryAbelian 2 (↥(⁅sourceModule (d.block.map d.H.subtype),d.affineCentralizerResidual eH⁆ : Subgroup G)) ∧
      M ⊓ centralizer ({u}:Set G)=(T:Subgroup G) ⊓ centralizer ({u}:Set G) ∧
      ((T:Subgroup G) ⊓ centralizer ({u}:Set G)).relIndex (T:Subgroup G)=2 ∧
      ¬d.affineCentralizer eH ≤ M ∧
      J ≤ d.affineCentralizer eH ∧
      (J,d.affineCentralizer eH) ∈ localPairsIn (Chapter1.He G) M (centralizer ({u}:Set G)) ∧
      centralizer ({u}:Set G) ∈ gammaMax (Chapter1.He G) M ∧
      centralizer ({u}:Set G) ∉ Chapter1.He G ∧
      ∃ P : Sylow 2 (centralizer ({u}:Set G)),
        (P:Subgroup _).map (centralizer ({u}:Set G)).subtype =
          (T:Subgroup G) ⊓ centralizer ({u}:Set G) := by
  obtain ⟨e,hU,hS,hp,huU,hu2,huJ,huZ,hsR,hsJ,hSJ,hZ,hz,hZJ,hZT,
    huP,hJcard,hJe,hE,hMu,hi,hout,hJH⟩ :=
    d.single_alternating_selected_centralizer_packet hG T hM hTM hu hST hsingle hA hD
  obtain ⟨hpair,hg,P,hP⟩ := d.single_alternating_secondary_selection_of_marks
    hG T hM hTM hu hST hsingle hA ((e.symm BinaryFiveAffine.t:d.H):G)
    hu2 huJ hout hMu hi
  have hnon := d.single_alternating_secondary_not_He_of_affine_marks
    hG T hM hTM hu hdelta hcounter hST hsingle hA e hS huJ hg P hP hMu hi
  exact ⟨e,hU,hS,hp,huU,hu2,huJ,huZ,hsR,hsJ,hSJ,hZ,hz,hZJ,hZT,
    huP,hJcard,hJe,hE,hMu,hi,hout,hJH,hpair,hg,hnon,P,hP⟩
end CFSG.Quasithin.Chapter2
