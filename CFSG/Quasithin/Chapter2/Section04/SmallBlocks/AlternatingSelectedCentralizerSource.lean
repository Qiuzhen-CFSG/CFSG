module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingMarkedCentralizerSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondaryCentralizerSource
/-!
# Selecting the original marked alternating-five centralizer packet

The original trivial-centralizer branch supplies one affine equivalence and
its marked involution. The finite Hᵤ packet is transported through that same
equivalence, while the original secondary-centralizer calculation gives
Mᵤ=Tᵤ of index two. Since Hᵤ contains an A₄ residual it lies outside M;
the selected Thompson subgroup lies in Hᵤ. No model or centralizer premise
is left to the downstream involution-centralizer continuation.

Source: Aschbacher--Smith 2.4.29, printed pp.545--546.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_selected_centralizer_packet
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
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
      J ≤ d.affineCentralizer eH := by
  obtain ⟨e,hU,hS,hm⟩ := d.single_alternating_marked_involutions
    hG T hM hTM hu hST hsingle hA hD
  rcases hm with ⟨huU,hu2,huJ,huZ,hsR,hsJ,hSJ,hZ,hz,hZJ,hZT,huP,hJcard,hJe⟩
  have hp := d.single_alternating_marked_centralizer_packet hsingle e hU
  obtain ⟨hMu,hi⟩ := d.single_alternating_secondary_centralizer_of_marks
    hG T hM hTM hu hST hsingle hA hD ((e.symm BinaryFiveAffine.t:d.H):G)
      huP hu2 huZ huJ hJcard hJe
  have hout := d.marked_centralizer_not_le_of_secondary_centralizer T e hp hMu
  refine ⟨e,hU,hS,hp,huU,hu2,huJ,huZ,hsR,hsJ,hSJ,hZ,hz,hZJ,hZT,huP,hJcard,hJe,
    d.single_alternating_marked_moved_elementary hsingle hA e,hMu,hi,hout,?_⟩
  let R := (d.S:Subgroup d.H).map d.H.subtype
  let J := elementaryAbelianMaxJ R
  have hJR : J≤R := sSup_le fun _ h=>h.1
  have hJH : J≤d.H := hJR.trans (map_subtype_le _)
  have hJC : J≤centralizer ({((e.symm BinaryFiveAffine.t:d.H):G)}:Set G) := by
    have hh := congrArg (fun X : Subgroup G => X) hSJ
    change R ⊓ centralizer ({((e.symm BinaryFiveAffine.t:d.H):G)}:Set G)=J at hh
    rw [←hh]
    exact inf_le_right
  exact le_inf hJH hJC

end CFSG.Quasithin.Chapter2
