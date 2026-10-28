module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingResidualTransferSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondaryA6Source
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingFrattiniSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondaryGammaSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTransferTerminalSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingNontrivialSource

/-!
# Exclusion of the original single alternating-five source branch

Retain the same affine coordinates and marked involutions from the original
secondary Gamma packet. The residual transfer argument gives an involution
fused with the central core involution inside the secondary Sylow and outside
the original selected subgroup. The actual secondary normal A6 component and
its moving four-group force a factor five in this involution's centralizer,
contradicting the order of the original maximal involution centralizer.
The nontrivial block-centralizer branch is already excluded by its full-Sylow
component argument. All extra marks and actions are produced from the original
source hypotheses.

Source: Aschbacher--Smith 2.4.29, printed pp.545--546.
-/


public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource ChapterC.Section05.BlockAnalysis
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_trivial_centralizer_false
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T:Subgroup G)≤M)
    (hu : ∀N:Subgroup G, IsMaximalTwoLocal N→(T:Subgroup G)≤N→N=M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hcounter : ¬IsTheorem241Model G)
    (hST : (d.S:Subgroup d.H).map d.H.subtype<(T:Subgroup G))
    (hsingle:d.L0=d.block)
    (hA:IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD:(T:Subgroup G) ⊓ centralizer (d.block.map d.H.subtype:Set G)=⊥) : False := by
  classical
  let B:=M⊓d.block.map d.H.subtype
  let I:=(pResidual 2 B).map B.subtype
  let P:=I.pCoreIn 2
  let S:=(d.S:Subgroup d.H).map d.H.subtype
  let J:=elementaryAbelianMaxJ S
  obtain ⟨eH,hU,hS,hp,huU,hu2,huJ,huZ,_hsS,_hsJ,hSJ,hZ,_hz,_hZJ,hZT,
    huP,_hJcard,_hJe,_hE,hMu,hi,hout,hJH,_hpair,_hg,hnon,Pu,hPu⟩ :=
    d.single_alternating_secondary_gamma_packet hG T hM hTM hu hdelta hcounter
      hST hsingle hA hD
  let u:G:=(eH.symm BinaryFiveAffine.t:d.H)
  let z:G:=(eH.symm BinaryFiveAffine.standardZ:d.H)
  let C:=centralizer ({u}:Set G)
  let Tu:=(T:Subgroup G)⊓C
  have hphi: (frattini S).map S.subtype≤P:=
    d.single_alternating_frattini_le_core hG T hM hTM hu hST hsingle hA hD
  have hfuse:∃r∈Tu,r∉S∧orderOf r=2∧IsConj z r:=
    d.single_alternating_residual_transfer_of_marks hG T hM hTM hu hST hsingle hA hD
      eH huP hu2 huJ huZ hZ hMu hi hphi
  have hzmark : d.affineCentralVector eH=z := by
    change (((eH.symm (SemidirectProduct.inl BinaryFiveAffine.centralSingular)):d.H):G)=z
    rw [←BinaryFiveAffine.standardZ_eq_centralSingular]
  have hZa : (center P).map P.subtype=zpowers (d.affineCentralVector eH) := by
    rw [hzmark]
    exact hZ
  have hZTa : zpowers (d.affineCentralVector eH)≤(center (T:Subgroup G)).map (T:Subgroup G).subtype := by
    rw [hzmark,←hZ]
    exact hZT
  have huUa : d.affineInvolution eH∈sourceModule (d.block.map d.H.subtype) := by
    have he : ((blockU d.block).map d.block.subtype).map d.H.subtype =
        sourceModule (d.block.map d.H.subtype) :=
      (moduleLayer_map d.H.subtype d.H.subtype_injective d.block).symm
    exact he ▸ huU
  obtain ⟨K,_hK,_hKn,⟨eK⟩,hTuK,hF4,hFK,hFTu,hRi,hRS,hRF,hx⟩ :=
    d.single_alternating_secondary_a6_geometry_of_marks hG T hM hTM hu hST hsingle hA hD
      eH hU hS hp huUa hu2 huJ huZ hSJ hZa hZTa huP hMu hi hout hJH hnon Pu hPu
  let F:=(d.affineCentralizerResidual eH).pCoreIn 2
  let : IsKleinFour F:=hF4
  let eKa : K.map C.subtype≃*alternatingGroup (Fin 6):=
    (K.equivMapOfInjective C.subtype C.subtype_injective).symm.trans eK
  have htwo:IsPGroup 2 Tu:=T.isPGroup'.to_le inf_le_left
  have hcent:centralizer ({z}:Set G)=M := by
    have he := (d.single_alternating_maximal_core_of_centralizer_bot
      hG T hM hTM hu hST hsingle hA hD).2
    rw [hZ] at he
    apply le_antisymm
    · rw [he,le_centralizer_iff,zpowers_le]
      intro x hx
      exact mem_centralizer_singleton_iff.mp hx
    · rw [he]
      exact centralizer_le (show ({z}:Set G)⊆(zpowers z:Set G) from
        Set.singleton_subset_iff.mpr (mem_zpowers z))
  exact d.single_alternating_transfer_marks_false hG T hM hTM hu hST hsingle hA hD
    (K.map C.subtype) Tu F hTuK htwo eKa hFK hFTu (J.subgroupOf Tu) hRi hRS hRF hx z hcent hfuse

theorem MinimalBlockSetup.single_alternating_source_false
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T:Subgroup G)≤M)
    (hu : ∀N:Subgroup G, IsMaximalTwoLocal N→(T:Subgroup G)≤N→N=M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hcounter : ¬IsTheorem241Model G)
    (hST : (d.S:Subgroup d.H).map d.H.subtype<(T:Subgroup G))
    (hsingle:d.L0=d.block)
    (hA:IsAlternatingBlock (d.block.map d.H.subtype) 5) : False := by
  by_cases hD:(T:Subgroup G)⊓centralizer (d.block.map d.H.subtype:Set G)=⊥
  · exact d.single_alternating_trivial_centralizer_false hG T hM hTM hu hdelta hcounter
      hST hsingle hA hD
  · exact d.single_alternating_nontrivial_centralizer_false hG T hM hTM hu hST hsingle hA hD
end CFSG.Quasithin.Chapter2
