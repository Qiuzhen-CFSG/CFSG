module
public import CFSG.Quasithin.Chapter15.Section01.SourceOmegaMarkedSplitting
public import Theory.GroupTheory.QuaternionDihedralEights
public import Theory.GroupTheory.ElementaryEightImageTransport

/-!
# Two actual point eights in the solvable full-Omega branch

The marked two-generator subgroup I inherits characteristic two from H.
Its same normal quaternion core is therefore self-centralizing in I.
The actual S₃ quotient supplies cubic and swapping actors, which construct
two distinct elementary eights with full point images. Injective transport
places them in G, and the original residual centralizer splitting promotes
PV-normality to normalization by the full chosen Sylow subgroup T.

Source: Aschbacher--Smith, E.2.9, E.2.17 and 15.1.11, printed pp.221--222,
229--230 and1089. The final solvable source theorem discharges all earlier
pair, fitting, actor and splitting inputs and retains the same P throughout.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- Actual marked-pair eights, with T-normality supplied by the same-core splitting. -/
theorem source_fullOmega_marked_pair_two_point_eights
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (I : Subgroup H) (hWI : (localModule T M).subgroupOf H ≤ I)
    (hgen : ∃g:I, ((localModule T M).subgroupOf H).subgroupOf I ⊔
      (((localModule T M).subgroupOf H).subgroupOf I).map (MulAut.conj g).toMonoidHom=⊤)
    (he : Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup 3))
    (hd : Nonempty (QuaternionCentralProductData (I.pCoreIn 2)))
    (R : Subgroup G)
    (hprod : (T : Subgroup G)=(I.pCoreIn 2).map H.subtype ⊔
      ((T : Subgroup G)⊓centralizer (localModule T M : Set G)))
    (hRC : (T : Subgroup G)⊓centralizer (localModule T M : Set G)=localModule T M⊔R)
    (hPR : (I.pCoreIn 2).map H.subtype ≤ centralizer (R : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    SourceCases.Omega (imageRepresentation M (localModule T M)
      (le_normalizer_conjugateSpanBy _ _)) →
    ∃ E F : Subgroup G, E≠F ∧
      ∀ U∈({E,F} : Set (Subgroup G)), IsElementaryAbelian 2 U ∧ Nat.card U=8 ∧
        U≤(I.pCoreIn 2).map H.subtype ∧ (T : Subgroup G)≤normalizer (U : Set G) ∧
        ((I.pCoreIn 2).map H.subtype ⊔ localModule T M)⊓centralizer (U : Set G)=U ∧
        Nonempty (ElementaryEightPointImage U) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  intro ho
  let V := localModule T M
  let W := V.subgroupOf H
  let W₀ := W.subgroupOf I
  let S : Sylow 2 H := T.subtype hH.1.1.2
  let d := source_15_1_1_qrcConfiguration hG T hM hH
  have hVT : V ≤ (T : Subgroup G) := d.module_le_core.trans (left_core_le_sylow d)
  have hVH : V≤H := hVT.trans hH.1.1.2
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVH
  let : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.subgroupOf hWI
  have hTV : (S : Subgroup H)≤normalizer (W : Set H) := by
    rw [←subgroupOf_normalizer_eq hVH]
    exact fun _ hs => (le_normalizer_conjugateSpanBy _ _ : M≤normalizer (V : Set G)) (hM.1.2 hs)
  obtain ⟨_,_,_,_,hfit⟩ := source_centralizing_minimalParabolic hG T hM hJ H hH
  obtain ⟨g,hg⟩ := hgen
  have hIfit := ChapterE.Witnesses.Solvable.two_conjugate_fitting S W I hTV hWI g hg hfit
  have hself : centralizer (pCore 2 I : Set I)≤pCore 2 I := by
    rw [←hIfit]
    exact centralizer_generalizedFitting_le I
  let dI : QuaternionCentralProductData (pCore 2 I) :=
    hd.some.map ((pCore 2 I).equivMapOfInjective I.subtype I.subtype_injective).symm
  have hWcard : Nat.card W₀=16 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWI).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hVH).toEquiv]
    obtain ⟨x,_,_⟩ := ho.2.2.2.2
    calc
      Nat.card V = Nat.card (Additive V) := rfl
      _ = Nat.card OrthogonalFourBinary.Space := Nat.card_congr x.toEquiv
      _ = 16 := by simp [OrthogonalFourBinary.Space,OrthogonalFourBinary.Plane,OrthogonalFourBinary.F]
  obtain ⟨E,F,hne,hEF⟩ := dI.two_eights_of_dihedral_quotient (pCore 2 I) W₀ hWcard hself he.some
  let f := H.subtype.comp I.subtype
  have hf : Function.Injective f := H.subtype_injective.comp I.subtype_injective
  have hPmap : (pCore 2 I).map f=(I.pCoreIn 2).map H.subtype := by
    change (pCore 2 I).map (H.subtype.comp I.subtype)=((pCore 2 I).map I.subtype).map H.subtype
    rw [map_map]
  have hWmap : W₀.map f=V := by
    rw [←map_map,map_subgroupOf_eq_of_le hWI,map_subgroupOf_eq_of_le hVH]
  refine ⟨E.map f,F.map f,(fun h => hne (map_injective hf h)),?_⟩
  intro U hU
  have hex : ∃ U₀∈({E,F} : Set (Subgroup I)), U=U₀.map f := by
    rcases hU with hU | hU
    · exact ⟨E,Or.inl rfl,hU⟩
    · exact ⟨F,Or.inr rfl,hU⟩
  obtain ⟨U₀,hU₀,rfl⟩ := hex
  obtain ⟨helem,hcard,hle,hn,hcentral,hpoint⟩ := hEF U₀ hU₀
  let := helem
  have hle' : U₀.map f≤(I.pCoreIn 2).map H.subtype := hPmap ▸ map_mono hle
  have hn' : (I.pCoreIn 2).map H.subtype⊔V≤normalizer (U₀.map f : Set G) := by
    rw [←hPmap,←hWmap,←Subgroup.map_sup]
    exact (map_mono hn).trans (U₀.le_normalizer_map f)
  have hT : (T : Subgroup G)≤normalizer (U₀.map f : Set G) := by
    rw [hprod,hRC,←sup_assoc]
    apply sup_le hn'
    exact ((le_centralizer_iff.mp hPR).trans (centralizer_le hle')).trans (Subgroup.centralizer_le_normalizer _)
  refine ⟨IsElementaryAbelian.map f,(card_map_of_injective hf).trans hcard,hle',hT,?_,
    hpoint.map (fun p => p.map f hf)⟩
  change ((I.pCoreIn 2).map H.subtype⊔V)⊓centralizer (U₀.map f : Set G)=U₀.map f
  rw [←hPmap,←hWmap,←Subgroup.map_sup,map_inf_centralizer_of_injective f hf,hcentral]
/-- The solvable full-Omega source supplies the same core, quotient geometry, and two point eights. -/
theorem source_fullOmega_solvable_two_point_eights
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable H) (hout : ¬localModule T M ≤ H.pCoreIn 2) :
    let V := localModule T M
    let N := chosenNormalizer T M V
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    SourceCases.Omega (imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)) →
    ∃ P : Subgroup G, P≤(T : Subgroup G) ∧ H≤normalizer (P : Set G) ∧
      Nonempty (QuaternionCentralProductData P) ∧
      (T : Subgroup G)=P⊔((T : Subgroup G)⊓centralizer (V : Set G)) ∧
      P⊓centralizer (V : Set G)=P⊓V ∧
      ⁅(T : Subgroup G)⊓centralizer (V : Set G),P⁆≤P⊓V ∧
      let X := (cubicCommutatorResidual (P.subgroupOf N)).map N.subtype
      X⊓centralizer (V : Set G)=V ∧
      ∃ E F : Subgroup G, E≠F ∧
        ∀ U∈({E,F} : Set (Subgroup G)), IsElementaryAbelian 2 U ∧ Nat.card U=8 ∧
          U≤P ∧ (T : Subgroup G)≤normalizer (U : Set G) ∧
          (P⊔V)⊓centralizer (U : Set G)=U ∧ Nonempty (ElementaryEightPointImage U) := by
  dsimp only
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  intro ho
  obtain ⟨I,hWI,hgen,he,_,hPT,hn,hd,hprod,hint,hcomm,hX,hRC,_,hPC⟩ :=
    source_fullOmega_solvable_marked_residual_splitting hG T hM hJ hH hs hout ho
  let P := (I.pCoreIn 2).map H.subtype
  let V := localModule T M
  let N := chosenNormalizer T M V
  let X := (cubicCommutatorResidual (P.subgroupOf N)).map N.subtype
  let R := (T : Subgroup G)⊓centralizer (V : Set G)⊓centralizer (X : Set G)
  have hdI : Nonempty (QuaternionCentralProductData (I.pCoreIn 2)) := hd.map
    (fun d => d.map ((I.pCoreIn 2).equivMapOfInjective H.subtype H.subtype_injective).symm)
  refine ⟨P,hPT,hn,hd,hprod,hint,hcomm,hX,?_⟩
  exact source_fullOmega_marked_pair_two_point_eights hG T hM hJ hH I hWI hgen he hdI
    R hprod hRC hPC ho

end CFSG.Quasithin.Chapter15.Section01
