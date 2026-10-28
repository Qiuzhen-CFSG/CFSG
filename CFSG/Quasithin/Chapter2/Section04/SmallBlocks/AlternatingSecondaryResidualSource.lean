module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondaryGammaSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondaryComponentAbsorption
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSylowSource
/-!
# The selected secondary A4 residual and its Sylow geometry

The original affine packet identifies O²(Hᵤ) with A4 and places its four-group
inside the actual Sylow subgroup of Gᵤ. The selected Thompson subgroup
normalizes the residual and has index two in that Sylow subgroup. The marked
product u z lies in the residual four-group. All maps retain the original
ambient centralizer; the final consumer selects the original Gamma packet
and constructs its marked 1.1.5 and component-refinement inputs.

Source: Aschbacher--Smith, 2.4.29, printed pp.545--546.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource ChapterC.Section05.BlockAnalysis
private theorem affine_residual_core_le_vector :
    BinaryFiveAffine.residualImage.pCoreIn 2 ≤ BinaryFiveAffine.vectorGroup := by
  have hLX : BinaryFiveAffine.residualImage≤BinaryFiveAffine.X := by
    rw [BinaryFiveAffine.residualImage_eq]
    rintro _ ⟨g,hg,rfl⟩
    exact ⟨g,rfl⟩
  have hXL : BinaryFiveAffine.X≤normalizer (BinaryFiveAffine.residualImage : Set BinaryFiveAffine.W) := by
    rw [BinaryFiveAffine.residualImage_eq]
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,BinaryFiveAffine.X] using
      (alternatingGroup (Fin 4)).le_normalizer_map BinaryFiveAffine.symmetricEmbedding
  have hcore := pCoreIn_mono_of_normalizes (p:=2) hLX hXL
  change _≤(pCore 2 BinaryFiveAffine.X).map BinaryFiveAffine.X.subtype at hcore
  rw [BinaryFiveAffine.X_twoCore_image] at hcore
  apply hcore.trans
  rintro _ ⟨v,hv,rfl⟩
  exact ⟨v,rfl⟩

variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_secondary_thompson_index_of_marks
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G)≤M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G)≤N → N=M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0=d.block) (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (u : G)
    (hJC : elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)≤centralizer ({u}:Set G))
    (hi : ((T : Subgroup G)⊓centralizer ({u}:Set G)).relIndex (T : Subgroup G)=2)
    (P : Sylow 2 (centralizer ({u}:Set G)))
    (hP : (P : Subgroup (centralizer ({u}:Set G))).map (centralizer ({u}:Set G)).subtype=
      (T : Subgroup G)⊓centralizer ({u}:Set G)) :
    (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)).subgroupOf
      (centralizer ({u}:Set G)) ≤ (P : Subgroup (centralizer ({u}:Set G))) ∧
    ((elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)).subgroupOf
      (centralizer ({u}:Set G))).relIndex (P : Subgroup (centralizer ({u}:Set G)))=2 := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let J := elementaryAbelianMaxJ S
  let C := centralizer ({u}:Set G)
  let Tu := (T : Subgroup G)⊓C
  have hJS : J≤S := sSup_le fun A hA=>hA.1
  have hJT : J≤(T : Subgroup G) := hJS.trans hST.le
  have hJTu : J≤Tu := le_inf hJT hJC
  have hJSi := (d.single_alternating_family_action hG T hST hsingle hA).1
  have hSTi := (d.single_alternating_sylow_index_source hG T hM hTM hu hST hsingle hA).1
  have hiT : J.relIndex (T : Subgroup G)=4 := by
    rw [←relIndex_mul_relIndex J S (T : Subgroup G) hJS hST.le,hJSi,hSTi]
  have hiTu : J.relIndex Tu=2 := by
    have hh := relIndex_mul_relIndex J Tu (T : Subgroup G) hJTu (show Tu≤(T : Subgroup G) from inf_le_left)
    rw [hi] at hh
    omega
  refine ⟨?_,?_⟩
  · intro j hj
    have hm : (j:G)∈(P : Subgroup C).map C.subtype := hP.symm ▸ hJTu hj
    obtain ⟨p,hp,he⟩ := hm
    exact (C.subtype_injective he) ▸ hp
  · rw [←relIndex_map_map_of_injective _ _ C.subtype_injective,
      map_subgroupOf_eq_of_le hJC,hP]
    exact hiTu


theorem MinimalBlockSetup.single_alternating_secondary_residual_geometry_of_marks
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G)≤M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G)≤N → N=M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0=d.block) (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (eH : d.H ≃* BinaryFiveAffine.W)
    (hU : ((blockU d.block).map d.block.subtype).map eH.toMonoidHom=BinaryFiveAffine.vectorGroup)
    (hp : d.MarkedA5CentralizerPacket eH)
    (hJH : elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)≤d.affineCentralizer eH)
    (hi : ((T : Subgroup G)⊓centralizer ({d.affineInvolution eH}:Set G)).relIndex (T : Subgroup G)=2)
    (P : Sylow 2 (centralizer ({d.affineInvolution eH}:Set G)))
    (hP : (P : Subgroup (centralizer ({d.affineInvolution eH}:Set G))).map
      (centralizer ({d.affineInvolution eH}:Set G)).subtype=
      (T : Subgroup G)⊓centralizer ({d.affineInvolution eH}:Set G)) :
    let C := centralizer ({d.affineInvolution eH}:Set G)
    let L := (d.affineCentralizerResidual eH).subgroupOf C
    let R := (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)).subgroupOf C
    IsPPerfect 2 L ∧ Nonempty (L ≃* alternatingGroup (Fin 4)) ∧
      R≤(P : Subgroup C) ∧ R.relIndex (P : Subgroup C)=2 ∧
      R≤normalizer (L : Set C) ∧
      (pCore 2 L).map L.subtype≤(P : Subgroup C) ∧
      ∃ a : L, a∈pCore 2 L ∧ a≠1 ∧
        d.affineCentralVector eH=(a:G)*d.affineInvolution eH := by
  let u := d.affineInvolution eH
  let C := centralizer ({u}:Set G)
  let La := d.affineCentralizerResidual eH
  let L := La.subgroupOf C
  let J := elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let R := J.subgroupOf C
  have hLH : La≤d.affineCentralizer eH := map_subtype_le _
  have hLC : La≤C := hLH.trans inf_le_right
  let eR : pResidual 2 (d.affineCentralizer eH) ≃* La :=
    (pResidual 2 (d.affineCentralizer eH)).equivMapOfInjective
      (d.affineCentralizer eH).subtype (d.affineCentralizer eH).subtype_injective
  let eL : L ≃* alternatingGroup (Fin 4) :=
    (subgroupOfEquivOfLe hLC).trans (eR.symm.trans hp.residual.some)
  have hLperf : IsPPerfect 2 L :=
    (isPPerfect_pResidual (G:=d.affineCentralizer eH) 2).of_surjective
      (eR.trans (subgroupOfEquivOfLe hLC).symm).toMonoidHom
      (eR.trans (subgroupOfEquivOfLe hLC).symm).surjective
  have hJC : J≤C := hJH.trans inf_le_right
  obtain ⟨hRP,hRi⟩ := d.single_alternating_secondary_thompson_index_of_marks hG T hM hTM hu
    hST hsingle hA u hJC hi P hP
  have hRN : R≤normalizer (L : Set C) := by
    rw [←subgroupOf_normalizer_eq hLC]
    exact comap_mono (hJH.trans (le_normalizer_embedded_pResidual 2 (d.affineCentralizer eH)))
  let f : BinaryFiveAffine.W →* G := d.H.subtype.comp eH.symm.toMonoidHom
  have hfL : BinaryFiveAffine.residualImage.map f=La := by
    rw [←BinaryFiveAffine.markedResidualImage_map eH,map_map]
    have hf : f.comp eH.toMonoidHom=d.H.subtype := by
      ext x
      exact congrArg d.H.subtype (eH.symm_apply_apply x)
    rw [hf]
    exact BinaryFiveAffine.markedResidualImage_ambient_map d.H eH
  let Ui := (blockU d.block).map d.block.subtype
  have hUi : Ui.map d.H.subtype=sourceModule (d.block.map d.H.subtype) :=
    (moduleLayer_map d.H.subtype d.H.subtype_injective d.block).symm
  have hfU : BinaryFiveAffine.vectorGroup.map f=sourceModule (d.block.map d.H.subtype) := by
    rw [←hU,map_map]
    have hf : f.comp eH.toMonoidHom=d.H.subtype := by
      ext x
      exact congrArg d.H.subtype (eH.symm_apply_apply x)
    rw [hf,hUi]
  have hEU : La.pCoreIn 2≤sourceModule (d.block.map d.H.subtype) := by
    have hh := map_mono (f:=f) affine_residual_core_le_vector
    rw [map_pCoreIn_of_injective 2 _ f (d.H.subtype_injective.comp eH.symm.injective),hfL,hfU] at hh
    exact hh
  have hUcore : Ui=pCore 2 d.H := by
    apply (map_injective (f:=eH.toMonoidHom) eH.injective)
    rw [hU,pCore_map_iso,BinaryFiveAffine.pCore_eq_vectorGroup]
  have hUS : sourceModule (d.block.map d.H.subtype)≤(d.S : Subgroup d.H).map d.H.subtype := by
    rw [←hUi,hUcore]
    exact map_mono (pCore_isPGroup.le_sylow_of_normal d.S)
  have hES : La.pCoreIn 2≤(T : Subgroup G) := (hEU.trans hUS).trans hST.le
  have hEambient : ((pCore 2 L).map L.subtype).map C.subtype=La.pCoreIn 2 := by
    change (L.pCoreIn 2).map C.subtype=La.pCoreIn 2
    rw [map_pCoreIn_of_injective 2 L C.subtype C.subtype_injective,map_subgroupOf_eq_of_le hLC]
  have hEP : (pCore 2 L).map L.subtype≤(P : Subgroup C) := by
    intro a ha
    have hae : (a:G)∈La.pCoreIn 2 := hEambient ▸ mem_map_of_mem C.subtype ha
    obtain ⟨p,hp,he⟩ := hP.symm ▸ (show (a:G)∈(T : Subgroup G)⊓C from ⟨hES hae,a.property⟩)
    exact (C.subtype_injective he) ▸ hp
  have ham := hp.marked_core
  have haL := pCoreIn_le 2 La ham
  let aa : L := ⟨⟨u*d.affineCentralVector eH,hLC haL⟩,haL⟩
  have ha : aa∈pCore 2 L := by
    have hh : (aa:C)∈(pCore 2 L).map L.subtype := by
      obtain ⟨b,hb,he⟩ := ham
      let bb : L := (subgroupOfEquivOfLe hLC).symm b
      have hbb : bb∈pCore 2 L := by
        have hm := mem_map_of_mem (subgroupOfEquivOfLe hLC).symm.toMonoidHom hb
        rwa [pCore_map_iso 2 (subgroupOfEquivOfLe hLC).symm] at hm
      exact ⟨bb,hbb,Subtype.ext he⟩
    exact (mem_map_iff_mem L.subtype_injective).mp hh
  have haeq : (aa:G)=u*d.affineCentralVector eH := rfl
  have hza : d.affineCentralVector eH=(aa:G)*u := by
    have hc := mem_centralizer_singleton_iff.mp ((hLC haL) : u*d.affineCentralVector eH∈C)
    have huu : u*u=1 := by
      have huorder : orderOf u=2 := by
        change orderOf ((eH.symm BinaryFiveAffine.t:d.H):G)=2
        exact (orderOf_injective d.H.subtype d.H.subtype_injective (eH.symm BinaryFiveAffine.t)).trans
          ((eH.symm.orderOf_eq _).trans BinaryFiveAffine.t_order)
      simpa only [huorder,pow_two] using pow_orderOf_eq_one u
    rw [haeq]
    calc
      d.affineCentralVector eH=(u*u)*d.affineCentralVector eH := by rw [huu,one_mul]
      _ = u*(u*d.affineCentralVector eH) := mul_assoc _ _ _
      _ = (u*d.affineCentralVector eH)*u := hc.symm
  exact ⟨hLperf,⟨eL⟩,hRP,hRi,hRN,hEP,aa,ha,
    fun hh=>hp.marked_ne (congrArg (fun a:L=>(a:G)) hh),hza⟩


/-- The marked residual data used by the secondary component argument. -/
structure SecondaryResidualGeometry {C : Type*} [Group C]
    (P L R : Subgroup C) (z u : G) (f : C →* G) : Prop where
  perfect : IsPPerfect 2 L
  alternating : Nonempty (L ≃* alternatingGroup (Fin 4))
  thompson_le : R≤P
  thompson_index : R.relIndex P=2
  thompson_normalizes : R≤normalizer (L : Set C)
  core_le : (pCore 2 L).map L.subtype≤P
  marked : ∃a:L, a∈pCore 2 L ∧ a≠1 ∧ z=f (a:C)*u

theorem MinimalBlockSetup.single_alternating_secondary_residual_packet
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G)≤M)
    (hu : ∀N:Subgroup G, IsMaximalTwoLocal N → (T:Subgroup G)≤N → N=M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty) (hcounter : ¬IsTheorem241Model G)
    (hST : (d.S:Subgroup d.H).map d.H.subtype<(T:Subgroup G))
    (hsingle : d.L0=d.block) (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD : (T:Subgroup G)⊓centralizer (d.block.map d.H.subtype:Set G)=⊥) :
    ∃eH:d.H≃*BinaryFiveAffine.W,
      let u:=d.affineInvolution eH
      let z:=d.affineCentralVector eH
      let C:=centralizer ({u}:Set G)
      ∃P:Sylow 2 C,
        (P:Subgroup C).map C.subtype=(T:Subgroup G)⊓C ∧ orderOf u=2 ∧
        M⊓C=(T:Subgroup G)⊓C ∧ C∉Chapter1.He G ∧
        Chapter1.Lemma115Hypotheses C P M z ∧
        (∀K:Subgroup C, IsComponent C K →
          Nonempty (ComponentRefinement.MathieuSourceSetup C (K.map C.subtype) M P z)) ∧
        SecondaryResidualGeometry (P:Subgroup C)
          ((d.affineCentralizerResidual eH).subgroupOf C)
          ((elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)).subgroupOf C)
          z u C.subtype := by
  obtain ⟨eH,hU,hS,hp,huU,hu2,huJ,huZ,hsR,hsJ,hSJ,hZ,hz,hZJ,hZT,
    huP,hJcard,hJe,hE,hMu,hi,hout,hJH,hpair,hg,hnon,P,hP⟩ :=
    d.single_alternating_secondary_gamma_packet hG T hM hTM hu hdelta hcounter hST hsingle hA hD
  have hzT : d.affineCentralVector eH∈(center (T:Subgroup G)).map (T:Subgroup G).subtype := by
    change ((eH.symm (SemidirectProduct.inl BinaryFiveAffine.centralSingular):d.H):G)∈_
    rw [←BinaryFiveAffine.standardZ_eq_centralSingular]
    apply hZT
    rw [hZ]
    exact mem_zpowers _
  have hz2 : orderOf (d.affineCentralVector eH)=2 := by
    change orderOf ((eH.symm (SemidirectProduct.inl BinaryFiveAffine.centralSingular):d.H):G)=2
    rw [←BinaryFiveAffine.standardZ_eq_centralSingular]
    exact (orderOf_injective d.H.subtype d.H.subtype_injective (eH.symm BinaryFiveAffine.standardZ)).trans
      ((eH.symm.orderOf_eq _).trans BinaryFiveAffine.standardZ_order)
  have h115 := d.single_alternating_secondary_lemma115_of_marks hG T hM hTM hu hST
    hsingle hA (d.affineInvolution eH) hu2 huJ hout hMu hi P hP (d.affineCentralVector eH) hzT hz2
  obtain ⟨hL,eA,hRP,hRi,hRN,hEP,a,ha,hane,hza⟩ :=
    d.single_alternating_secondary_residual_geometry_of_marks hG T hM hTM hu hST hsingle hA
      eH hU hp hJH hi P hP
  refine ⟨eH,P,hP,hu2,hMu,hnon,h115,?_,hL,eA,hRP,hRi,hRN,hEP,a,ha,hane,hza⟩
  intro K hK
  exact ⟨d.single_alternating_secondary_refinement_setup_of_marks hG T hM hTM hu hST
    hsingle hA (d.affineInvolution eH) hu2 huJ hout hMu hi P hP (d.affineCentralVector eH) hzT hz2 K hK⟩

end CFSG.Quasithin.Chapter2
