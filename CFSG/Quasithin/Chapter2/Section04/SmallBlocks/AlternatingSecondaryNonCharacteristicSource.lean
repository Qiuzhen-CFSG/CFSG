module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondarySelectionSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPairSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingBorelSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.LinearSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.CubicDoubleCenterSource
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.PairFrattini
public import Theory.SpecificGroups.BinaryFiveAffine.ThompsonFrattini
public import Theory.Frattini.Intersection

/-!
# The secondary centralizer is not of characteristic two

If the original selected involution centralizer were of characteristic two,
its marked Sylow subgroup would admit the Section 2.4 block reduction.
The linear and single cubic source exclusions remove those cases. A paired
cubic block has trivial intersection between its Thompson Frattini subgroup
and its center, whereas the retained pair involution lies in both. Finally,
an alternating-five block has a Borel image of order twelve, incompatible
with its intersection with M being a two-group.

The affine consumer transports the actual square root into J(S), so it
uses the same involution and full Sylow marking as the original selection.
Source: Aschbacher--Smith, 2.4.29, printed p.545.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_not_in_centralizer_of_two_intersection
    (d : MinimalBlockSetup M) (hsingle:d.L0=d.block)
    (hA:ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (u:G) (hHC:d.H≤centralizer ({u}:Set G))
    (hp:IsPGroup 2 (M ⊓ centralizer ({u}:Set G) : Subgroup G)) : False := by
  let B := M.subgroupOf d.H
  let f : B →* (M ⊓ centralizer ({u}:Set G) : Subgroup G) :=
    { toFun b := ⟨((b:d.H):G),⟨b.property,hHC (b:d.H).property⟩⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro x y hh
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : (M ⊓ centralizer ({u}:Set G) : Subgroup G) => (a:G)) hh
  have hB := hp.of_injective f hf
  obtain ⟨q,e,i,hq,hker,hL,hkerL,hBq,hBL,hcard,he⟩ := d.single_alternating_borel_action hsingle hA
  have hI : IsPGroup 2 (((M.subgroupOf d.H) ⊓ d.block).map q) :=
    (hB.to_le inf_le_left).map q
  obtain ⟨n,hn⟩ := hI.exists_card_eq
  have hd : 3∣2^n := hn ▸ hcard.symm ▸ (by decide : 3∣12)
  have : 3∣2 := Nat.prime_three.dvd_of_dvd_pow hd
  norm_num at this

theorem MinimalBlockSetup.single_alternating_secondary_not_He_of_marks
    (_d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T:Subgroup G)≤M)
    (hu : ∀N:Subgroup G, IsMaximalTwoLocal N→(T:Subgroup G)≤N→N=M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hcounter : ¬IsTheorem241Model G)
    (u:G) (hu2:orderOf u=2)
    (R:Subgroup G) (hR:R∈beta M)
    (hRT:R=elementaryAbelianMaxJ (T:Subgroup G))
    (huPhi:u∈(frattini R).map R.subtype)
    (hg:centralizer ({u}:Set G)∈gammaMax (Chapter1.He G) M)
    (P:Sylow 2 (centralizer ({u}:Set G)))
    (hP:(P:Subgroup _).map (centralizer ({u}:Set G)).subtype=
      (T:Subgroup G) ⊓ centralizer ({u}:Set G))
    (hRP:R≤(T:Subgroup G) ⊓ centralizer ({u}:Set G))
    (hPT:(T:Subgroup G) ⊓ centralizer ({u}:Set G)<(T:Subgroup G))
    (hMu:M ⊓ centralizer ({u}:Set G)=(T:Subgroup G) ⊓ centralizer ({u}:Set G)) :
    centralizer ({u}:Set G)∉Chapter1.He G := by
  intro he
  let C := centralizer ({u}:Set G)
  have hzero : C∈gammaEvenZero (Chapter1.He G) M := ⟨Or.inr hg,he⟩
  have hRb : (P:Subgroup C).map C.subtype∈beta M :=
    beta_mono hR (hP.symm ▸ hRP) (P.isPGroup'.map C.subtype)
  have hfull : ((P:Subgroup C).map C.subtype,C)∈localPairsIn (Chapter1.He G) M C :=
    ⟨⟨hRb,he,hg.1.1,map_subtype_le _,gamma_not_le hg.1⟩,le_rfl⟩
  obtain ⟨e,heC,heS⟩ := exists_minimalBlockSetup_with_sylow hG T hTM hu hzero P hfull
  have heTu : (e.S:Subgroup e.H).map e.H.subtype=
      (T:Subgroup G) ⊓ C := heS.trans hP
  have heT : (e.S:Subgroup e.H).map e.H.subtype<(T:Subgroup G) := heTu ▸ hPT
  have htype := ChapterC.Section05.BlockAnalysis.chiZero_equiv
    (equivMapOfInjective e.block e.H.subtype e.H.subtype_injective) e.block_type.2
  rcases htype with ⟨n,hL⟩ | h3 | h5
  · exact e.linear_source_false hG T hM hTM hu hdelta heT hcounter hL
  · by_cases hepair : e.L0=e.block
    · exact hcounter (e.single_cubic_classification hG T heT hepair h3 hM hu hdelta)
    obtain ⟨c⟩ := e.paired_cubic_coordinates hG T hM hTM hu heT hepair h3
    have hJR : elementaryAbelianMaxJ ((e.S:Subgroup e.H).map e.H.subtype)=R := by
      rw [heTu]
      exact (elementaryAbelianMaxJ_eq_of_intermediate_finite (T:Subgroup G)
        ((T:Subgroup G) ⊓ C) (hRT.symm ▸ hRP) inf_le_left).trans hRT.symm
    have huH : u∈e.H := map_subtype_le _ (heTu.symm ▸ hRP ((map_subtype_le _) huPhi))
    have huZ : u∈(center e.H).map e.H.subtype := by
      refine ⟨⟨u,huH⟩,mem_center_iff.mpr ?_,rfl⟩
      intro a
      exact Subtype.ext (mem_centralizer_singleton_iff.mp (heC a.property))
    have huPhi' : u∈(frattini (DoubleA3.sourceR e)).map (DoubleA3.sourceR e).subtype := by
      have hJR' : DoubleA3.sourceR e=R := hJR
      rw [hJR']
      exact huPhi
    have hbot : u∈(⊥:Subgroup G) := c.frattini_inf_center_eq_bot ▸ ⟨huPhi',huZ⟩
    have hh := mem_bot.mp hbot
    rw [hh,orderOf_one] at hu2
    omega
  · have heone := e.alternating_five_single_source hG T hM hTM hu heT h5
    have hp : IsPGroup 2 (M ⊓ C : Subgroup G) := hMu.symm ▸ T.isPGroup'.to_le inf_le_left
    exact e.single_alternating_not_in_centralizer_of_two_intersection heone h5 u heC hp
omit [Finite G] in
theorem MinimalBlockSetup.single_alternating_pair_mem_thompson_frattini
    (d : MinimalBlockSetup M) (eH : d.H ≃* BinaryFiveAffine.W)
    (hS : (d.S : Subgroup d.H).map eH.toMonoidHom =
      (BinaryFiveAffine.standardSylow : Subgroup BinaryFiveAffine.W)) :
    ((eH.symm BinaryFiveAffine.t : d.H) : G) ∈
      (frattini (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))).map
        (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)).subtype := by
  let f : BinaryFiveAffine.W →* G := d.H.subtype.comp eH.symm.toMonoidHom
  have hf : Function.Injective f := d.H.subtype_injective.comp eH.symm.injective
  have hRm : (BinaryFiveAffine.standardSylow : Subgroup BinaryFiveAffine.W).map f =
      (d.S : Subgroup d.H).map d.H.subtype := by
    rw [←hS,map_map]
    have hh : f.comp eH.toMonoidHom=d.H.subtype := by
      apply MonoidHom.ext
      intro x
      simp [f]
    rw [hh]
  have hJm : BinaryFiveAffine.sylowBase.map f =
      elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) := by
    rw [←BinaryFiveAffine.thompson_standardSylow,
      ←elementaryAbelianMaxJ_map_injective f hf,hRm]
  change f BinaryFiveAffine.t ∈ _
  rw [←hJm,frattini_image_map _ f hf]
  exact mem_map_of_mem f BinaryFiveAffine.t_mem_frattini_base

theorem MinimalBlockSetup.single_alternating_secondary_not_He_of_affine_marks
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T:Subgroup G)≤M)
    (hu : ∀N:Subgroup G, IsMaximalTwoLocal N→(T:Subgroup G)≤N→N=M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hcounter : ¬IsTheorem241Model G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T:Subgroup G))
    (hsingle : d.L0=d.block)
    (hA : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (eH : d.H ≃* BinaryFiveAffine.W)
    (hS : (d.S : Subgroup d.H).map eH.toMonoidHom =
      (BinaryFiveAffine.standardSylow : Subgroup BinaryFiveAffine.W)) :
    let u : G := (eH.symm BinaryFiveAffine.t : d.H)
    let R := elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)
    let C := centralizer ({u}:Set G)
    u∈(center R).map R.subtype → C∈gammaMax (Chapter1.He G) M →
    (P : Sylow 2 C) → (P:Subgroup C).map C.subtype=(T:Subgroup G) ⊓ C →
    M ⊓ C=(T:Subgroup G) ⊓ C →
    ((T:Subgroup G) ⊓ C).relIndex (T:Subgroup G)=2 → C∉Chapter1.He G := by
  intro u R C huR hg P hP hMu hi
  have hR : R∈beta M := d.thompson_beta_of_index_two hG T hM hTM hu hST
    (d.single_alternating_family_action hG T hST hsingle hA).1
  have hRT : R=elementaryAbelianMaxJ (T:Subgroup G) :=
    (d.single_alternating_sylow_index_source hG T hM hTM hu hST hsingle hA).2.2.symm
  have hRC : R≤C := by
    obtain ⟨w,hw,hwv⟩ := huR
    intro r hr
    apply mem_centralizer_singleton_iff.mpr
    rw [←hwv]
    exact congrArg Subtype.val (mem_center_iff.mp hw ⟨r,hr⟩)
  have hRP : R≤(T:Subgroup G) ⊓ C :=
    le_inf ((sSup_le fun _ h=>h.1).trans hST.le) hRC
  have hPT : (T:Subgroup G) ⊓ C < (T:Subgroup G) := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro hh
    rw [hh,relIndex_self] at hi
    omega
  have hu2 : orderOf u=2 := by
    change orderOf ((eH.symm BinaryFiveAffine.t : d.H):G)=2
    exact (orderOf_injective d.H.subtype d.H.subtype_injective
      (eH.symm BinaryFiveAffine.t)).trans
        ((eH.symm.orderOf_eq BinaryFiveAffine.t).trans BinaryFiveAffine.t_order)
  exact d.single_alternating_secondary_not_He_of_marks hG T hM hTM hu hdelta hcounter
    u hu2 R hR hRT (d.single_alternating_pair_mem_thompson_frattini eH hS)
    hg P hP hRP hPT hMu

end CFSG.Quasithin.Chapter2
