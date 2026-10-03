module
public import Stellmacher.SectionTwo.NormalSupplementCore
public import Stellmacher.SectionTwo.CoreCentralizerSylow
public import Stellmacher.SectionTwo.LemmaTwoThree
public import Stellmacher.CharacteristicTwoNormal
public import Stellmacher.BaumannMap
public import Stellmacher.BaumannNormalizer
/-!
# Baumann Sylow control across a normal supplement

Let N be normal in the finite Section Two group G, with N S = G and a
supplied Sylow Q of N whose image is normalized by S and lies in S.
Assume this image contains the central involutions of S and is nontrivial,
and that O2(G)=C_S(V) for the original module V=vSubgroup S.
Then V lies in the Baumann subgroup B of Q's image, and B is a Sylow
two-subgroup of its normal closure in G.

Core-centralizer Sylow control restricts from G to N. Comparing the original
module with the native module of Q gives the exact (2.3) hypotheses in N.
The supporting native transfer identifies its Baumann normal closure with
the closure in G by the normal-supplement identity and maps its Sylow witness.
The central involutions of S lie in B, so V lies in its normal closure;
normality of V and the resulting Sylow control then put V inside B.

Source: Stellmacher (2.3) and the normal-supplement argument in (4.6),
Journal of Algebra 190 (1997), pp.20 and26, reused in (8.3), p38;
refs/latex/stellmacher-n-group.tex. The native transfer formerly appeared
privately in SectionFour/BaumannSylow and now serves both applications.
-/

namespace Stellmacher.SectionTwo

private theorem sylow_map_range
    {H G : Type*} [Group H] [Group G] [Finite H]
    (f : H →* G) (T : Sylow 2 H) :
    IsSylowSubgroupIn ((T : Subgroup H).map f) f.range := by
  let U := T.mapSurjective f.rangeRestrict_surjective
  refine ⟨U, ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map]
  congr 1

/-- Transport the native (2.3) Sylow across a normal supplement. -/
public theorem baumann_sylow_of_native_two_three
    {H : Type*} [Group H] [Finite H]
    (E S B : Subgroup H) [E.Normal]
    (hE : Hypotheses E) (Q : Sylow 2 E)
    (hcore : pCore 2 E = (Q : Subgroup E) ⊓
      Subgroup.centralizer (vSubgroup Q : Set E))
    (hgen : E ⊔ S = ⊤)
    (hB : B = ((Q : Subgroup E) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (Q : Subgroup E)) : Set E)).map E.subtype)
    (hSB : S ≤ Subgroup.normalizer (B : Set H)) :
    IsSylowSubgroupIn B (Subgroup.normalClosure (B : Set H)) := by
  let b := (Q : Subgroup E) ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ (Q : Subgroup E)) : Set E)
  let l := Subgroup.normalClosure (b : Set E)
  obtain ⟨T, hT⟩ := lemma_two_three hE Q hcore b l rfl rfl
  have hBE : B ≤ E := hB ▸ Subgroup.map_subtype_le b
  have hBsub : B.subgroupOf E = b := by
    rw [hB]
    exact Subgroup.comap_map_eq_self_of_injective E.subtype_injective _
  have hLc : Subgroup.normalClosure (B : Set H) = l.map E.subtype := by
    rw [Subgroup.normalClosure_eq_map_of_normal_supplement E S B hgen hBE hSB,hBsub]
  let f : l →* H := E.subtype.comp l.subtype
  have hf : f.range = l.map E.subtype := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h := sylow_map_range f T
  rw [hf] at h
  have hTm : (T : Subgroup l).map f = B := by
    change (T : Subgroup l).map (E.subtype.comp l.subtype) = B
    rw [← Subgroup.map_map,hT]
    exact hB.symm
  rwa [hTm, ← hLc] at h

/-- The original center module lies in the normal supplement's Baumann Sylow. -/
public theorem normal_supplement_baumann_setup
    {G : Type*} [Group G] [Finite G] (h : Hypotheses G) (S : Sylow 2 G)
    (N : Subgroup G) [N.Normal] (Q : Sylow 2 N)
    (hgen : N ⊔ (S : Subgroup G) = ⊤)
    (hQS : (Q : Subgroup N).map N.subtype ≤ (S : Subgroup G))
    (hSN : (S : Subgroup G) ≤
      Subgroup.normalizer (((Q : Subgroup N).map N.subtype : Subgroup G) : Set G))
    (hZQ : zSubgroup S ≤ (Q : Subgroup N).map N.subtype)
    (hQne : (Q : Subgroup N) ≠ ⊥)
    (hcore : pCore 2 G = (S : Subgroup G) ⊓ Subgroup.centralizer (vSubgroup S : Set G)) :
    let B := (Q : Subgroup N).map N.subtype ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ ((Q : Subgroup N).map N.subtype)) : Set G)
    vSubgroup S ≤ B ∧
      IsSylowSubgroupIn B (Subgroup.normalClosure (B : Set G)) := by
  classical
  let QA := (Q : Subgroup N).map N.subtype
  let B := QA ⊓ Subgroup.centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ QA) : Set G)
  let L := Subgroup.normalClosure (B : Set G)
  have hVnorm : (vSubgroup S).Normal := Subgroup.normalClosure_normal
  let _ : (vSubgroup S).Normal := hVnorm
  have hNchar := characteristicTwo_normal_subgroup h.solvable h.centralizer_twoCore_le N
  have hN2 : Even (Nat.card N) := by
    have hdvd : 2 ∣ Nat.card Q := Q.isPGroup'.card_eq_or_dvd.resolve_left
      (fun hc => hQne (Subgroup.card_eq_one.mp hc))
    exact even_iff_two_dvd.mpr (hdvd.trans (Subgroup.card_subgroup_dvd_card (Q : Subgroup N)))
  have hsecN : Hypotheses N := by
    let _ := h.solvable
    exact ⟨inferInstance,hN2,hNchar⟩
  have hcoreN := normal_supplement_core_centralizer N S Q hgen hQS hZQ hSN
    (twoCore_sylow_centralizer_of_core_equality S (vSubgroup S) N hcore)
  have hSB : (S : Subgroup G) ≤ Subgroup.normalizer (B : Set G) :=
    hSN.trans (normalizer_le_normalizer_baumann QA)
  have hBmap : B = ((Q : Subgroup N) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (Q : Subgroup N)) : Set N)).map N.subtype := by
    rw [baumann_map_injective N.subtype N.subtype_injective]
  have hBSyl := baumann_sylow_of_native_two_three N (S : Subgroup G) B
    hsecN Q hcoreN hgen hBmap hSB
  have hZB : zSubgroup S ≤ B := by
    refine le_inf hZQ ?_
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwJ := (mem_omegaOneCenterAmbient_iff _ w).mp hw |>.1
    have hJQ : elementaryAbelianMaxJ QA ≤ QA := sSup_le fun _ hA => hA.1
    exact (mem_omegaOneCenterAmbient_iff _ z).mp hz |>.2.2 w (hQS (hJQ hwJ))
  have hVL : vSubgroup S ≤ L :=
    Subgroup.normalClosure_mono hZB
  have hV2 := (vSubgroup_le_twoCore_and_elementaryAbelian h S).2.isPGroup
  have hV2L : IsPGroup 2 ((vSubgroup S).subgroupOf L) :=
    hV2.comap_of_injective L.subtype L.subtype_injective
  obtain ⟨TB,hTB⟩ := hBSyl
  refine ⟨?_,TB,hTB⟩
  change vSubgroup S ≤ B
  rw [← Subgroup.map_subgroupOf_eq_of_le hVL,← hTB]
  exact Subgroup.map_mono (hV2L.le_sylow_of_normal TB)
end Stellmacher.SectionTwo

