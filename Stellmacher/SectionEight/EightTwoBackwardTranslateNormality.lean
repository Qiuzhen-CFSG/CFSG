module

public import Stellmacher.SectionEight.EightTwoBackwardNativeQuotient
public import Stellmacher.SectionEight.EightTwoBackwardHallModuleOrbit
public import Stellmacher.SectionTwo.OddNormalizerTranslate
public import Stellmacher.SectionTwo.LemmaTwoFive
public import Theory.GroupTheory.Hall.OddSylowComplement

/-!
# Neighbor-module normality from the first-edge core intersection

In the noncentral branch of Stellmacher (8.2), assume critical length greater
than one and normality of the first-edge core intersection in the initial
stabilizer. Then the first-step neighbor module is normal in that stabilizer.
These are the intermediate hypotheses supplied by the backward-containment
reduction, not extra hypotheses on the final noncontainment theorem.

The local setup supplies the normal supplement L = Ea Qfirst and an exact
native Sylow T whose image is Qfirst, with the characteristic obstruction.
The native quotient theorem supplies the remaining (2.5) hypotheses in L.
Choose an odd Hall complement in Gfirst and transport its conjugation action
on Qfirst along the supplied Sylow-image equivalence. The generic translate
identity and the actual native-module Hall-orbit theorem identify the ambient
image of the automorphism-translate join with Vfirst. Thus (2.5) makes Vfirst
normal under L. Since Gfirst already normalizes Vfirst, its edge Sylow does
too, and L S = Ga upgrades normality to Ga. Neither L = Ga nor equality of
the native module with Za is used. The final contradiction is assembled by
the separate backward-neighbor noncontainment theorem.

Source: Stellmacher (8.2), first containment case, Journal of Algebra 190
(1997), printed pp.37–38, refs/latex/stellmacher-n-group.tex, using (2.5).
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_two_neighbor_module_normal_of_core_intersection_normal
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlen : 1 < ctx.criticalPath.length)
    (hnormal : NormalIn
      (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
      (GAt ctx.Γ ctx.criticalPath.a)) :
    NormalIn (VAt ctx.Γ ctx.criticalPath.firstStep)
      (GAt ctx.Γ ctx.criticalPath.a) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let L := EAt Γ cp.a ⊔ QAt Γ cp.firstStep
  let B := QAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Pb := GAt Γ cp.firstStep
  let h := ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated
  obtain ⟨hLN, hgen, T, hT, hchar⟩ :=
    eight_two_local_setup_of_core_intersection_normal ctx hnormal
  obtain ⟨hsec, hunique, projection, hsurj, hker⟩ :=
    eight_two_backward_native_quotient ctx hcenter hlen hnormal T hT
  obtain ⟨hSPb, W, hW⟩ := (SevenSix.edge_sylow_data h Γ cp).2
  obtain ⟨U, hodd, hcomp⟩ := Subgroup.exists_odd_complement_sylow_two
    (SevenSix.edge_local_data h Γ cp).2.2 W
  let actors := U.map Pb.subtype
  have hactorsOdd : Odd (Nat.card actors) := by
    rw [show actors = U.map Pb.subtype from rfl,
      Subgroup.card_map_of_injective Pb.subtype_injective]
    exact hodd
  have hactorsN : actors ≤ Subgroup.normalizer (B : Set H) :=
    (Subgroup.map_subtype_le U).trans (SevenSix.stabilizer_le_normalizer_q Γ cp.firstStep)
  let action := SectionTwo.sylowImageNormalizerAction T L.subtype
    L.subtype_injective B hT actors hactorsN
  have hactionOdd : Odd (Nat.card action.range) :=
    SectionTwo.sylowImageNormalizerAction_range_odd T L.subtype
      L.subtype_injective B hT actors hactorsN hactorsOdd
  have hVT : SectionTwo.vSubgroup T ≤ (T : Subgroup L) :=
    (SectionTwo.vSubgroup_le_twoCore_and_elementaryAbelian hsec T).1.trans
      (fitting_pCore_le_sylow T)
  have horbit : conjugateClosure ((SectionTwo.vSubgroup T).map L.subtype) actors = V :=
    eight_two_backward_hall_module_orbit ctx hcenter hlen hnormal T hT W hW U hodd hcomp
  have htranslate : (⨆ actor : action.range,
      SectionTwo.automorphismTranslateV T (actor : MulAut T)).map L.subtype = V :=
    (SectionTwo.map_sylowImageNormalizerAction_translate_join T L.subtype
      L.subtype_injective B hT actors hactorsN hVT).trans horbit
  obtain ⟨K, hK, hKN, _⟩ := SectionTwo.lemma_two_five hsec T hchar hunique
    projection hsurj hker ⟨MulEquiv.ulift⟩ action.range hactionOdd
  have hKV : K.map L.subtype = V := by rw [hK]; exact htranslate
  have hVL : V ≤ L := hKV ▸ Subgroup.map_subtype_le K
  have hVP : V ≤ GAt Γ cp.a := hVL.trans hLN.1
  have hLV : L ≤ Subgroup.normalizer (V : Set H) := by
    let _ : K.Normal := hKN
    have hm := Subgroup.le_normalizer_map (H := K) L.subtype
    rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, hKV] at hm
  refine ⟨hVP, (Subgroup.normal_subgroupOf_iff_le_normalizer hVP).mpr ?_⟩
  rw [← hgen]
  exact sup_le hLV (hSPb.trans (stabilizer_le_normalizer_v Γ cp.firstStep))

end Stellmacher.SectionEight
