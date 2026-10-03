module
public import Stellmacher.SectionEight.EightTwoBackwardLocalSetup
public import Stellmacher.SectionFiveToSeven.VertexLocalModule
public import Stellmacher.SectionTwo.NormalSupplementV
public import Mathlib.GroupTheory.Complement

/-!
# Reducing the actual Hall-module orbit in Stellmacher (8.2)

For the smaller normal supplement L = Ea Qfirst with its exact supplied
Sylow image Qfirst, the ambient native Section Two module contains Za.
For every supplied edge Sylow W in the next stabilizer and every complement
U to W, the U-conjugate closure of Za is exactly Vfirst. These are the
lower-bound ingredients for the actual native-module orbit identification;
the native module's upper bound by Vfirst remains a separate prerequisite.

The lower bound transports the supplied Sylow through the subgroup-of
equivalence and applies the normal-supplement module comparison inside Ga.
The graph's local transitivity describes every neighbor center as a
conjugate of Za. Factoring a conjugator as an element of U followed by W,
and using S-invariance of Za, removes the W factor. Normalization of Vfirst
by the next stabilizer gives the opposite inclusion for this vertex orbit.
Neither noncentrality, a critical-length bound, nor oddness of U is needed
for these reductions. No upper bound for the native module is asserted.

Source: Stellmacher (8.2), first containment case, Journal of Algebra 190
(1997), printed pp.37–38, refs/latex/stellmacher-n-group.tex. This separates
the source's vertex Hall orbit from the additional native-module comparison
required by the literal Section Two (2.5) interface.

The local companion uses the ambient-retaining Section Eight context.
The legacy public signature is preserved by its exact graph-preserving
`toLocalContext` adapter; supplied Sylow maps and action instances are retained.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

set_option maxHeartbeats 600000 in
public theorem eight_two_backward_vertex_le_native_module_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hnormal : NormalIn
      (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
      (GAt ctx.Γ ctx.criticalPath.a))
    (T : Sylow 2 ↥(EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep))
    (hT : (T : Subgroup ↥(EAt ctx.Γ ctx.criticalPath.a ⊔
      QAt ctx.Γ ctx.criticalPath.firstStep)).map
        (EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep).subtype =
          QAt ctx.Γ ctx.criticalPath.firstStep) :
    ZAt ctx.Γ ctx.criticalPath.a ≤ (SectionTwo.vSubgroup T).map
      (EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep).subtype := by
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let Pb := stabilizer Γ cp.firstStep
  let B := q Γ cp.firstStep
  let L := e Γ cp.a ⊔ B
  let N := L.subgroupOf P
  obtain ⟨hLN, hgen, _⟩ := eight_two_local_setup_of_core_intersection_normal_local ctx hnormal
  have hLP : L ≤ P := hLN.1
  let _ : N.Normal := hLN.2
  obtain ⟨hSP, R, hR⟩ := (SevenSix.edge_sylow_data h Γ cp).1
  have hRS : (R : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hSP]
    exact hR
  let equiv : N ≃* L := Subgroup.subgroupOfEquivOfLe hLP
  let Q : Sylow 2 N := T.mapSurjective (f := equiv.symm.toMonoidHom) equiv.symm.surjective
  have hQmap : ((Q : Subgroup N).map N.subtype).map P.subtype = B := by
    change (((T : Subgroup L).map equiv.symm.toMonoidHom).map N.subtype).map P.subtype = B
    rw [Subgroup.map_map, Subgroup.map_map]
    exact hT
  have hBS : B ≤ S := (SevenSix.local_cores_le_edge_sylow h Γ cp).2
  have hBP : B ≤ P := hBS.trans hSP
  have hQN : (Q : Subgroup N).map N.subtype = B.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hBP]
    exact hQmap
  have hQS : (Q : Subgroup N).map N.subtype ≤ (R : Subgroup P) := by
    rw [hQN, hRS]
    exact Subgroup.subgroupOf_mono P hBS
  have hNgen : N ⊔ (R : Subgroup P) = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_sup, hR, Subgroup.map_subgroupOf_eq_of_le hLP,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hgen
  have hSB : S ≤ Subgroup.normalizer (B : Set H) :=
    (SevenSix.edge_sylow_data h Γ cp).2.1.trans
      (SevenSix.stabilizer_le_normalizer_q Γ cp.firstStep)
  have hSN : (R : Subgroup P) ≤
      Subgroup.normalizer ((Q : Subgroup N).map N.subtype : Set P) := by
    rw [hQN, hRS]
    exact (Subgroup.le_normalizer_comap P.subtype).trans' (Subgroup.comap_mono hSB)
  have hZQ : SectionTwo.zSubgroup R ≤ (Q : Subgroup N).map N.subtype := by
    have hOm : omegaOneCenter S ≤ z Γ cp.firstStep := by
      obtain ⟨_, Rb, hRb⟩ := (SevenSix.edge_sylow_data h Γ cp).2
      rw [z, Γ.zAt_def]
      exact le_sSup ⟨Rb, congrArg omegaOneCenter hRb.symm⟩
    have ha : cp.a ∈ neighborhood Γ cp.firstStep :=
      (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)
    have hzB : z Γ cp.firstStep ≤ B :=
      ((lemma_seven_three h Γ).center_core cp.firstStep cp.a ha).trans
        ((SevenSix.omegaOneCenter_le_centerAmbient _).trans (Subgroup.map_subtype_le _))
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    rw [hQmap]
    change (omegaOneCenterAmbient (R : Subgroup P)).map P.subtype ≤ _
    rw [← omegaOneCenterAmbient_map_injective P.subtype P.subtype_injective, hR]
    exact hOm.trans hzB
  have hlower := SectionTwo.vSubgroup_le_map_of_normal_supplement N R Q hNgen hQS hZQ hSN
  have hVtransport : SectionTwo.vSubgroup Q =
      (SectionTwo.vSubgroup T).map equiv.symm.toMonoidHom := by
    change Subgroup.normalClosure (omegaOneCenterAmbient (Q : Subgroup N) : Set N) =
      (Subgroup.normalClosure (omegaOneCenterAmbient (T : Subgroup L) : Set L)).map _
    rw [Subgroup.map_normalClosure _ _ equiv.symm.surjective]
    congr 1
    rw [← Subgroup.coe_map]
    congr 1
    exact omegaOneCenterAmbient_map_injective equiv.symm.toMonoidHom equiv.symm.injective _
  have hm := Subgroup.map_mono (f := P.subtype) hlower
  rw [vertexZ_eq_local_vSubgroup Γ cp.a R, hVtransport,
    Subgroup.map_map, Subgroup.map_map] at hm
  exact hm

public theorem eight_two_backward_vertex_hall_orbit_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (W : Sylow 2 (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hW : (W : Subgroup (GAt ctx.Γ ctx.criticalPath.firstStep)).map
      (GAt ctx.Γ ctx.criticalPath.firstStep).subtype = S)
    (U : Subgroup (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hcomp : (W : Subgroup (GAt ctx.Γ ctx.criticalPath.firstStep)).IsComplement' U) :
    conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a)
      (U.map (GAt ctx.Γ ctx.criticalPath.firstStep).subtype) =
        VAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let Pb := GAt Γ cp.firstStep
  let h := ctx.sectionSeven
  have ha : cp.a ∈ neighborhood Γ cp.firstStep :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)
  have hZa : z Γ cp.a ≤ v Γ cp.firstStep := by
    rw [v, Γ.vAt_def]
    exact le_sSup ⟨cp.a, ha, rfl⟩
  have hSN : S ≤ Subgroup.normalizer (z Γ cp.a : Set H) :=
    (SevenSix.edge_sylow_data h Γ cp).1.1.trans (stabilizer_le_normalizer_z Γ cp.a)
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro element ⟨actor, generator, rfl⟩
    have hactor : (actor : H) ∈ Pb :=
      Subgroup.map_subtype_le U actor.property
    exact (Subgroup.mem_normalizer_iff.mp
      (stabilizer_le_normalizer_v Γ cp.firstStep hactor) generator).mp
        (hZa generator.property)
  · change v Γ cp.firstStep ≤ _
    rw [v, Γ.vAt_def]
    apply sSup_le
    rintro Z ⟨neighbor, hn, rfl⟩
    obtain ⟨actor, hactor⟩ :=
      (lemma_seven_one h Γ).local_transitivity cp.firstStep ha hn
    change z Γ neighbor ≤ _
    rw [← hactor, z_act]
    rintro element ⟨generator, hgenerator, rfl⟩
    obtain ⟨⟨oddActor, sylowActor⟩, hfactor, _⟩ := hcomp.symm.existsUnique actor⁻¹
    have hs : ((sylowActor : Pb) : H) ∈ S := by
      exact hW.le (Subgroup.mem_map_of_mem Pb.subtype sylowActor.property)
    have hconj : ((sylowActor : Pb) : H) * generator *
        ((sylowActor : Pb) : H)⁻¹ ∈ z Γ cp.a :=
      (Subgroup.mem_normalizer_iff.mp (hSN hs) generator).mp hgenerator
    apply Subgroup.subset_closure
    refine ⟨⟨((oddActor : Pb) : H),
      Subgroup.mem_map_of_mem Pb.subtype oddActor.property⟩,
      ⟨_, hconj⟩, ?_⟩
    have hfactorH := congrArg (fun value : Pb => (value : H)) hfactor
    change ((oddActor : Pb) : H) * ((sylowActor : Pb) : H) = (actor : H)⁻¹ at hfactorH
    change (actor : H)⁻¹ * generator * ((actor : H)⁻¹)⁻¹ =
      ((oddActor : Pb) : H) *
        (((sylowActor : Pb) : H) * generator * ((sylowActor : Pb) : H)⁻¹) *
          ((oddActor : Pb) : H)⁻¹
    rw [← hfactorH]
    simp only [mul_inv_rev, mul_assoc]


public theorem eight_two_backward_vertex_le_native_module
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hnormal : NormalIn
      (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
      (GAt ctx.Γ ctx.criticalPath.a))
    (T : Sylow 2 ↥(EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep))
    (hT : (T : Subgroup ↥(EAt ctx.Γ ctx.criticalPath.a ⊔
      QAt ctx.Γ ctx.criticalPath.firstStep)).map
        (EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep).subtype =
          QAt ctx.Γ ctx.criticalPath.firstStep) :
    ZAt ctx.Γ ctx.criticalPath.a ≤ (SectionTwo.vSubgroup T).map
      (EAt ctx.Γ ctx.criticalPath.a ⊔ QAt ctx.Γ ctx.criticalPath.firstStep).subtype := by
  exact eight_two_backward_vertex_le_native_module_local ctx.toLocalContext hnormal T hT

public theorem eight_two_backward_vertex_hall_orbit
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (W : Sylow 2 (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hW : (W : Subgroup (GAt ctx.Γ ctx.criticalPath.firstStep)).map
      (GAt ctx.Γ ctx.criticalPath.firstStep).subtype = S)
    (U : Subgroup (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hcomp : (W : Subgroup (GAt ctx.Γ ctx.criticalPath.firstStep)).IsComplement' U) :
    conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a)
      (U.map (GAt ctx.Γ ctx.criticalPath.firstStep).subtype) =
        VAt ctx.Γ ctx.criticalPath.firstStep := by
  exact eight_two_backward_vertex_hall_orbit_local ctx.toLocalContext W hW U hcomp

end Stellmacher.SectionEight
