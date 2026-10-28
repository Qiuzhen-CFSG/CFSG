module
public import Stellmacher.SectionEight.LemmaEightOne

/-!
# The central first-step fixed line in (8.5)

In the noncommuting critical-pair context, suppose the initial center has
order four and the first-step center is central in its stabilizer. Then
the first-step center is the order-two Sylow-fixed line in the initial
center. This supplies the local input for identifying the critical
commutator at both ends in the long-path argument of Stellmacher (8.5),
`refs/files/stellmacher-n-group.pdf`, PDF page 30 / journal p.40.

Use the exact quotient-module witness from (8.1), its action, and the image
of the actual edge Sylow. The nontrivial barred offender join makes this
projected Sylow nontrivial. Orbit parity gives at least two fixed module
elements; faithfulness excludes fixing all four. The quotient-module
fixed-point cardinality theorem transfers this order-two line to the
ambient centralizer intersection, without identifying raw LocalJ with
SectionOne.oneJ or assuming additional one-seven factor data.

For the graph transfer, each vertex center contains the omega-center of
the edge Sylow by its defining join. Conversely the elementary initial
center lies in that Sylow, so its Sylow-fixed subgroup lies in the same
omega-center. Centrality puts the first-step center there too. These
containments identify the two centers' shared line. The ordinary quotient
and long-path hypotheses are retained for the requested assembly API;
this local argument does not need them, (8.3), or (6.4).
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem elementary_centralizer_le_omega
    {G : Type u} [Group G] {E T : Subgroup G}
    (hET : E ≤ T) (hcentral : E ≤ Subgroup.centralizer (T : Set G))
    (hpow : ∀ element ∈ E, element ^ 2 = 1) :
    E ≤ omegaOneCenter T := by
  intro element helement
  let point : T := ⟨element, hET helement⟩
  have hpoint : point ∈ Subgroup.center T := by
    rw [Subgroup.mem_center_iff]
    intro actor
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hcentral helement) actor actor.property
  let centralPoint : Subgroup.center T := ⟨point, hpoint⟩
  have hpower : centralPoint ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact hpow element helement
  have homega : centralPoint ∈ omega₁ (G := Subgroup.center T) (p := 2) := by
    rw [omega₁, omega]
    apply Subgroup.subset_closure
    simpa using hpower
  exact Subgroup.mem_map_of_mem T.subtype
    (Subgroup.mem_map_of_mem (Subgroup.center T).subtype homega)

private theorem omega_sylow_le_z
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (vertex : Γ.Vertex)
    (hS : IsSylowTwoIn S (stabilizer Γ vertex)) :
    omegaOneCenter S ≤ z Γ vertex := by
  obtain ⟨_, sylow, hsylow⟩ := hS
  change omegaOneCenter S ≤ Γ.zAt vertex
  rw [Γ.zAt_def]
  exact le_sSup ⟨sylow, congrArg omegaOneCenter hsylow.symm⟩

/-- The central first-step center is the order-two fixed line in the
four-element initial center, with the hypotheses of the (8.5) assembly. -/
public theorem eight_five_first_step_fixed_line_of_card_four_and_quotient
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (_hquotient : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (_hlong : 2 < ctx.criticalPath.length) :
    Nat.card (ZAt ctx.Γ ctx.criticalPath.firstStep) = 2 ∧
      ZAt ctx.Γ ctx.criticalPath.firstStep ≤ ZAt ctx.Γ ctx.criticalPath.a := by
  let h := ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let Za := z Γ cp.a
  let Zfirst := z Γ cp.firstStep
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hback : cp.a ∈ neighborhood Γ cp.firstStep :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)
  let := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hfirst
  let := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hback
  have hlocal := SevenSix.edge_local_data h Γ cp
  have hSylow : IsSylowTwoIn S P := hlocal.1.1.1.2.1
  have hSylowFirst : IsSylowTwoIn S (stabilizer Γ cp.firstStep) :=
    hlocal.2.1.1.2.1
  have hZaS : Za ≤ S :=
    ((lemma_seven_three h Γ).center_core cp.a cp.firstStep hfirst).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
        ((Subgroup.map_subtype_le _).trans (SevenSix.local_cores_le_edge_sylow h Γ cp).1))
  have hZfirstS : Zfirst ≤ S :=
    ((lemma_seven_three h Γ).center_core cp.firstStep cp.a hback).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
        ((Subgroup.map_subtype_le _).trans (SevenSix.local_cores_le_edge_sylow h Γ cp).2))
  have hZfirstCentral : Zfirst ≤ Subgroup.centralizer (S : Set H) :=
    (hcenter.trans (SevenSix.centerAmbient_le_centralizer _)).trans
      (Subgroup.centralizer_le hSylowFirst.1)
  have hZfirstOmega : Zfirst ≤ omegaOneCenter S :=
    elementary_centralizer_le_omega hZfirstS hZfirstCentral
      (fun element helement => elemPow_eq_one_of_isElementaryAbelian element helement)
  have hOmegaZa : omegaOneCenter S ≤ Za := omega_sylow_le_z Γ cp.a hSylow
  have hOmegaFirst : omegaOneCenter S ≤ Zfirst :=
    omega_sylow_le_z Γ cp.firstStep hSylowFirst
  have hfixedEq : Za ⊓ Subgroup.centralizer (S : Set H) = Zfirst := by
    apply le_antisymm
    · apply le_trans _ hOmegaFirst
      exact elementary_centralizer_le_omega (inf_le_left.trans hZaS) inf_le_right
        (fun element helement => elemPow_eq_one_of_isElementaryAbelian element helement.1)
    · exact le_inf (hZfirstOmega.trans hOmegaZa) hZfirstCentral
  obtain ⟨w, _⟩ := (lemma_eight_one ctx).barred_decomposition
  let := w.groupX
  let := w.finiteX
  let := MulDistribMulAction.compHom Za w.action
  obtain ⟨hSP, sylow, hsylow⟩ := hSylow
  have hnative : (sylow : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hSP]
    exact hsylow
  let imageSylow := sylow.mapSurjective w.surjective
  have himage : (imageSylow : Subgroup w.X) = (S.subgroupOf P).map w.projection := by
    change (sylow : Subgroup P).map w.projection = _
    rw [hnative]
  have hJne := (lemma_eight_one_offender ctx w).2
  have hJle : SectionOne.oneJ (V := Za) ((S.subgroupOf P).map w.projection) ≤
      (imageSylow : Subgroup w.X) := by
    rw [himage]
    exact sSup_le fun _ hactor => hactor.1
  have hnontrivial : (imageSylow : Subgroup w.X) ≠ ⊥ := by
    intro hbot
    exact hJne (bot_unique (hJle.trans_eq hbot))
  let fixed := FixedPoints.subgroup imageSylow Za
  change Nat.card Za = 4 at hcard
  have hparity := imageSylow.isPGroup'.card_modEq_card_fixedPoints Za
  change Nat.card Za % 2 = Nat.card fixed % 2 at hparity
  have hpositive : 0 < Nat.card fixed := Nat.card_pos
  have hproper : fixed ≠ ⊤ := by
    intro htop
    apply hnontrivial
    apply bot_unique
    intro actor hactor
    change actor = 1
    apply w.action_injective
    rw [map_one]
    apply MulEquiv.ext
    intro point
    have hpoint : point ∈ fixed := htop ▸ Subgroup.mem_top point
    exact hpoint (⟨actor, hactor⟩ : imageSylow)
  have hless : Nat.card fixed < 4 := by
    have hle := Subgroup.card_le_card_group fixed
    by_contra hnot
    apply hproper
    apply Subgroup.eq_top_of_card_eq
    omega
  have hfixedCard : Nat.card fixed = 2 := by
    omega
  have htransfer := w.fixedPoints_card S hSP
  change Nat.card (FixedPoints.subgroup ((S.subgroupOf P).map w.projection) Za) = _ at htransfer
  rw [← himage] at htransfer
  have hfirstCard : Nat.card Zfirst = 2 := by
    rw [← hfixedEq, ← htransfer]
    exact hfixedCard
  exact ⟨hfirstCard, hZfirstOmega.trans hOmegaZa⟩

end Stellmacher.SectionEight
