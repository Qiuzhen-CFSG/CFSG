module
public import Stellmacher.SectionTen.TenOneSmallCommonConclusions
public import Theory.GroupTheory.CenterSmallIndex

/-!
# The elementary common-core subgroup in the small branch

In the actual small-module, SL2(2) branch of Section Ten, the intersection
W₀ of all middle-neighbor cores inside the generated middle neighborhood
is an elementary abelian subgroup of order eight, normalized by the middle
stabilizer. The subgroup is the literal W₀ from the statement of (10.1).

Middle conjugation permutes the neighboring cores and normalizes the
neighborhood, hence normalizes W₀. The existing neighborhood order and
common-core index give order eight. The middle center is central in W₀
and has index two, so W₀ is abelian. Its squaring homomorphism has image
inside the middle center and order at most two. This image is normalized
by the middle stabilizer, whose action on its center has no invariant
line. The squaring image is therefore trivial.

This supplies the initial common-core subgroup for W*=C_Qmiddle(W₀) in
the nonsolvable-centralizer argument of Stellmacher (10.1)(a3), printed
pp.60–61/PDF pp.50–51, `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_common_core_elementary
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle
    GAt ctx.Γ middle ≤ Subgroup.normalizer (W0 : Set G) ∧
      IsElementaryAbelian 2 W0 ∧ Nat.card W0 = 8 := by
  classical
  let Γ := ctx.Γ
  let M := GAt Γ middle
  let U := GeneratedNeighborhoodV Γ middle
  let Z := ZAt Γ middle
  let K := NeighborhoodQIntersection Γ (Neighborhood Γ middle)
  let W0 := K ⊓ U
  have hW0U : W0 ≤ U := inf_le_right
  have hMU : M ≤ Subgroup.normalizer (U : Set G) :=
    nine_seven_stabilizer_normalizes_neighborhood Γ middle
  have hMW0 : M ≤ Subgroup.normalizer (W0 : Set G) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro actor hactor element helement
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hMU hactor) element).mp helement.2⟩
    change actor * element * actor⁻¹ ∈
      (sInf {Q : Subgroup G | ∃ neighbor, neighbor ∈ Neighborhood Γ middle ∧ Q = QAt Γ neighbor})
    rw [Subgroup.mem_sInf]
    rintro Q ⟨neighbor,hneighbor,rfl⟩
    have hadj := adjacent_act Γ actor ((mem_neighborhood_iff_adjacent Γ).mp hneighbor)
    have hfix : Γ.act actor middle = middle :=
      (Set.ext_iff.mp (Γ.stabilizer_def middle) actor).mp hactor
    rw [hfix] at hadj
    have hKle : K ≤ QAt Γ (Γ.act actor neighbor) :=
      sInf_le ⟨Γ.act actor neighbor, (mem_neighborhood_iff_adjacent Γ).mpr hadj,rfl⟩
    have hback : element ∈ QAt Γ (Γ.act actor neighbor) := hKle helement.1
    change element ∈ q Γ (Γ.act actor neighbor) at hback
    rw [q_act] at hback
    obtain ⟨preimage,hpreimage,heq⟩ := hback
    have hvalue : actor * element * actor⁻¹ = preimage := by
      rw [← heq]
      simp [mul_assoc]
    exact hvalue ▸ hpreimage
  have hUcard : Nat.card U = 32 := ten_one_small_neighborhood_card ctx middle hpath hsmall
  have hW0card : Nat.card W0 = 8 := by
    have hindex := ten_one_small_neighborhood_core_index ctx middle hpath hsmall hmodel
    change Nat.card U = 4 * Nat.card W0 at hindex
    omega
  have hZU : Z ≤ U := by
    obtain ⟨_,hfirst,_,_⟩ := sectionTenOpeningGeometry ctx middle hpath
    exact (nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm hfirst)).trans
      (le_sSup ⟨_, (mem_neighborhood_iff_adjacent Γ).mpr hfirst,rfl⟩)
  have hZK : Z ≤ K := by
    apply le_sInf
    rintro Q ⟨neighbor,hneighbor,rfl⟩
    exact (nine_seven_neighbor_center_le_module Γ
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hneighbor))).trans
        (neighbor_join_le_core_of_length_gt_one Γ ctx.criticalPath
          (by rw [ctx.critical_length]; decide) neighbor)
  have hZW0 : Z ≤ W0 := le_inf hZK hZU
  have hZcard : Nat.card Z = 4 := (sectionTenOpeningData ctx middle hpath).center_card
  have hZcentral : Z ≤ Subgroup.centralizer (U : Set G) := by
    change ZAt ctx.Γ middle ≤ Subgroup.centralizer (GeneratedNeighborhoodV ctx.Γ middle : Set G)
    rw [← ten_one_small_intersection ctx middle hpath hsmall]
    exact ten_one_common_intersection_centralizes ctx middle hpath
  have hZcenter : Z.subgroupOf W0 ≤ Subgroup.center W0 := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hZcentral hz) w (hW0U w.property)
  have hZindex : (Z.subgroupOf W0).index = 2 := by
    have hcount := (Z.subgroupOf W0).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZW0).toEquiv,
      hW0card,hZcard] at hcount
    omega
  have hcomm : IsMulCommutative W0 := by
    apply (commutator_eq_bot_iff W0).mp
    by_contra hne
    have hfour := (Subgroup.center_eq_and_index_four_of_central_small_index
      (Z.subgroupOf W0) hZcenter (by omega) hne).2
    omega
  let _ := hcomm
  let _ : CommGroup W0 := IsMulCommutative.instCommGroup
  let square : W0 →* G := W0.subtype.comp (powMonoidHom 2)
  have hZker : Z.subgroupOf W0 ≤ square.ker := by
    let _ : IsElementaryAbelian 2 Z := by
      rw [show Z = omegaOneCenter (QAt Γ middle) from
        (sectionTenOpeningData ctx middle hpath).center_omega]
      exact omegaOneCenterAmbient_elementaryAbelian _
    intro z hz
    exact elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=Z) z hz
  have hsquaresZ : square.range ≤ Z := by
    rintro _ ⟨x,rfl⟩
    change (x:G)^2 ∈ Z
    have hh := (Z.subgroupOf W0).mul_mem_iff_of_index_two hZindex (a:=x) (b:=x)
    simpa only [pow_two] using
      (show (x:G) * (x:G) ∈ Z from hh.mpr Iff.rfl)
  have hsquaresM : M ≤ Subgroup.normalizer (square.range : Set G) := by
    apply Subgroup.le_normalizer_iff.mpr
    rintro actor hactor _ ⟨x,rfl⟩
    have hx := (Subgroup.mem_normalizer_iff.mp (hMW0 hactor) (x:G)).mp x.property
    refine ⟨⟨actor * (x:G) * actor⁻¹,hx⟩,?_⟩
    change (actor * (x:G) * actor⁻¹)^2 = actor * (x:G)^2 * actor⁻¹
    simp only [pow_two]
    group
  have hkerCard : 4 ≤ Nat.card square.ker := by
    have hle := Subgroup.card_le_of_le hZker
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZW0).toEquiv,hZcard] at hle
    exact hle
  have hsquareCard : Nat.card square.range ≤ 2 := by
    have hcount := square.ker.card_mul_index
    rw [Subgroup.index_ker,hW0card] at hcount
    nlinarith
  have hsquareNe := ten_one_no_invariant_middle_line ctx middle hpath square.range
    hsquaresZ hsquaresM
  have hsquareBot : square.range = ⊥ := by
    apply Subgroup.card_eq_one.mp
    have hpos := Nat.card_pos (α:=square.range)
    omega
  refine ⟨hMW0,?_,hW0card⟩
  refine ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_⟩
  intro x
  apply Subtype.ext
  have hh : square x ∈ square.range := ⟨x,rfl⟩
  rw [hsquareBot] at hh
  exact hh

end Stellmacher.SectionTen
