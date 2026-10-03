module
public import Stellmacher.SectionEight.EightTwoDistanceTwoDefs
public import Stellmacher.SectionEight.EightTwoEdgeQuadraticAction
public import Stellmacher.SectionFiveToSeven.NeighborJoinCore
public import Theory.GroupTheory.CentralElementaryInvolutionOrbit
public import Theory.GroupAction.SubgroupConjugation
public import Theory.GroupAction.Quotient
public import Theory.Frattini.PGroup
public import Theory.GroupAction.FourGroupOrbit
public import Theory.GroupTheory.IndexTwoIntersectionLine

/-!
# The actual distance-two subgroup has nontrivial Frattini subgroup

In the noncentral case of Stellmacher (8.2), suppose the critical distance
is two and back is the supplied backward neighbor forming a critical pair
with the first forward neighbor. For the literal subgroup
`distanceTwoVZero ctx back`, assume the separately established source
structure: normality in the initial stabilizer, centrality in its
neighbor-center join Va, and index four in Va. Then its ambient Frattini
subgroup is nontrivial. No orbit hypothesis is assumed.

The shared neighbor-join theorem puts Va in the initial core. The actual
first edge is Sylow and its opposite core has index two; critical endpoint
noncommutation therefore makes the image of Zback in Va/V0 a line of
order two. The backward edge Sylow fixes its unique nonidentity element.
Neighbor transitivity carries Zback to every neighbor center, so that
element's orbit generates the whole four-element quotient. The orbit
lemma then covers all three nonidentity cosets by conjugates of a chosen
involution from Zback.

If the Frattini subgroup of V0 were trivial, V0 would be elementary abelian
because it is a finite two-subgroup of the backward core. The central
involution-orbit theorem would then make Va elementary abelian as well,
contradicting the actual critical commutator of the two neighbor centers.
All quotient calculations use the same named conjugation and quotient
actions; the graph's inverse-actor convention is retained in the transport.

Source: Stellmacher (8.2), Journal of Algebra 190 (1997), printed p.38,
the elementary-V0 paragraph in refs/latex/stellmacher-n-group.tex and the
journal scan. Normality, centrality, and index four are explicit inputs
proved by the separate distance-two structure theorem.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
open scoped IsMulCommutative
universe u

private theorem neighbor_z_le_v
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (a back : Γ.Vertex)
    (hback : back ∈ neighborhood Γ a) : z Γ back ≤ v Γ a := by
  rw [v, Γ.vAt_def]
  exact le_sSup ⟨back, hback, rfl⟩

/-- The actual central index-four subgroup at distance two has nontrivial Frattini subgroup. -/
public theorem eight_two_distance_two_vzero_frattini_ne_bot_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlen : ctx.criticalPath.length = 2) (back : ctx.Γ.Vertex)
    (hback : back ∈ neighborhood ctx.Γ ctx.criticalPath.a)
    (hcritical : IsCriticalPair ctx.Γ back ctx.criticalPath.firstStep)
    (hnormal : NormalIn (distanceTwoVZero ctx back) (GAt ctx.Γ ctx.criticalPath.a))
    (hcentral : distanceTwoVZero ctx back ≤ CenterAmbient (VAt ctx.Γ ctx.criticalPath.a))
    (hindex : (distanceTwoVZero ctx back).relIndex (VAt ctx.Γ ctx.criticalPath.a) = 4) :
    frattiniAmbient (distanceTwoVZero ctx back) ≠ ⊥ := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  change cp.length = 2 at hlen
  let V := v Γ cp.a
  let P := stabilizer Γ cp.a
  let Z := z Γ back
  let K0 := distanceTwoVZero ctx back
  have hKV : K0 ≤ V := inf_le_left.trans inf_le_left
  have hZV : Z ≤ V := neighbor_z_le_v Γ cp.a back hback
  have hPaV : P ≤ Subgroup.normalizer (V : Set G) := stabilizer_le_normalizer_v Γ cp.a
  have hPaK : P ≤ Subgroup.normalizer (K0 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hnormal.1).mp hnormal.2
  let K := K0.subgroupOf V
  let _ : K.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKV).mpr
    ((Subgroup.le_centralizer_iff.mp (hcentral.trans
      (SevenSix.centerAmbient_le_centralizer V))).trans (Subgroup.centralizer_le_normalizer _))
  let actV := Subgroup.conjMulDistribMulActionOfLeNormalizer P V hPaV
  let _ := actV
  have hKinv : IsInvariant P V K := by
    constructor
    intro a w
    exact Subgroup.mem_normalizer_iff.mp (hPaK a.property) (w : G)
  let actX := quotientMulDistribMulAction K hKinv
  let _ := actX
  let _ : MulAction.QuotientAction P K := quotientAction_of_isInvariant K hKinv
  let π := QuotientGroup.mk' K
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective K
  have hπsmul (a : P) (w : V) : π (a • w) = a • π w :=
    (MulAction.Quotient.smul_mk (H := K) a w).symm
  have hπone (w : V) : π w = 1 ↔ w ∈ K := QuotientGroup.eq_one_iff w
  have hXcard : Nat.card (V ⧸ K) = 4 := hindex
  let L := (Z.subgroupOf V).map π
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hbackrev : cp.a ∈ neighborhood Γ back :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((SevenSix.mem_neighborhood_iff_adjacent Γ).mp hback))
  have hZQ : Z ≤ q Γ back :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core back cp.a hbackrev).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans (Subgroup.map_subtype_le _))
  have hnoncomm := eight_two_critical_pair_commutator_ne_local ctx hcenter back cp.firstStep hcritical
  have hZnot : ¬ Z ≤ q Γ cp.firstStep := by
    intro hh
    apply hnoncomm
    rw [Subgroup.commutator_comm]
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    exact (((lemma_seven_three ctx.sectionSeven Γ).center_core cp.firstStep cp.a
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
        (SevenSix.centerAmbient_le_centralizer _))).trans (Subgroup.centralizer_le hh)
  have hVcore : V ≤ q Γ cp.a :=
    SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp (by omega) cp.a
  let E := P ⊓ stabilizer Γ cp.firstStep
  have hVE : V ≤ E := by
    have hQaP : q Γ cp.a ≤ P := by
      rw [q, Γ.twoCoreAt_def]
      exact Subgroup.map_subtype_le _
    have hQaf := (lemma_seven_three ctx.sectionSeven Γ).sylow_and_core
      cp.a cp.firstStep hfirst (default : Sylow 2 (↥(P ⊓ stabilizer Γ cp.firstStep)))
    exact hVcore.trans (le_inf hQaP hQaf.2.2)
  have hSylowE : IsSylowTwoIn E (stabilizer Γ cp.firstStep) := by
    simpa only [inf_comm] using eight_two_adjacent_intersection_is_sylow_local
      ctx hcenter cp.firstStep cp.a (Γ.adjacent_symm cp.firstStep_adj)
  have hER : (q Γ cp.firstStep).relIndex E = 2 := by
    rw [q, Γ.twoCoreAt_def]
    exact eight_two_core_relIndex_two _ E hSylowE
      (eight_two_dihedral_core_local ctx hcenter cp.firstStep)
  have hVR : (q Γ cp.firstStep).relIndex V = 2 := by
    have hle := Subgroup.relIndex_le_of_le_right hVE (by rw [hER]; decide)
    have hpos : 0 < (q Γ cp.firstStep).relIndex V :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hne : (q Γ cp.firstStep).relIndex V ≠ 1 :=
      fun hh => hZnot (hZV.trans (Subgroup.relIndex_eq_one.mp hh))
    omega
  have hline : K0.relIndex Z = 2 :=
    Subgroup.intersection_relIndex_eq_two_of_not_le V (q Γ back)
      (q Γ cp.firstStep) Z hZV hZQ hZnot hVR
  have hLcard : Nat.card L = 2 := by
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk']
    have hmap := Subgroup.relIndex_map_map_of_injective K (Z.subgroupOf V) V.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hKV,
      Subgroup.map_subgroupOf_eq_of_le hZV] at hmap
    exact hmap ▸ hline
  obtain ⟨x, hx, hxuniq⟩ := (Nat.card_eq_two_iff' (1 : L)).mp hLcard
  obtain ⟨t, ht, htx⟩ := x.property
  have ht2 : t ^ 2 = 1 := by
    let _ : IsElementaryAbelian 2 Z :=
      SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ
        ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
          (Γ.adjacent_symm ((SevenSix.mem_neighborhood_iff_adjacent Γ).mp hback)))
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (t : G) ht
  have htxne : π t ≠ 1 := by
    intro hh
    apply hx
    apply Subtype.ext
    exact htx ▸ hh
  have hvalues (z : V) (hz : z ∈ Z.subgroupOf V) : π z = 1 ∨ π z = π t := by
    let zz : L := ⟨π z, Subgroup.mem_map_of_mem π hz⟩
    by_cases he : zz = 1
    · exact Or.inl (congrArg Subtype.val he)
    · have hh := congrArg Subtype.val (hxuniq zz he)
      exact Or.inr (hh.trans htx.symm)
  obtain ⟨_, T, hT⟩ := eight_two_adjacent_intersection_is_sylow_local ctx hcenter
    cp.a back ((SevenSix.mem_neighborhood_iff_adjacent Γ).mp hback)
  have hfix : ∀ s : T, (s : P) • (π t) = π t := by
    intro s
    have hsedge : ((s : P) : G) ∈ P ⊓ stabilizer Γ back :=
      hT.le (Subgroup.mem_map_of_mem P.subtype s.property)
    have hsZ : (s : P) • t ∈ Z.subgroupOf V :=
      (Subgroup.mem_normalizer_iff.mp
        (stabilizer_le_normalizer_z Γ back hsedge.2) (t : G)).mp ht
    have hne : π ((s : P) • t) ≠ 1 := by
      intro hh
      have hh' := congrArg (fun y : V ⧸ K => (s : P)⁻¹ • y) hh
      rw [hπsmul] at hh'
      apply htxne
      simpa only [inv_smul_smul, smul_one] using hh'
    exact (hπsmul (s : P) t).symm.trans ((hvalues _ hsZ).resolve_left hne)
  have horbitgen : Subgroup.closure (MulAction.orbit P (π t)) = ⊤ := by
    let C := Subgroup.closure (MulAction.orbit P (π t))
    let N := C.comap π
    have hVN : V ≤ N.map V.subtype := by
      change v Γ cp.a ≤ _
      rw [v, Γ.vAt_def]
      refine sSup_le ?_
      rintro U ⟨d, hd, rfl⟩
      obtain ⟨a, ha⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a hback hd
      change z Γ d ≤ _
      rw [← ha, z_act]
      rintro w ⟨z, hz, rfl⟩
      let zz : V := ⟨z, hZV hz⟩
      refine ⟨a⁻¹ • zz, ?_, rfl⟩
      change π (a⁻¹ • zz) ∈ C
      rw [hπsmul]
      rcases hvalues zz hz with hh | hh
      · rw [hh, smul_one]
        exact C.one_mem
      · rw [hh]
        exact Subgroup.subset_closure (MulAction.mem_orbit_iff.mpr ⟨a⁻¹, rfl⟩)
    have hNtop : N = ⊤ := by
      apply Subgroup.map_injective V.subtype_injective
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact le_antisymm (Subgroup.map_subtype_le _) hVN
    apply top_unique
    intro y _
    obtain ⟨w, rfl⟩ := hπ y
    exact (show w ∈ N by rw [hNtop]; trivial)
  have horbit : ∀ y : V ⧸ K, y ≠ 1 → ∃ a : P, a • (π t) = y := by
    intro y hy
    exact MulAction.mem_orbit_iff.mp
      (MulAction.nonidentity_mem_orbit_of_card_four hXcard (π t) htxne
        (by rw [← map_pow, ht2, map_one]) T hfix horbitgen y hy)
  intro hphi
  have hKp : IsPGroup 2 K0 := by
    have hp : IsPGroup 2 (q Γ back) := by
      rw [q, Γ.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2) (G := stabilizer Γ back)).map _
    exact hp.to_le (inf_le_left.trans inf_le_right)
  let _ : Fact (IsPGroup 2 K0) := ⟨hKp⟩
  have hKelem : IsElementaryAbelian 2 K0 :=
    frattini_eq_bot_iff_isElementaryAbelian.mp
      ((Subgroup.map_eq_bot_iff_of_injective _ K0.subtype_injective).mp hphi)
  let _ : IsElementaryAbelian 2 K0 := hKelem
  have hKelem' : IsElementaryAbelian 2 K := IsElementaryAbelian.subgroupOf hKV
  have hKVcent : K ≤ Subgroup.center V := by
    intro k hk
    apply Subgroup.mem_center_iff.mpr
    intro w
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp
      ((SevenSix.centerAmbient_le_centralizer V) (hcentral hk)) _ w.property
  have hVelem : IsElementaryAbelian 2 V :=
    isElementaryAbelian_of_central_involution_orbit K hKVcent hKelem' t ht2 (by
      intro v hv
      obtain ⟨a, ha⟩ := horbit (π v) (fun hh => hv ((hπone v).mp hh))
      have heq : π (a • t) = π v := (hπsmul a t).trans ha
      have hmem : (a • t)⁻¹ * v ∈ K := by
        apply (hπone _).mp
        rw [map_mul, map_inv, heq, inv_mul_cancel]
      exact ⟨MulDistribMulAction.toMulAut P V a, ⟨_, hmem⟩, by simp⟩)
  have hcomm := eight_two_critical_pair_commutator_ne_local ctx hcenter back cp.firstStep hcritical
  apply hcomm
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hwV := neighbor_z_le_v Γ cp.a cp.firstStep
    ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) hw
  let _ : IsElementaryAbelian 2 V := hVelem
  exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := V)).comm
    (⟨w, hwV⟩ : V) ⟨z, hZV hz⟩)

end Stellmacher.SectionEight
