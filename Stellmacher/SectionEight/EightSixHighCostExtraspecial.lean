module
public import Stellmacher.SectionEight.EightSixHighCostResidualCard
public import Stellmacher.SectionEight.EightSixHighCostNextCore
public import Stellmacher.SectionEight.EightSixHighCostNextCenter
public import Theory.ElementaryAbelian.Extraspecial

/-!
# The extraspecial next core in the high-cost branch

In the selected high-cost local configuration of Stellmacher (8.6), the
actual next two-core is extraspecial of order 512. The original graph,
selector, core, intersection, and elementary-intersection hypotheses are
retained; no center equality or extraspecial model is assumed.

The selected fixed core is the next central line and Qnext=Vnext. The
residual decomposition, together with the selected orbit containing that
line, then gives Qnext=[Qnext,O²(E)], whose order is already known to be512.
The full-center transfer identifies its native center with the actual
order-two line. The proved elementary Vnext/Znext quotient transports through
Qnext=Vnext and the exact center equality. The central quotient therefore
has order256 and is nontrivial, completing the extraspecial predicate.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.6), immediately after
assertion (18), printed p.45, refs/files/stellmacher-n-group.pdf. The center
transfer fills the step implicit in the source's invocation of (7.3)(b),
without changing that lemma's one-sided containment.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped IsMulCommutative
universe u

public theorem eight_six_high_cost_next_core_extraspecial
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (E A0 : Subgroup G) (actor : G)
    (geom : SectionNine.NineThreeGeometricData ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor)
    (hcore : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      QAt ctx.Γ ctx.criticalPath.a)
    (hedge : E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (ha : actor ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
    (hout : actor ∉ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D : Subgroup G) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup G))
    (hmin : ∀ other : G, other ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      other ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        eightSixCommutatorCost ctx.Γ ctx.criticalPath actor ≤
          eightSixCommutatorCost ctx.Γ ctx.criticalPath other)
    (hQ : Q = twoCoreIn L)
    (hhigh : ∀ mover : G, mover ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      mover ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        8 ≤ eightSixCommutatorCost ctx.Γ ctx.criticalPath mover)
    (helementary : IsElementaryAbelianSubgroup 2 D) :
    IsExtraspecial 2 (QAt ctx.Γ ctx.criticalPath.firstStep) ∧
      Nat.card (QAt ctx.Γ ctx.criticalPath.firstStep) = 512 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let R := QAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let K := twoResidualIn E
  let Y := ⁅R,K⁆
  let U := conjugateClosure (ZAt Γ cp.a) E
  have hselected := eight_six_selected_fixed_core_containment ctx hcenter hquot hlength
    hcard previous D L Q hprev hD hL hQ data E A0 actor geom hcore hedge ha hout hlarge hmin
  have hc : CenterAmbient R = Z := eight_six_high_cost_next_core_center ctx hcenter hquot
    hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL hhigh hselected.1
  have hRV : R = V := eight_six_high_cost_next_core_eq_v ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL hhigh hselected.1 helementary
  have hfixed : R ⊓ Subgroup.centralizer (K : Set G) = Z :=
    eight_six_selected_fixed_core_eq_next_center ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL hhigh hselected.1
  have hpacket := eight_six_selected_residual_decomposition ctx hcenter hquot hlength
    hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hspan : V = Y ⊔ (V ⊓ Subgroup.centralizer (K : Set G)) := hpacket.2.2
  have hUY : U ≤ Y := eight_six_selected_orbit_le_residual_commutator ctx hcenter hquot
    hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hseedU : ZAt Γ cp.a ≤ U := by
    intro z hz
    exact Subgroup.subset_closure ⟨(1:E),⟨z,hz⟩,by simp⟩
  have hZY : Z ≤ Y :=
    (eight_six_first_step_fixed_line_local ctx hcenter hcard).2.trans (hseedU.trans hUY)
  have hRY : R = Y := by
    have hs : R = Y ⊔ (R ⊓ Subgroup.centralizer (K : Set G)) := by
      simpa only [hRV] using hspan
    rw [hfixed,sup_eq_left.mpr hZY] at hs
    exact hs
  have hRcard : Nat.card R = 512 := by
    rw [hRY]
    exact (eight_six_high_cost_residual_card ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL
      ha hout hlarge hmin hQ hhigh).2
  have hZnative : Subgroup.center R = Z.subgroupOf R := by
    rw [← hc]
    exact (Subgroup.comap_map_eq_self_of_injective R.subtype_injective _).symm
  have hcenterCard : Nat.card (Subgroup.center R) = 2 := by
    rw [← Subgroup.card_map_of_injective R.subtype_injective]
    change Nat.card (CenterAmbient R) = 2
    rw [hc]
    exact (eight_six_first_step_fixed_line_local ctx hcenter hcard).1
  obtain ⟨hNV,hWV,_⟩ := eight_six_next_quotient_module_data_local ctx hcenter hlength
    hcard data.first_commutator
  change (Z.subgroupOf V).Normal at hNV
  change IsElementaryAbelian 2 (V ⧸ Z.subgroupOf V) at hWV
  have hRquot : ∃ hNR : (Z.subgroupOf R).Normal,
      let _ := hNR
      IsElementaryAbelian 2 (R ⧸ Z.subgroupOf R) := by
    rw [hRV]
    exact ⟨hNV,hWV⟩
  obtain ⟨hNR,hWR⟩ := hRquot
  let _ := hNR
  have hquotient : IsElementaryAbelian 2 (R ⧸ Subgroup.center R) := by
    let e := QuotientGroup.quotientMulEquivOfEq hZnative
    let _ := hWR
    exact {
      toIsMulCommutative := ⟨⟨fun a b => e.injective (by simp only [map_mul]; exact mul_comm _ _)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun w =>
        e.injective (by
          rw [map_pow,map_one]
          exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p 2 (R ⧸ Z.subgroupOf R)) _)) }
  have hWcard : Nat.card (R ⧸ Subgroup.center R) = 256 := by
    have hh := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center R)
    rw [hRcard,hcenterCard] at hh
    omega
  have hnontrivial : Nontrivial (R ⧸ Subgroup.center R) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hWcard]; decide)
  exact ⟨⟨hcenterCard,hquotient,hnontrivial⟩,hRcard⟩

end Stellmacher.SectionEight
