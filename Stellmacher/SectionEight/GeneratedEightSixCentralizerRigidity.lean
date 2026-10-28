module

public import Stellmacher.SectionEight.GeneratedEightSixRigidityResidual
public import Stellmacher.SectionEight.GeneratedEightSixRigidityLastCenter
public import Stellmacher.SectionEight.GeneratedEightSixSL2ResidualOdd
public import Theory.GroupTheory.CenterFreeCentralSubgroup

/-!
# Sylow-central subgroup rigidity in equation (2)

Equation-one data make `U ⊔ Z_a` normal in the initial stabilizer and central
in its two-core. The SL₂(2) quotient gives an odd residual image, so the
center-free coprime-action collapse puts this subgroup in `Z_a`. The
distance-two, order-four center argument then puts `U` in `Z_first`.

This is the subgroup test preceding the centralizer identity in Stellmacher
(8.6), printed p.42, first paragraph, `refs/files/stellmacher-n-group.pdf`.
It uses neither the intersection Frattini collapse nor elementary `D`.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem eight_six_rigidity_le_initial_center
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hcenter : ZAt graph path.firstStep ≤ CenterAmbient (GAt graph path.firstStep))
    (hquot : QuotientIsModel (GAt graph path.a) (QAt graph path.a) SL2Two)
    (previous : graph.Vertex) (D L Q : Subgroup G)
    (hD : D = QAt graph previous ⊓ QAt graph path.firstStep)
    (hL : L = conjugateClosure (QAt graph previous) (GAt graph path.a))
    (data : EightSixEquationOneData graph path previous D L Q)
    (U : Subgroup G) (hUD : U ≤ D)
    (hUS : ⁅U, S⁆ ≤ ZAt graph path.firstStep) :
    U ≤ ZAt graph path.a := by
  let initial := GAt graph path.a
  let center := ZAt graph path.a
  let core := QAt graph path.a
  let residual := EAt graph path.a
  let subgroup := U ⊔ center
  have hnormal := eight_six_rigidity_sup_normal hyp graph path hcenter
    previous D L Q data U hUD hUS
  have hcentral := eight_six_rigidity_sup_centralizes_initial_core hyp graph path hcenter
    previous D L Q hD data U hUD hUS
  have hcomm := eight_six_rigidity_sup_residual_commutator_le hyp graph path
    previous D L Q hD hL data U hUD
  have hcoreEq : core = twoCoreIn initial := graph.twoCoreAt_def path.a
  have hresidualEq : residual = twoResidualIn initial := graph.twoResidualAt_def path.a
  have hresidualLe : residual ≤ initial := hresidualEq ▸ SevenSix.twoResidualIn_le initial
  let coreNative := core.subgroupOf initial
  let residualNative := residual.subgroupOf initial
  let subgroupNative := subgroup.subgroupOf initial
  let centerNative := center.subgroupOf initial
  let _ : coreNative.Normal := by
    change (core.subgroupOf initial).Normal
    rw [hcoreEq]
    exact SevenSix.twoCoreIn_normal initial
  let _ : residualNative.Normal := by
    change (residual.subgroupOf initial).Normal
    rw [hresidualEq]
    exact SevenSix.twoResidualIn_normal initial
  let _ : subgroupNative.Normal := hnormal.2
  have hcoreTwo : IsPGroup 2 coreNative := by
    have htwo : IsPGroup 2 core := by
      rw [hcoreEq]
      exact (pCore_isPGroup (p := 2) (G := initial)).map initial.subtype
    exact htwo.comap_of_injective initial.subtype initial.subtype_injective
  obtain ⟨hS, sylow, hsylow⟩ := (SevenSix.edge_sylow_data hyp graph path).1
  have hcover : residualNative ⊔ (sylow : Subgroup initial) = ⊤ := by
    apply Subgroup.map_injective initial.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hresidualLe, hsylow,
      hresidualEq, SevenSix.twoResidualIn_sup_sylow ⟨hS, sylow, hsylow⟩,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have htrivial : Subgroup.center initial = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective _ initial.subtype_injective).mp
    exact data.initial_center_trivial
  have hresidualNativeEq : residualNative = twoResidualAmbient (⊤ : Subgroup initial) := by
    apply Subgroup.map_injective initial.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hresidualLe,
      map_twoResidualAmbient_of_subgroup_image (⊤ : Subgroup initial) initial.subtype
        initial (by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype])]
    exact hresidualEq
  obtain ⟨projection, hsurjective, hkernel⟩ := hquot
  change projection.ker = coreNative at hkernel
  have hoddImage : Odd (Nat.card (residualNative.map projection)) := by
    rw [hresidualNativeEq]
    exact eight_six_odd_residual_image_of_sl2 coreNative projection hsurjective hkernel
  have hodd : Odd (Nat.card (residualNative.map (QuotientGroup.mk' coreNative))) := by
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', ← hkernel,
      Subgroup.relIndex_ker]
    exact hoddImage
  have hsubgroupCore : subgroupNative ≤ coreNative := by
    intro element helement
    exact (hcentral helement).1
  have hsubgroupCentral : subgroupNative ≤ Subgroup.centralizer (coreNative : Set initial) := by
    intro element helement
    rw [Subgroup.mem_centralizer_iff]
    intro other hother
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hcentral helement).2 other hother
  have hcommNative : ⁅subgroupNative, residualNative⁆ ≤ centerNative := by
    have hmap : (⁅subgroupNative, residualNative⁆).map initial.subtype ≤ center := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hnormal.1,
        Subgroup.map_subgroupOf_eq_of_le hresidualLe]
      exact hcomm
    intro element helement
    exact hmap (Subgroup.mem_map_of_mem initial.subtype helement)
  have hle := Subgroup.le_of_centerfree_odd_image_central_subgroup sylow
    residualNative coreNative subgroupNative centerNative hcover hcoreTwo hodd
    htrivial hsubgroupCore hsubgroupCentral hcommNative
  intro element helement
  have hmember : element ∈ subgroup := (show U ≤ subgroup from le_sup_left) helement
  exact hle (show (⟨element, hnormal.1 hmember⟩ : initial) ∈ subgroupNative from hmember)

public theorem generated_eight_six_centralizer_rigidity
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex)
    (_hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (D L Q : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (_hQ : Q = twoCoreIn L)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (U : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hU : U ≤ D ⊓ Subgroup.centralizer
      (VAt ctx.Γ ctx.criticalPath.firstStep : Set (P1 ⊔ P2 : Subgroup H)))
    (hUS : ⁅U, S.subgroupOf (P1 ⊔ P2)⁆ ≤ ZAt ctx.Γ ctx.criticalPath.firstStep) :
    U ≤ ZAt ctx.Γ ctx.criticalPath.firstStep := by
  have hUZ := eight_six_rigidity_le_initial_center ctx.sectionSeven ctx.Γ ctx.criticalPath
    hcenter hquot previous D L Q hD hL data U (hU.trans inf_le_left) hUS
  exact eight_six_rigidity_le_first_center_of_le_initial ctx.toLocalContext
    hcenter hlength hcard previous D L Q data U hUZ (hU.trans inf_le_right)

end Stellmacher.SectionEight
