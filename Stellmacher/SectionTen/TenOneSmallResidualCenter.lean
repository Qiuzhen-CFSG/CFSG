module
public import Stellmacher.SectionTen.TenOneSmallResidualQuotientAction
public import Stellmacher.SectionTen.TenOneSmallResidualClassTwo
public import Stellmacher.SectionTen.TenOneSmallModuleCoreCommutator

/-!
# The center of the small residual core

In the order-eight, SL2(2) branch of Section Ten, the center of the first
residual two-core is exactly the first central line. This identifies the
center required for the quaternion central-product recognition in
Stellmacher (10.1)(a), Journal of Algebra 190 (1997), printed p.60.

The center is invariant under the first stabilizer. Its image in the actual
elementary four-quotient R/V is therefore trivial or full. A full image would
make R centralize the abelian subgroup V, contradicting [V,R]=Z of order two.
Thus the center lies in V. The faithful action on the elementary four-quotient
V/Z gives the same dichotomy there; its full-image case would again make V
central. Consequently the center is Z. Both quotient actions retain their
literal conjugation formulas, and no irreducibility is assumed.
-/
namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_residual_center
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    CenterAmbient (twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)) =
      ZAt ctx.Γ ctx.criticalPath.firstStep := by
  let vertex := ctx.criticalPath.firstStep
  let P := GAt ctx.Γ vertex
  let Q := QAt ctx.Γ vertex
  let R := twoCoreIn (EAt ctx.Γ vertex)
  let V := VAt ctx.Γ vertex
  let Z := ZAt ctx.Γ vertex
  let C := CenterAmbient R
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hVR : V ≤ R := ten_one_small_module_le_residual_core ctx middle hpath hsmall hmodel
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := stabilizer_le_normalizer_v ctx.Γ vertex
  have hQP : Q ≤ P := by
    change ctx.Γ.twoCoreAt vertex ≤ _
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hEP : EAt ctx.Γ vertex ≤ P := by
    change ctx.Γ.twoResidualAt vertex ≤ _
    rw [ctx.Γ.twoResidualAt_def]
    exact twoResidualIn_le P
  have hRP : R ≤ P := (twoCoreIn_le _).trans hEP
  have hcomm : ⁅V,R⁆ = Z := ten_one_small_module_core_commutator ctx middle hpath hsmall hmodel
  obtain ⟨hZcard,hVQ,_⟩ := nine_next_center_commutator_and_kernel
    ctx.toAmbientSectionNineContext hb vertex ⟨1,ctx.Γ.act_one _⟩
  change Nat.card Z = 2 at hZcard
  change ⁅V,Q⁆ = Z at hVQ
  have hZV : Z ≤ V := by
    rw [← hVQ]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hQP.trans hPV)
  have hPZ : P ≤ Subgroup.centralizer (Z : Set G) :=
    nine_next_center_centralizes_stabilizer ctx.toLocalContext.toSectionNineLocalContext
      vertex ⟨1,ctx.Γ.act_one _⟩
  have hCR : C ≤ R := Subgroup.map_subtype_le _
  have hCcR : C ≤ Subgroup.centralizer (R : Set G) := centerAmbient_le_centralizer R
  have hZC : Z ≤ C := by
    intro z hz
    refine Subgroup.mem_map.mpr ⟨⟨z,hVR (hZV hz)⟩,?_,rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro r
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hPZ (hRP r.property)) z hz).symm
  have hne : ⁅V,R⁆ ≠ ⊥ := by
    rw [hcomm]
    intro hbot
    have hone := Subgroup.card_eq_one.mpr hbot
    omega
  obtain ⟨hNV,hPR,_,hWcard,action,haction,_,hlarge⟩ :=
    ten_one_small_residual_quotient_action ctx middle hpath hsmall hmodel
  let _ := hNV
  have hPC : P ≤ Subgroup.normalizer (C : Set G) := hPR.trans
    (BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic
      R (Subgroup.center R))
  let W := R ⧸ V.subgroupOf R
  let π : R →* W := QuotientGroup.mk' (V.subgroupOf R)
  let D := (C.subgroupOf R).map π
  have hforward (actor : action.range) (point : W) (hpoint : point ∈ D) :
      actor • point ∈ D := by
    obtain ⟨a,ha⟩ := actor.property
    obtain ⟨x,hx,rfl⟩ := hpoint
    change (actor : MulAut W) (π x) ∈ D
    rw [← ha,haction]
    exact Subgroup.mem_map_of_mem π
      ((Subgroup.mem_normalizer_iff.mp (hPC a.property) x).mp hx)
  let _ : IsInvariant action.range W D := ⟨by
    intro a x
    constructor
    · exact hforward a x
    · intro hx
      have hh := hforward a⁻¹ (a • x) hx
      simpa only [inv_smul_smul] using hh⟩
  have hCV : C ≤ V := by
    rcases four_invariant_eq_bot_or_top action.range hWcard hlarge D with hbot | htop
    · have hle := (Subgroup.map_eq_bot_iff (C.subgroupOf R)).mp hbot
      change C.subgroupOf R ≤ (QuotientGroup.mk' (V.subgroupOf R)).ker at hle
      rw [QuotientGroup.ker_mk'] at hle
      intro c hc
      exact hle (show (⟨c,hCR hc⟩ : R) ∈ C.subgroupOf R from hc)
    · have hjoin : C ⊔ V = R := by
        have hpre := Subgroup.comap_map_eq π (C.subgroupOf R)
        change D.comap π = C.subgroupOf R ⊔ π.ker at hpre
        rw [htop,Subgroup.comap_top,QuotientGroup.ker_mk'] at hpre
        have hm := congrArg (Subgroup.map R.subtype) hpre
        rw [Subgroup.map_sup,Subgroup.map_subgroupOf_eq_of_le hCR,
          Subgroup.map_subgroupOf_eq_of_le hVR,← MonoidHom.range_eq_map,
          Subgroup.range_subtype] at hm
        exact hm.symm
      let _ : IsElementaryAbelian 2 V :=
        ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath
          ctx.commutator_eq).longer_case hb).1
      have hRcV : R ≤ Subgroup.centralizer (V : Set G) := by
        rw [← hjoin]
        exact sup_le (hCcR.trans (Subgroup.centralizer_le hVR))
          (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)
      exact False.elim (hne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (Subgroup.le_centralizer_iff.mp hRcV)))
  obtain ⟨hNZ,_,actionV,hactV,hkernel⟩ := nine_next_quotient_conjugation_action
    ctx.toAmbientSectionNineContext hb vertex ⟨1,ctx.Γ.act_one _⟩
  let _ := hNZ
  let X := V ⧸ Z.subgroupOf V
  let ρ : V →* X := QuotientGroup.mk' (Z.subgroupOf V)
  let F := (C.subgroupOf V).map ρ
  have hXcard : Nat.card X = 4 := by
    have hcount := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf V)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv] at hcount
    change Nat.card V = 8 at hsmall
    rw [hsmall,hZcard] at hcount
    change Nat.card (V ⧸ Z.subgroupOf V) = 4
    omega
  have hQnative : Q.subgroupOf P = pCore 2 P := by
    change (ctx.Γ.twoCoreAt vertex).subgroupOf P = _
    rw [ctx.Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hactorsCard : Nat.card actionV.range = 6 := by
    obtain ⟨projection,hsurj,hker⟩ := hmodel
    rw [← Subgroup.index_ker,hkernel,← hQnative,← hker,Subgroup.index_ker]
    rw [MonoidHom.range_eq_top.mpr hsurj,Nat.card_congr Subgroup.topEquiv.toEquiv]
    exact SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩
  have hforwardV (actor : actionV.range) (point : X) (hpoint : point ∈ F) :
      actor • point ∈ F := by
    obtain ⟨a,ha⟩ := actor.property
    obtain ⟨x,hx,rfl⟩ := hpoint
    change (actor : MulAut X) (ρ x) ∈ F
    rw [← ha,hactV]
    exact Subgroup.mem_map_of_mem ρ
      ((Subgroup.mem_normalizer_iff.mp (hPC a.property) x).mp hx)
  let _ : IsInvariant actionV.range X F := ⟨by
    intro a x
    constructor
    · exact hforwardV a x
    · intro hx
      have hh := hforwardV a⁻¹ (a • x) hx
      simpa only [inv_smul_smul] using hh⟩
  apply le_antisymm _ hZC
  rcases four_invariant_eq_bot_or_top actionV.range hXcard
    (by rw [hactorsCard]; decide) F with hbot | htop
  · have hle := (Subgroup.map_eq_bot_iff (C.subgroupOf V)).mp hbot
    change C.subgroupOf V ≤ (QuotientGroup.mk' (Z.subgroupOf V)).ker at hle
    rw [QuotientGroup.ker_mk'] at hle
    intro c hc
    exact hle (show (⟨c,hCV hc⟩ : V) ∈ C.subgroupOf V from hc)
  · have hjoin : C ⊔ Z = V := by
      have hpre := Subgroup.comap_map_eq ρ (C.subgroupOf V)
      change F.comap ρ = C.subgroupOf V ⊔ ρ.ker at hpre
      rw [htop,Subgroup.comap_top,QuotientGroup.ker_mk'] at hpre
      have hm := congrArg (Subgroup.map V.subtype) hpre
      rw [Subgroup.map_sup,Subgroup.map_subgroupOf_eq_of_le hCV,
        Subgroup.map_subgroupOf_eq_of_le hZV,← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at hm
      exact hm.symm
    have hVC : V ≤ C := by rw [← hjoin]; exact sup_le le_rfl hZC
    exact False.elim (hne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hVC.trans hCcR)))
end Stellmacher.SectionTen

