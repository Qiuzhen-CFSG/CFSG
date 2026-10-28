module
public import Stellmacher.SectionTen.TenOneLargeResidualQuotientElementary
public import Stellmacher.SectionTen.TenOneLargeGeneratedResidualEscape
public import Stellmacher.SectionTen.TenOneLargeTerminalIrreducible
public import Stellmacher.SectionTen.TenOneLargeTerminalFullSupport
public import Stellmacher.SectionNine.NineNextVModule

/-!
# The terminal residual core has derived subgroup equal to the terminal module

In the actual no-transvection Section Ten context, write U for the terminal
residual two-core and V for its module. The derived subgroup of U is exactly V.
The theorem keeps only the original context, middle vertex, critical-path
offset and no-transvection hypothesis; it makes no choice between the residual
models and assumes no terminal core index.

The elementary U/V quotient first gives U'≤V. Since U is normal in the terminal
stabilizer P, its derived subgroup has invariant image in the literal V/Z
quotient action. Irreducibility and the proved residual-derived escape from
the middle center force that image to be the whole quotient. Thus each vector
in V differs from a derived element by an element of Z. The terminal center
centralizes the residual E and P normalizes U', so [V,E]≤U'. Full residual
support [V,E]=V proves equality. The actual quotient normality and action
instances supplied by the existing producers are retained throughout.

Source: Stellmacher, Journal of Algebra 190 (1997), (10.1)(b1), printed p.60,
and the residual-derived argument following (18), printed pp.64–65.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
open scoped commutatorElement
universe u

public theorem ten_one_large_terminal_residual_derived_eq
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    DerivedAmbient (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')) =
      VAt ctx.Γ ctx.criticalPath.a' := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a'
  let E := EAt Γ cp.a'
  let U := twoCoreIn E
  let V := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let D := ⁅U,U⁆
  rw [show DerivedAmbient U = D from Subgroup.map_subtype_commutator U]
  obtain ⟨hUV,hWUV,_⟩ := ten_one_large_residual_quotient_elementary ctx middle hpath hno
  let _ := hUV
  let _ := hWUV
  have hderived : _root_.commutator U ≤ V.subgroupOf U :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      (inferInstance : IsMulCommutative (U ⧸ V.subgroupOf U))
  have hDV : D ≤ V := by
    rw [show D = (_root_.commutator U).map U.subtype from
      (Subgroup.map_subtype_commutator U).symm]
    rintro point ⟨native,hnative,rfl⟩
    exact hderived hnative
  have hE : E = twoResidualIn P := Γ.twoResidualAt_def _
  have hEP : E ≤ P := hE ▸ twoResidualIn_le P
  have hUP : U ≤ P := (twoCoreIn_le E).trans hEP
  have hPU : P ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUP).mp
      (twoCoreIn_normal_of_normal E P hEP (hE ▸ twoResidualIn_normal P))
  have hPD : P ≤ Subgroup.normalizer (D : Set G) :=
    le_normalizer_commutator_of_le_normalizers' hPU hPU
  have hshort : 1 < cp.length := by rw [ctx.critical_length]; decide
  have hVP : V ≤ P :=
    (neighbor_join_le_core_of_length_gt_one Γ cp hshort cp.a').trans (by
      change Γ.twoCoreAt cp.a' ≤ P
      rw [Γ.twoCoreAt_def]
      exact twoCoreIn_le _)
  obtain ⟨_,_,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hZmiddle : Z ≤ ZAt Γ middle := by
    rw [(sectionTenOpeningData ctx middle hpath).center_direct_product.1]
    exact le_sup_right
  have hZV : Z ≤ V := hZmiddle.trans
    (nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm hterminal))
  obtain ⟨alignment,_,halignment⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  obtain ⟨hN,hW,action,hformula,hkernel⟩ := nine_next_quotient_conjugation_action
    ctx.toAmbientSectionNineContext hshort cp.a' ⟨alignment,halignment⟩
  let _ := hN
  let _ := hW
  let quotient := QuotientGroup.mk' (Z.subgroupOf V)
  let Dbar := (D.subgroupOf V).map quotient
  have hinvariant : ∀ mover : P, ∀ point,
      point ∈ Dbar → action mover point ∈ Dbar := by
    rintro mover point ⟨native,hnative,rfl⟩
    rw [hformula]
    refine Subgroup.mem_map.mpr ⟨_, ?_, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hPD mover.property) native).mp hnative
  have htop : Dbar = ⊤ := by
    rcases ten_one_large_terminal_irreducible ctx middle hpath hno
      action hformula hkernel Dbar hinvariant with hzero | hfull
    · have hDZ : D ≤ Z := by
        intro point hpoint
        let native : V := ⟨point,hDV hpoint⟩
        have hq : quotient native ∈ Dbar := Subgroup.mem_map_of_mem quotient hpoint
        rw [hzero] at hq
        exact (QuotientGroup.eq_one_iff (N := Z.subgroupOf V) native).mp hq
      exact (ten_one_large_terminal_residual_derived_not_le_middle_center
        ctx middle hpath hno (hDZ.trans hZmiddle)).elim
    · exact hfull
  have hdecompose (point : G) (hpoint : point ∈ V) :
      ∃ native : V, (native : G) ∈ D ∧ point / (native : G) ∈ Z := by
    obtain ⟨native,hnative,heq⟩ := htop.ge (Subgroup.mem_top (quotient ⟨point,hpoint⟩))
    refine ⟨native,hnative,?_⟩
    have hdiff : (⟨point,hpoint⟩ : V) / native ∈ Z.subgroupOf V :=
      QuotientGroup.eq_iff_div_mem.mp heq.symm
    exact hdiff
  have hZE : ⁅Z,E⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (Subgroup.le_centralizer_iff.mp (hEP.trans
      (nine_next_center_centralizes_stabilizer
        ctx.toLocalContext.toSectionNineLocalContext cp.a' ⟨alignment,halignment⟩)))
  have hDE : ⁅D,E⁆ ≤ D :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hEP.trans hPD)
  have hVED : ⁅V,E⁆ ≤ D := by
    apply Subgroup.commutator_le.mpr
    intro point hpoint actor hactor
    obtain ⟨native,hnative,hcentral⟩ := hdecompose point hpoint
    have heq : point = (point / (native : G)) * (native : G) :=
      (div_mul_cancel point (native : G)).symm
    have hzero : ⁅point / (native : G),actor⁆ = 1 :=
      hZE.le (Subgroup.commutator_mem_commutator hcentral hactor)
    have hmem : ⁅(native : G),actor⁆ ∈ D :=
      hDE (Subgroup.commutator_mem_commutator hnative hactor)
    rw [heq,commutatorElement_mul_left_eq_conj_mul,hzero,mul_one]
    exact (Subgroup.mem_normalizer_iff.mp (hPD (hVP (hZV hcentral))) _).mp hmem
  exact le_antisymm hDV
    ((ten_one_large_terminal_residual_full ctx middle hpath hno).symm.le.trans hVED)

end Stellmacher.SectionTen
