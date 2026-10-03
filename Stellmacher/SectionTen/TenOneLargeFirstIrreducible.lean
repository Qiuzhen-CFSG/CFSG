module
public import Stellmacher.SectionTen.TenOneLargeTerminalIrreducible
public import Theory.GroupAction.SubgroupQuotientIrreducible
/-!
# Irreducibility of the prescribed first-step quotient action

For the original large Section Ten context, every invariant subgroup of the
supplied first-step V/Z quotient action is trivial or the whole quotient.
The normality, elementary quotient, action formula and exact core-kernel
parameters are preserved. The no-transvection hypothesis remains the original
one comparing the first module to the terminal quotient.

An actual element of the middle stabilizer sends the first neighbor to the
terminal neighbor, transporting its stabilizer, module and center together.
Conjugation carries each proper invariant subgroup between the first center
and module to such a subgroup at the terminal vertex. The literal terminal
quotient action and its proved irreducibility force that image to be the
terminal center: the alternative full quotient image would contradict
properness. Injectivity returns the original first center. The existing
quotient correspondence then applies this maximality to the supplied first
action and its conjugation formula, retaining its original quotient dictionary.

Source: Stellmacher, Journal of Algebra 190 (1997), (10.1)(20), printed p.65,
using the conjugate of the terminal irreducibility from (14), printed p.63.
This is the first-action input for the actual centralizer commutator family.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u

public theorem ten_one_large_first_irreducible
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    [hN : ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (VAt ctx.Γ ctx.criticalPath.firstStep)).Normal]
    [_hW : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.firstStep ⧸
      (ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf (VAt ctx.Γ ctx.criticalPath.firstStep))]
    (action : GAt ctx.Γ ctx.criticalPath.firstStep →* MulAut
      (VAt ctx.Γ ctx.criticalPath.firstStep ⧸
        (ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf (VAt ctx.Γ ctx.criticalPath.firstStep)))
    (hformula : ∀ mover : GAt ctx.Γ ctx.criticalPath.firstStep,
      ∀ point : VAt ctx.Γ ctx.criticalPath.firstStep,
      action mover (QuotientGroup.mk'
        ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf (VAt ctx.Γ ctx.criticalPath.firstStep)) point) =
        QuotientGroup.mk'
          ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf (VAt ctx.Γ ctx.criticalPath.firstStep))
          ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp
              (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep mover.property)
                point).mp point.property⟩)
    (hkernel : action.ker = pCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    ∀ D : Subgroup (VAt ctx.Γ ctx.criticalPath.firstStep ⧸
        (ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf (VAt ctx.Γ ctx.criticalPath.firstStep)),
      (∀ mover : GAt ctx.Γ ctx.criticalPath.firstStep, ∀ point,
        point ∈ D → action mover point ∈ D) → D = ⊥ ∨ D = ⊤ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let Pt := GAt Γ cp.a'
  let V := VAt Γ cp.firstStep
  let Vt := VAt Γ cp.a'
  let Z := ZAt Γ cp.firstStep
  let Zt := ZAt Γ cp.a'
  -- Keep the supplied kernel dictionary; invariant preimages use the formula below.
  have _hfirst_kernel : action.ker = pCore 2 P := hkernel
  obtain ⟨_,hfirst,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  obtain ⟨mover,hmove⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity middle
    ((mem_neighborhood_iff_adjacent Γ).mpr hfirst)
    ((mem_neighborhood_iff_adjacent Γ).mpr hterminal)
  let f : MulAut G := MulAut.conj (mover:G)⁻¹
  have hPmap : P.map f.toMonoidHom = Pt := by
    change _ = stabilizer Γ cp.a'
    rw [←hmove,stabilizer_act]
    rfl
  have hVmap : V.map f.toMonoidHom = Vt := by
    change _ = v Γ cp.a'
    rw [←hmove,v_act]
  have hZmap : Z.map f.toMonoidHom = Zt := by
    change _ = z Γ cp.a'
    rw [←hmove,z_act]
  have hZV : Z ≤ V := by
    apply le_trans ?_ (nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm hfirst))
    rw [(sectionTenOpeningData ctx middle hpath).center_direct_product.1]
    exact le_sup_left
  have hshort : 1 < cp.length := by rw [ctx.critical_length]; decide
  obtain ⟨alignment,_,halignment⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  obtain ⟨hNt,hWt,terminalAction,terminalFormula,terminalKernel⟩ :=
    nine_next_quotient_conjugation_action ctx.toAmbientSectionNineContext
      hshort cp.a' ⟨alignment,halignment⟩
  let _ := hNt
  let _ := hWt
  let qt := QuotientGroup.mk' (Zt.subgroupOf Vt)
  have hmax : ∀ K : Subgroup G, Z ≤ K → K < V →
      P ≤ Subgroup.normalizer (K : Set G) → K = Z := by
    intro K hZK hKV hPK
    let Kt := K.map f.toMonoidHom
    have hKtV : Kt ≤ Vt := (Subgroup.map_mono hKV.le).trans_eq hVmap
    have hZKt : Zt ≤ Kt := hZmap ▸ Subgroup.map_mono hZK
    have hPtKt : Pt ≤ Subgroup.normalizer (Kt : Set G) := by
      rw [←hPmap]
      exact (Subgroup.map_mono hPK).trans (Subgroup.le_normalizer_map f.toMonoidHom)
    let image := (Kt.subgroupOf Vt).map qt
    have hinvariant : ∀ actor : Pt, ∀ point,
        point ∈ image → terminalAction actor point ∈ image := by
      rintro actor point ⟨native,hnative,rfl⟩
      rw [terminalFormula]
      refine Subgroup.mem_map.mpr ⟨_,?_,rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hPtKt actor.property) native).mp hnative
    rcases ten_one_large_terminal_irreducible ctx middle hpath hno
      terminalAction terminalFormula terminalKernel image hinvariant with hzero | htop
    · have hKtZ : Kt ≤ Zt := by
        intro point hpoint
        let native : Vt := ⟨point,hKtV hpoint⟩
        have hq : qt native ∈ image := Subgroup.mem_map_of_mem qt hpoint
        rw [hzero] at hq
        exact (QuotientGroup.eq_one_iff (N := Zt.subgroupOf Vt) native).mp hq
      apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
      exact (le_antisymm hKtZ hZKt).trans hZmap.symm
    · have hVtKt : Vt ≤ Kt := by
        intro point hpoint
        obtain ⟨native,hnative,heq⟩ := htop.ge (Subgroup.mem_top (qt ⟨point,hpoint⟩))
        have hdiff : (⟨point,hpoint⟩ : Vt) / native ∈ Zt.subgroupOf Vt :=
          QuotientGroup.eq_iff_div_mem.mp heq.symm
        have hproduct := Kt.mul_mem (hZKt hdiff) hnative
        change point / (native:G) * (native:G) ∈ Kt at hproduct
        simpa only [div_mul_cancel] using hproduct
      have hKVeq : K = V := Subgroup.map_injective (f := f.toMonoidHom) f.injective
        ((le_antisymm hKtV hVtKt).trans hVmap.symm)
      exact (hKV.ne hKVeq).elim
  exact Subgroup.quotient_conjugation_irreducible_of_maximal P V Z hZV
    (stabilizer_le_normalizer_v Γ cp.firstStep) hN hmax action hformula

end Stellmacher.SectionTen
